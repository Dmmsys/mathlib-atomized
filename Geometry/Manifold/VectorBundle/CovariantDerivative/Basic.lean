/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Covariant derivatives

This file defines covariant derivatives (aka Koszul connections) on vector bundles over manifolds.

There are versions of the story: a local unbundled one and a global bundled one.
The local version is used by the global version but also (in other files) when
seeing a global object in a local trivialization.

In the whole file `M` is a manifold over any nontrivially normed field `𝕜` and `V` is
a vector bundle over `M` with model fiber `F`.

## Main definitions and constructions

* `IsCovariantDerivativeOn`: A function from sections of a vector bundle `V` over a manifold `M` to
  sections of $Hom(TM, V)$ is a *covariant derivative* on a set `s` in `M` if it is additive and
  satisfies the Leibniz rule when applied to sections that are differentiable at a point of `s`.
* `ContMDiffCovariantDerivativeOn`: A covariant derivative ∇ on some set is called *of class* `C^k`
  iff, whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇_X σ` is a `C^k`
  section. This is a class so typeclass inference can deduce this automatically.
* `IsCovariantDerivativeOn.add_one_form`: Adding a one-form taking values in the endomorphisms of
  the vector bundle to a covariant derivative on a set gives a covariant derivative on that set.
* `IsCovariantDerivativeOn.difference`: The difference of two covariant derivatives on a set,
  as a one-form taking values in the endomorphism bundle.
* `CovariantDerivative`: a globally defined covariant derivative on a vector bundle, as a bundled
  object.
* `ContMDiffCovariantDerivative`: A covariant derivative ∇ is called *of class* `C^k`
  iff, whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇_X σ` is a `C^k`
  section. This is a class so typeclass inference can deduce this automatically.
* `CovariantDerivative.addOneForm`: Adding a one-form taking values in the endomorphisms of the
  vector bundle to a covariant derivative gives a covariant derivative.
* `CovariantDerivative.difference`: The difference of two covariant derivatives, as a one-form
  taking values in the endomorphism bundle.

## Implementation notes

On paper there are several equivalent ways to define covariant derivatives on a vector bundle
`V → M`. The most common one starts with a function `∇` taking as input a global smooth vector field
`X` and a global smooth section `σ` and giving as output a global smooth section `∇_X σ`, before
proving the result that `(∇_X σ) x` at a point `x` only depends on the value of the vector field at
that point and the 1-jet of the section at that point.

Here we ask for a map sending a global section `σ` of `V` to a global section `∇ σ` of `Hom(TM, V)`.
So the fact that `(∇_X σ) x` depends only on `X x` is baked into the definition.
Note also that we don’t put any differentiability restriction on `σ` and `X`, the type of
the covariant derivative map is simply `(Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))`.
But the conditions on this map involve differentiability, see the definition of
`IsCovariantDerivativeOn`.

This file proves that `(∇_X σ) x` depends only on the germ of `σ` at `x`, but not the stronger
statement that it depends only the 1-jet of `σ` at `x`. This will be proved in a later file.
-/

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public noncomputable section

/-! ## Local unbundled theory -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M -> Type*} [TopologicalSpace (TotalSpace F V)]
  [forall x, AddCommGroup (V x)] [forall x, Module 𝕜 (V x)]
  [forall x : M, TopologicalSpace (V x)]
  [forall x, IsTopologicalAddGroup (V x)] [forall x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/--
Definition of `IsCovariantDerivativeOn` / `IsCovariantDerivativeOn` 的定义

English:
structure IsCovariantDerivativeOn
  axioms and operations (2):
    - add({σ σ' : Π x : M, V x} {x} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hx : x in s := by trivial)) : cov (σ + σ') x = cov σ x + cov σ' x
    - leibniz({σ : Π x : M, V x} {g : M -> 𝕜} {x} (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x in s := by trivial)) : cov (g • σ) x = g x • cov σ x + (d% g x).smulRight (σ x)

中文:
结构 是余variantDerivativeOn
  公理与运算 (2 个):
    - add({σ σ' : Π x : M, V x} {x} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hx : x in s := by trivial)) : cov (σ + σ') x = cov σ x + cov σ' x
    - leibniz({σ : Π x : M, V x} {g : M -> 𝕜} {x} (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x in s := by trivial)) : cov (g • σ) x = g x • cov σ x + (d% g x).smulRight (σ x)

Depends on / 依赖: Set.univ
-/
structure IsCovariantDerivativeOn
    (cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x))
    (s : Set M := Set.univ) : Prop where
  add {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hx : x in s := by trivial) :
    cov (σ + σ') x = cov σ x + cov σ' x
  leibniz {σ : Π x : M, V x} {g : M -> 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x in s := by trivial) :
    cov (g • σ) x = g x • cov σ x + (d% g x).smulRight (σ x)

/--
Definition of `ContMDiffCovariantDerivativeOn` / `ContMDiffCovariantDerivativeOn` 的定义

English:
class ContMDiffCovariantDerivativeOn
  parameters: [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k : Nat∞ω)
  axioms and operations (1):
    - contMDiff : forall {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) -> letI cov (x : M) : TotalSpace (E ->L[𝕜] F) fun x => TangentSpace I x ->L[𝕜] V x  [default: ⟨x, cov σ x⟩ ContMDiffOn I (I.prod 𝓘(𝕜, E ->L[𝕜] F)) k cov u]

中文:
类 余ntMDiffCovariantDerivativeOn
  参数: [是流形 I 1 M] [向量丛 𝕜 F V] (k : 自然数∞ω)
  公理与运算 (1 个):
    - contMDiff : 对任意 {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) -> letI cov (x : M) : 全空间 (E ->L[𝕜] F) fun x => TangentSpace I x ->L[𝕜] V x  [默认: ⟨x, cov σ x⟩ ContMDiffOn I (I.prod 𝓘(𝕜, E ->L[𝕜] F)) k cov u]
-/
class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k : Nat∞ω)
    (cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x))
    (u : Set M) where
  contMDiff : forall {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) ->
    letI cov (x : M) : TotalSpace (E ->L[𝕜] F) fun x => TangentSpace I x ->L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffOn I (I.prod 𝓘(𝕜, E ->L[𝕜] F)) k cov u
    -- TODO elaborators are not working here. We want to use `T% (cov σ)` and CMDiff[u] k f

variable {F}

namespace IsCovariantDerivativeOn

/-! ### Changing set

In this section, we change `s` in `IsCovariantDerivativeOn F cov s`, proving the condition is
monotone and local.
-/

section changing_set

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  proof: hcov.add hσ hσ' (hst hx)
  leibniz hσ hcov' hx := hcov.leibniz hσ hcov' (hst hx)

中文:
引理 mono
  证明: hcov.add hσ hσ' (hst hx)
  leibniz hσ hcov' hx := hcov.leibniz hσ hcov' (hst hx)

Depends on / 依赖: hcov.add
-/
lemma mono
    {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} {s t : Set M}
    (hcov : IsCovariantDerivativeOn F cov t) (hst : s subseteq t) : IsCovariantDerivativeOn F cov s where
  add hσ hσ' hx := hcov.add hσ hσ' (hst hx)
  leibniz hσ hcov' hx := hcov.leibniz hσ hcov' (hst hx)

/--
lemma `iUnion` / 引理 `iUnion`

English:
lemma iUnion
  statement: {ι : Type*} {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
  proof: by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).add hσ hσ'
  leibniz hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).leibniz hσ hf'

中文:
引理 iUnion
  结论: {ι : 类型} {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
  证明: by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).add hσ hσ'
  leibniz hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).leibniz hσ hf'

Depends on / 依赖: leibniz
-/
lemma iUnion {ι : Type*} {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    {s : ι -> Set M} (hcov : forall i, IsCovariantDerivativeOn F cov (s i)) :
    IsCovariantDerivativeOn F cov (⋃ i, s i) where
  add hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).add hσ hσ'
  leibniz hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).leibniz hσ hf'

end changing_set

-- TODO: prove that `cov σ x` depends on `σ` only via the 1-jet of `σ` at `x`.
-- This will be easy using the projection formula about Ehresmann connections,
-- which will be added in the planned file `CovariantDerivative/Ehresmann.lean`.
-- In the mean-time we use the following weaker results (which are convenient to apply anyway).

/--
lemma `congr_of_eqOn` / 引理 `congr_of_eqOn`

English:
lemma congr_of_eqOn
  proof: by
  classical
  have hxs' : x in s := mem_of_mem_nhds hxs
  let ψ (x' : M) : 𝕜 := if x' in s then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxs']
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have H (x' : M) : ((ψ : M -> 𝕜) • σ) x' = ((ψ : M -> 𝕜) • σ') x' := by
    dsimp [ψ]
    split_ifs with hx's
    · simpa using hσσ' _ hx's
    · simp
  have hψ' : HasMFDerivAt I 𝓘(𝕜) ψ x 0 := by
    have : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun (_x : M) => (1 : 𝕜)) x 0 := hasMFDerivAt_const ..
    refine this.congr_of_eventuallyEq ?_
    apply Filter.eventuallyEq_of_mem hxs
    intro t ht
    simp [ψ, ht]
  have := hcov.leibniz hσ hψ'.mdifferentiableAt
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M -> 𝕜) • σ) x := by
      simp [hcov.leibniz hσ hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]
    _ = cov ((ψ : M -> 𝕜) • σ') x := by rw [funext H]
    _ = cov σ' x := by
      simp [hcov.leibniz hσ' hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]

中文:
引理 congr_of_eqOn
  证明: by
  classical
  have hxs' : x in s := mem_of_mem_nhds hxs
  let ψ (x' : M) : 𝕜 := if x' in s then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxs']
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have H (x' : M) : ((ψ : M -> 𝕜) • σ) x' = ((ψ : M -> 𝕜) • σ') x' := by
    dsimp [ψ]
    split_ifs with hx's
    · simpa using hσσ' _ hx's
    · simp
  have hψ' : HasMFDerivAt I 𝓘(𝕜) ψ x 0 := by
    have : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun (_x : M) => (1 : 𝕜)) x 0 := hasMFDerivAt_const ..
    refine this.congr_of_eventuallyEq ?_
    apply Filter.eventuallyEq_of_mem hxs
    intro t ht
    simp [ψ, ht]
  have := hcov.leibniz hσ hψ'.mdifferentiableAt
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M -> 𝕜) • σ) x := by
      simp [hcov.leibniz hσ hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]
    _ = cov ((ψ : M -> 𝕜) • σ') x := by rw [funext H]
    _ = cov σ' x := by
      simp [hcov.leibniz hσ' hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]

Depends on / 依赖: classical, mem_of_mem_nhds
-/
lemma congr_of_eqOn
    {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hxs : s in 𝓝 x) (hσσ' : forall x in s, σ x = σ' x) :
    cov σ x = cov σ' x := by
  classical
  have hxs' : x in s := mem_of_mem_nhds hxs
  let ψ (x' : M) : 𝕜 := if x' in s then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxs']
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have H (x' : M) : ((ψ : M -> 𝕜) • σ) x' = ((ψ : M -> 𝕜) • σ') x' := by
    dsimp [ψ]
    split_ifs with hx's
    · simpa using hσσ' _ hx's
    · simp
  have hψ' : HasMFDerivAt I 𝓘(𝕜) ψ x 0 := by
    have : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun (_x : M) => (1 : 𝕜)) x 0 := hasMFDerivAt_const ..
    refine this.congr_of_eventuallyEq ?_
    apply Filter.eventuallyEq_of_mem hxs
    intro t ht
    simp [ψ, ht]
  have := hcov.leibniz hσ hψ'.mdifferentiableAt
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M -> 𝕜) • σ) x := by
      simp [hcov.leibniz hσ hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]
    _ = cov ((ψ : M -> 𝕜) • σ') x := by rw [funext H]
    _ = cov σ' x := by
      simp [hcov.leibniz hσ' hψ'.mdifferentiableAt, hψx, mvfderiv, hψ'.mfderiv]

open Filter Set in
/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  proof: by
  rw [eventually_iff_exists_mem] at hσσ'
  choose s' hs' b using hσσ'
  exact (hcov.mono inter_subset_left).congr_of_eqOn hσ hσ' (inter_mem hxs hs') fun x hx => b x hx.2

中文:
引理 congr_of_eventuallyEq
  证明: by
  rw [eventually_iff_exists_mem] at hσσ'
  choose s' hs' b using hσσ'
  exact (hcov.mono inter_subset_left).congr_of_eqOn hσ hσ' (inter_mem hxs hs') fun x hx => b x hx.2

Depends on / 依赖: congr_of_eqOn, eventually_iff_exists_mem, hcov.mono, inter_mem, inter_subset_left
-/
lemma congr_of_eventuallyEq
    {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hxs : s in 𝓝 x) (hσσ' : forallᶠ x in 𝓝 x, σ x = σ' x) :
    cov σ x = cov σ' x := by
  rw [eventually_iff_exists_mem] at hσσ'
  choose s' hs' b using hσσ'
  exact (hcov.mono inter_subset_left).congr_of_eqOn hσ hσ' (inter_mem hxs hs') fun x hx => b x hx.2

/-! ### Computational properties -/

section computational_properties

variable {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)} {s : Set M}

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: [VectorBundle 𝕜 F V] (hcov : IsCovariantDerivativeOn F cov s)
  proof: by
  simpa using (hcov.add (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : cov (0 + 0) x = _)

中文:
引理 zero
  结论: [向量丛 𝕜 F V] (hcov : 是余variantDerivativeOn F cov s)
  证明: by
  simpa using (hcov.add (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : cov (0 + 0) x = _)

Depends on / 依赖: hcov.add, mdifferentiableAt_zeroSection
-/
lemma zero [VectorBundle 𝕜 F V] (hcov : IsCovariantDerivativeOn F cov s)
    {x} (hx : x in s := by trivial) :
    cov 0 x = 0 := by
  simpa using (hcov.add (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : cov (0 + 0) x = _)

/--
theorem `smul_const` / 定理 `smul_const`

English:
theorem smul_const
  statement: (hcov : IsCovariantDerivativeOn F cov s)
  proof: by
  simpa [mvfderiv] using! hcov.leibniz (g := fun _ => a) hσ mdifferentiableAt_const

中文:
定理 smul_const
  结论: (hcov : 是余variantDerivativeOn F cov s)
  证明: by
  simpa [mvfderiv] using! hcov.leibniz (g := fun _ => a) hσ mdifferentiableAt_const

Depends on / 依赖: hcov.leibniz, leibniz, mdifferentiableAt_const, mvfderiv
-/
theorem smul_const (hcov : IsCovariantDerivativeOn F cov s)
    {σ : Π x : M, V x} {x} (a : 𝕜)
    (hσ : MDiffAt (T% σ) x) (hx : x in s := by trivial) :
    cov (a • σ) x = a • cov σ x := by
  simpa [mvfderiv] using! hcov.leibniz (g := fun _ => a) hσ mdifferentiableAt_const

end computational_properties

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `IsCovariantDerivativeOn.add_one_form`.
* subtracting two covariant derivatives on some set gives a one-form taking values in
  the endomorphisms of the vector bundle. See `IsCovariantDerivativeOn.difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in the endomorphisms of the bundle, but we don’t package it that way yet.
-/
section operations

variable {s : Set M} {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}

/-- An affine combination of covariant derivatives is a covariant derivative. -/
@[simps]
/--
lemma `affine_combination` / 引理 `affine_combination`

English:
lemma affine_combination
  statement: (hcov : IsCovariantDerivativeOn F cov s)
  proof: by
    simp [hcov.add hσ hσ', hcov'.add hσ hσ']
    module
  leibniz hσ hφ hx := by
    simp [hcov.leibniz hσ hφ, hcov'.leibniz hσ hφ]
    module

中文:
引理 affine_combination
  结论: (hcov : 是余variantDerivativeOn F cov s)
  证明: by
    simp [hcov.add hσ hσ', hcov'.add hσ hσ']
    module
  leibniz hσ hφ hx := by
    simp [hcov.leibniz hσ hφ, hcov'.leibniz hσ hφ]
    module

Depends on / 依赖: hcov.add, hcov.leibniz, leibniz, module
-/
lemma affine_combination (hcov : IsCovariantDerivativeOn F cov s)
    {cov' : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    (hcov' : IsCovariantDerivativeOn F cov' s) (g : M -> 𝕜) :
    IsCovariantDerivativeOn F (fun σ => (g • (cov σ)) + (1 - g) • (cov' σ)) s where
  add hσ hσ' hx := by
    simp [hcov.add hσ hσ', hcov'.add hσ hσ']
    module
  leibniz hσ hφ hx := by
    simp [hcov.leibniz hσ hφ, hcov'.leibniz hσ hφ]
    module

/--
lemma `_root_.ContMDiffCovariantDerivativeOn.affine_combination` / 引理 `_root_.ContMDiffCovariantDerivativeOn.affine_combination`

English:
lemma _root_.ContMDiffCovariantDerivativeOn.affine_combination
  statement: [IsManifold I 1 M]
  proof: by
    apply ContMDiffOn.add_section
· exact hf.smul_section Hcov.contMDiff hσ
· exact (contMDiffOn_const.sub hf).smul_section Hcov'.contMDiff hσ

中文:
引理 _root_.余ntMDiffCovariantDerivativeOn.affine_combination
  结论: [是流形 I 1 M]
  证明: by
    apply ContMDiffOn.add_section
· exact hf.smul_section Hcov.contMDiff hσ
· exact (contMDiffOn_const.sub hf).smul_section Hcov'.contMDiff hσ
-/
lemma _root_.ContMDiffCovariantDerivativeOn.affine_combination [IsManifold I 1 M]
    [VectorBundle 𝕜 F V]
    {cov cov' : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    {u : Set M} {f : M -> 𝕜} {n : Nat∞ω} (hf : CMDiff[u] n f)
    (Hcov : ContMDiffCovariantDerivativeOn (F := F) n cov u)
    (Hcov' : ContMDiffCovariantDerivativeOn (F := F) n cov' u) :
    ContMDiffCovariantDerivativeOn F n (fun σ => (f • (cov σ)) + (1 - f) • (cov' σ)) u where
  contMDiff hσ := by
    apply ContMDiffOn.add_section
· exact hf.smul_section Hcov.contMDiff hσ
· exact (contMDiffOn_const.sub hf).smul_section Hcov'.contMDiff hσ

/--
lemma `finite_affine_combination` / 引理 `finite_affine_combination`

English:
lemma finite_affine_combination
  statement: {ι : Type*} {s : Finset ι}
  proof: by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add]; rw [(h i).add hσ hσ' hx]
  leibniz {σ g x} hσ hg hx := by
    calc ∑ i in s, f i x • cov i (g • σ) x
      _ = ∑ i in s, (g x • f i x • cov i σ x + f i x • (d% g x).smulRight (σ x)) := by
          congr! 1 with i hi
          rw [(h i).leibniz hσ hg]
          simp [mvfderiv]
          module
      _ = g x • ∑ i in s, f i x • cov i σ x + (∑ i in s, f i) x • (d% g x).smulRight (σ x) := by
          rw [Finset.sum_add_distrib]; rw [Finset.smul_sum]; rw [Finset.sum_apply]; rw [Finset.sum_smul]
      _ = g x • ∑ i in s, f i x • cov i σ x + (d% g x).smulRight (σ x) := by rw [hf]; simp

中文:
引理 finite_affine_combination
  结论: {ι : 类型} {s : 有限集 ι}
  证明: by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add]; rw [(h i).add hσ hσ' hx]
  leibniz {σ g x} hσ hg hx := by
    calc ∑ i in s, f i x • cov i (g • σ) x
      _ = ∑ i in s, (g x • f i x • cov i σ x + f i x • (d% g x).smulRight (σ x)) := by
          congr! 1 with i hi
          rw [(h i).leibniz hσ hg]
          simp [mvfderiv]
          module
      _ = g x • ∑ i in s, f i x • cov i σ x + (∑ i in s, f i) x • (d% g x).smulRight (σ x) := by
          rw [Finset.sum_add_distrib]; rw [Finset.smul_sum]; rw [Finset.sum_apply]; rw [Finset.sum_smul]
      _ = g x • ∑ i in s, f i x • cov i σ x + (d% g x).smulRight (σ x) := by rw [hf]; simp

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_smul, leibniz, module, mvfderiv, smulRight, smul_add, smul_sum, sum_add_distrib, sum_apply, sum_smul
-/
lemma finite_affine_combination {ι : Type*} {s : Finset ι}
    {u : Set M} {cov : ι -> (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    (h : forall i, IsCovariantDerivativeOn F (cov i) u) {f : ι -> M -> 𝕜} (hf : ∑ i in s, f i = 1) :
    IsCovariantDerivativeOn F (fun σ x => ∑ i in s, (f i x) • (cov i) σ x) u where
  add hσ hσ' hx := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add]; rw [(h i).add hσ hσ' hx]
  leibniz {σ g x} hσ hg hx := by
    calc ∑ i in s, f i x • cov i (g • σ) x
      _ = ∑ i in s, (g x • f i x • cov i σ x + f i x • (d% g x).smulRight (σ x)) := by
          congr! 1 with i hi
          rw [(h i).leibniz hσ hg]
          simp [mvfderiv]
          module
      _ = g x • ∑ i in s, f i x • cov i σ x + (∑ i in s, f i) x • (d% g x).smulRight (σ x) := by
          rw [Finset.sum_add_distrib]; rw [Finset.smul_sum]; rw [Finset.sum_apply]; rw [Finset.sum_smul]
      _ = g x • ∑ i in s, f i x • cov i σ x + (d% g x).smulRight (σ x) := by rw [hf]; simp

/--
lemma `_root_.ContMDiffCovariantDerivativeOn.finite_affine_combination` / 引理 `_root_.ContMDiffCovariantDerivativeOn.finite_affine_combination`

English:
lemma _root_.ContMDiffCovariantDerivativeOn.finite_affine_combination
  statement: [IsManifold I 1 M]
  proof: by
    simpa using ContMDiffOn.sum_section
      (fun i hi => (hf i hi).smul_section <| (hcov i hi).contMDiff hσ)

中文:
引理 _root_.余ntMDiffCovariantDerivativeOn.finite_affine_combination
  结论: [是流形 I 1 M]
  证明: by
    simpa using ContMDiffOn.sum_section
      (fun i hi => (hf i hi).smul_section <| (hcov i hi).contMDiff hσ)

Depends on / 依赖: ContMDiffOn, ContMDiffOn.sum_section, contMDiff, smul_section, sum_section
-/
lemma _root_.ContMDiffCovariantDerivativeOn.finite_affine_combination [IsManifold I 1 M]
    {n : Nat∞ω} [VectorBundle 𝕜 F V] {ι : Type*} {s : Finset ι} {u : Set M}
    {cov : ι -> (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    (hcov : forall i in s, ContMDiffCovariantDerivativeOn F n (cov i) u)
    {f : ι -> M -> 𝕜} (hf : forall i in s, CMDiff[u] n (f i)) :
    ContMDiffCovariantDerivativeOn F n (fun σ x => ∑ i in s, (f i x) • (cov i) σ x) u where
  contMDiff {σ} hσ := by
    simpa using ContMDiffOn.sum_section
      (fun i hi => (hf i hi).smul_section <| (hcov i hi).contMDiff hσ)

/--
lemma `add_one_form` / 引理 `add_one_form`

English:
lemma add_one_form
  statement: (hcov : IsCovariantDerivativeOn F cov s)
  proof: by
    simp [hcov.add hσ hσ']
    abel
  leibniz hσ hg hx := by
    simp [hcov.leibniz hσ hg]
    module

中文:
引理 add_one_form
  结论: (hcov : 是余variantDerivativeOn F cov s)
  证明: by
    simp [hcov.add hσ hσ']
    abel
  leibniz hσ hg hx := by
    simp [hcov.leibniz hσ hg]
    module

Depends on / 依赖: hcov.add, hcov.leibniz, leibniz, module
-/
lemma add_one_form (hcov : IsCovariantDerivativeOn F cov s)
    (A : Π x : M, V x ->L[𝕜] TangentSpace I x ->L[𝕜] V x) :
    IsCovariantDerivativeOn F (fun σ x => cov σ x + A x (σ x)) s where
  add hσ hσ' hx := by
    simp [hcov.add hσ hσ']
    abel
  leibniz hσ hg hx := by
    simp [hcov.leibniz hσ hg]
    module

section difference

/--
Definition of `differenceAux` / `differenceAux` 的定义

English:
definition differenceAux
  body: fun σ => cov σ - cov' σ

中文:
定义 differenceAux
  定义体: fun σ => cov σ - cov' σ
-/
private def differenceAux
    (cov cov' : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)) :
    (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x) :=
  fun σ => cov σ - cov' σ

variable
  {cov' : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
  {s : Set M}
  (hcov : IsCovariantDerivativeOn F cov s)
  (hcov' : IsCovariantDerivativeOn F cov' s)

/--
theorem `differenceAux_tensorial` / 定理 `differenceAux_tensorial`

English:
theorem differenceAux_tensorial
  statement: (hcov : IsCovariantDerivativeOn F cov s)
  proof: by
    simp [differenceAux, hcov.leibniz hσ hf, hcov'.leibniz hσ hf]
    module
  add hσ hσ' := by
    simp [differenceAux, hcov.add hσ hσ', hcov'.add hσ hσ']
    abel

中文:
定理 differenceAux_tensorial
  结论: (hcov : 是余variantDerivativeOn F cov s)
  证明: by
    simp [differenceAux, hcov.leibniz hσ hf, hcov'.leibniz hσ hf]
    module
  add hσ hσ' := by
    simp [differenceAux, hcov.add hσ hσ', hcov'.add hσ hσ']
    abel
-/
private theorem differenceAux_tensorial (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (x : M) (hx : x in s) : TensorialAt I F (differenceAux cov cov' · x) x where
  smul hf hσ := by
    simp [differenceAux, hcov.leibniz hσ hf, hcov'.leibniz hσ hf]
    module
  add hσ hσ' := by
    simp [differenceAux, hcov.add hσ hσ', hcov'.add hσ hσ']
    abel

-- We need more assumptions to use the tensoriality criterion in order to build the difference
-- operation.
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

open scoped Classical in
/--
Definition of `difference` / `difference` 的定义

English:
definition difference
  signature: (x : M)
  body: if hxs : x in s then
    TensorialAt.mkHom _ x (differenceAux_tensorial hcov hcov' _ hxs)
  else
    0

@[simp]

中文:
定义 difference
  签名: (x : M)
  定义体: if hxs : x in s then
    TensorialAt.mkHom _ x (differenceAux_tensorial hcov hcov' _ hxs)
  else
    0

@[simp]
-/
@[no_expose] def difference (x : M) : V x ->L[𝕜] TangentSpace I x ->L[𝕜] V x :=
  if hxs : x in s then
    TensorialAt.mkHom _ x (differenceAux_tensorial hcov hcov' _ hxs)
  else
    0

@[simp]
/--
lemma `difference_apply` / 引理 `difference_apply`

English:
lemma difference_apply
  given: {x : M} (hx : x in s := by trivial) {σ : Π x, V x} (hσ : MDiffAt (T% σ) x)
  proof: by
  simp only [difference, hx, reduceDIte]
  rw [TensorialAt.mkHom_apply _ hσ]
  rfl

中文:
引理 difference_apply
  条件: {x : M} (hx : x in s := by trivial) {σ : Π x, V x} (hσ : MDiffAt (T% σ) x)
  证明: by
  simp only [difference, hx, reduceDIte]
  rw [TensorialAt.mkHom_apply _ hσ]
  rfl

Depends on / 依赖: MDiffAt, TensorialAt, TensorialAt.mkHom_apply, difference, mkHom_apply, reduceDIte
-/
lemma difference_apply {x : M} (hx : x in s := by trivial) {σ : Π x, V x} (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' x (σ x) = cov σ x - cov' σ x := by
  simp only [difference, hx, reduceDIte]
  rw [TensorialAt.mkHom_apply _ hσ]
  rfl

end difference

end operations

end IsCovariantDerivativeOn

/-! ## Bundled global covariant derivatives -/

variable (I F V) in
/--
Bundled global covariant derivative on a vector bundle.
Caution, the argument order is nonstandard: `cov σ x (X x)` corresponds to `∇_X σ x` on paper.
-/
@[ext]
/--
Definition of `CovariantDerivative` / `CovariantDerivative` 的定义

English:
structure CovariantDerivative
  parameters: where
  axioms and operations (2):
    - toFun : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)
    - isCovariantDerivativeOnUniv : IsCovariantDerivativeOn F toFun Set.univ

中文:
结构 余variantDerivative
  参数: where
  公理与运算 (2 个):
    - toFun : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)
    - isCovariantDerivativeOnUniv : 是余variantDerivativeOn F toFun 集合.univ
-/
structure CovariantDerivative where
  /-- The covariant derivative as a function. -/
  toFun : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)
  isCovariantDerivativeOnUniv : IsCovariantDerivativeOn F toFun Set.univ

namespace CovariantDerivative

attribute [coe] toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (CovariantDerivative I F V)
  body: ⟨fun e => e.toFun⟩

中文:
实例 :
  签名: CoeFun (余variantDerivative I F V)
  定义体: ⟨fun e => e.toFun⟩

Depends on / 依赖: e.toFun
-/
instance : CoeFun (CovariantDerivative I F V)
    fun _ => (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x) :=
  ⟨fun e => e.toFun⟩

/--
lemma `isCovariantDerivativeOn` / 引理 `isCovariantDerivativeOn`

English:
lemma isCovariantDerivativeOn
  given: (cov : CovariantDerivative I F V) {s : Set M}
  proof: cov.isCovariantDerivativeOnUniv.mono (fun _ _ => trivial)

@[simp]

中文:
引理 isCovariantDerivativeOn
  条件: (cov : 余variantDerivative I F V) {s : 集合 M}
  证明: cov.isCovariantDerivativeOnUniv.mono (fun _ _ => trivial)

@[simp]

Depends on / 依赖: cov.isCovariantDerivativeOnUniv.mono, isCovariantDerivativeOnUniv
-/
lemma isCovariantDerivativeOn (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F cov s :=
  cov.isCovariantDerivativeOnUniv.mono (fun _ _ => trivial)

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  given: [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
  statement: cov 0 = 0
  proof: by
  ext1 x
  simp [cov.isCovariantDerivativeOnUniv.zero]

中文:
引理 zero
  条件: [向量丛 𝕜 F V] (cov : 余variantDerivative I F V)
  结论: cov 0 = 0
  证明: by
  ext1 x
  simp [cov.isCovariantDerivativeOnUniv.zero]

Depends on / 依赖: Matrix, Matrix.nondegenerate_toLinearMap, _iff, cov.isCovariantDerivativeOnUniv.zero, isCovariantDerivativeOnUniv
-/
lemma zero [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V) : cov 0 = 0 := by
  ext1 x
  simp [cov.isCovariantDerivativeOnUniv.zero]

/--
Definition of `ofIsCovariantDerivativeOnOfOpenCover` / `ofIsCovariantDerivativeOnOfOpenCover` 的定义

English:
definition ofIsCovariantDerivativeOnOfOpenCover
  signature: {ι : Type*} {s : ι -> Set M}
  body: ⟨cov, hs ▸ IsCovariantDerivativeOn.iUnion hcov⟩

@[deprecated (since := "2026-07-26")]
alias of_isCovariantDerivativeOn_of_open_cover := ofIsCovariantDerivativeOnOfOpenCover

@[simp]

中文:
定义 ofIsCovariantDerivativeOnOfOpenCover
  签名: {ι : 类型} {s : ι -> 集合 M}
  定义体: ⟨cov, hs ▸ IsCovariantDerivativeOn.iUnion hcov⟩

@[deprecated (since := "2026-07-26")]
alias of_isCovariantDerivativeOn_of_open_cover := ofIsCovariantDerivativeOnOfOpenCover

@[simp]

Depends on / 依赖: IsCovariantDerivativeOn, IsCovariantDerivativeOn.iUnion, iUnion
-/
def ofIsCovariantDerivativeOnOfOpenCover {ι : Type*} {s : ι -> Set M}
    {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    (hcov : forall i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨cov, hs ▸ IsCovariantDerivativeOn.iUnion hcov⟩

@[deprecated (since := "2026-07-26")]
alias of_isCovariantDerivativeOn_of_open_cover := ofIsCovariantDerivativeOnOfOpenCover

@[simp]
/--
lemma `of_isCovariantDerivativeOn_of_open_cover_coe` / 引理 `of_isCovariantDerivativeOn_of_open_cover_coe`

English:
lemma of_isCovariantDerivativeOn_of_open_cover_coe
  statement: {ι : Type*} {s : ι -> Set M}
  proof: rfl

中文:
引理 of_isCovariantDerivativeOn_of_open_cover_coe
  结论: {ι : 类型} {s : ι -> 集合 M}
  证明: rfl
-/
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι -> Set M}
    {cov : (Π x : M, V x) -> (Π x : M, TangentSpace I x ->L[𝕜] V x)}
    (hcov : forall i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    ofIsCovariantDerivativeOnOfOpenCover hcov hs = cov := rfl

/--
Definition of `ContMDiffCovariantDerivative` / `ContMDiffCovariantDerivative` 的定义

English:
class ContMDiffCovariantDerivative
  parameters: [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  axioms and operations (1):
    - contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

中文:
类 余ntMDiffCovariantDerivative
  参数: [是流形 I 1 M] [向量丛 𝕜 F V]
  公理与运算 (1 个):
    - contMDiff : 余ntMDiffCovariantDerivativeOn F k cov.toFun 集合.univ
-/
class ContMDiffCovariantDerivative [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    (cov : CovariantDerivative I F V) (k : Nat∞ω) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

@[simp]
/--
lemma `contMDiffCovariantDerivativeOn_univ_iff` / 引理 `contMDiffCovariantDerivativeOn_univ_iff`

English:
lemma contMDiffCovariantDerivativeOn_univ_iff
  statement: [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  proof: ⟨fun h => ⟨h⟩, fun h => h.contMDiff⟩

中文:
引理 contMDiffCovariantDerivativeOn_univ_iff
  结论: [是流形 I 1 M] [向量丛 𝕜 F V]
  证明: ⟨fun h => ⟨h⟩, fun h => h.contMDiff⟩

Depends on / 依赖: contMDiff, h.contMDiff
-/
lemma contMDiffCovariantDerivativeOn_univ_iff [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {cov : CovariantDerivative I F V} {k : Nat∞ω} :
    ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k :=
  ⟨fun h => ⟨h⟩, fun h => h.contMDiff⟩

section operations

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `CovariantDerivative.addOneForm`.
* subtracting two covariant derivatives on some set gives a one-form taking values in the
  endomorphisms of the vector bundle. See `CovariantDerivative.difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in the endomorphisms of the bundle, but we don’t package it that way yet.
-/

/-- An affine combination of covariant derivatives as a covariant derivative. -/
@[simps]
/--
Definition of `affineCombination` / `affineCombination` 的定义

English:
definition affineCombination
  signature: (cov cov' : CovariantDerivative I F V) (g : M -> 𝕜)
  body: fun σ => (g • (cov σ)) + (1 - g) • (cov' σ)
  isCovariantDerivativeOnUniv :=
    cov.isCovariantDerivativeOn.affine_combination cov'.isCovariantDerivativeOn _

@[deprecated (since := "2026-07-26")] alias affine_combination := affineCombination

中文:
定义 affineCombination
  签名: (cov cov' : 余variantDerivative I F V) (g : M -> 𝕜)
  定义体: fun σ => (g • (cov σ)) + (1 - g) • (cov' σ)
  isCovariantDerivativeOnUniv :=
    cov.isCovariantDerivativeOn.affine_combination cov'.isCovariantDerivativeOn _

@[deprecated (since := "2026-07-26")] alias affine_combination := affineCombination
-/
def affineCombination (cov cov' : CovariantDerivative I F V) (g : M -> 𝕜) :
    CovariantDerivative I F V where
  toFun := fun σ => (g • (cov σ)) + (1 - g) • (cov' σ)
  isCovariantDerivativeOnUniv :=
    cov.isCovariantDerivativeOn.affine_combination cov'.isCovariantDerivativeOn _

@[deprecated (since := "2026-07-26")] alias affine_combination := affineCombination

/--
Definition of `finiteAffineCombination` / `finiteAffineCombination` 的定义

English:
definition finiteAffineCombination
  signature: {ι : Type*} {s : Finset ι}
  body: ∑ i in s, (f i x) • (cov i) t x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.finite_affine_combination
    (fun i => (cov i).isCovariantDerivativeOn) hf

@[deprecated (since := "2026-07-26")] alias finite_affine_combination := finiteAffineCombination

中文:
定义 finiteAffineCombination
  签名: {ι : 类型} {s : 有限集 ι}
  定义体: ∑ i in s, (f i x) • (cov i) t x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.finite_affine_combination
    (fun i => (cov i).isCovariantDerivativeOn) hf

@[deprecated (since := "2026-07-26")] alias finite_affine_combination := finiteAffineCombination
-/
def finiteAffineCombination {ι : Type*} {s : Finset ι}
    (cov : ι -> CovariantDerivative I F V) {f : ι -> M -> 𝕜} (hf : ∑ i in s, f i = 1) :
    CovariantDerivative I F V where
  toFun t x := ∑ i in s, (f i x) • (cov i) t x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.finite_affine_combination
    (fun i => (cov i).isCovariantDerivativeOn) hf

@[deprecated (since := "2026-07-26")] alias finite_affine_combination := finiteAffineCombination

/--
lemma `ContMDiffCovariantDerivative.affineCombination` / 引理 `ContMDiffCovariantDerivative.affineCombination`

English:
lemma ContMDiffCovariantDerivative.affineCombination
  statement: [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  proof: ContMDiffCovariantDerivativeOn.affine_combination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.affine_combination :=
  ContMDiffCovariantDerivative.affineCombination

中文:
引理 余ntMDiffCovariantDerivative.affineCombination
  结论: [是流形 I 1 M] [向量丛 𝕜 F V]
  证明: ContMDiffCovariantDerivativeOn.affine_combination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.affine_combination :=
  ContMDiffCovariantDerivative.affineCombination

Depends on / 依赖: ContMDiffCovariantDerivativeOn, ContMDiffCovariantDerivativeOn.affine_combination, affine_combination, contMDiff, contMDiffOn, hcov.contMDiff, hf.contMDiffOn
-/
lemma ContMDiffCovariantDerivative.affineCombination [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  (cov cov' : CovariantDerivative I F V)
    {f : M -> 𝕜} {n : Nat∞ω} (hf : CMDiff n f)
    (hcov : ContMDiffCovariantDerivative cov n) (hcov' : ContMDiffCovariantDerivative cov' n) :
    ContMDiffCovariantDerivative (affineCombination cov cov' f) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.affine_combination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.affine_combination :=
  ContMDiffCovariantDerivative.affineCombination

/--
lemma `ContMDiffCovariantDerivative.finiteAffineCombination` / 引理 `ContMDiffCovariantDerivative.finiteAffineCombination`

English:
lemma ContMDiffCovariantDerivative.finiteAffineCombination
  statement: [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  proof: ContMDiffCovariantDerivativeOn.finite_affine_combination
      (fun i hi => (hcov i hi).contMDiff) (fun i hi => (hf' i hi).contMDiffOn)

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.finite_affine_combination :=
  ContMDiffCovariantDerivative.finiteAffineCombination

中文:
引理 余ntMDiffCovariantDerivative.finiteAffineCombination
  结论: [是流形 I 1 M] [向量丛 𝕜 F V]
  证明: ContMDiffCovariantDerivativeOn.finite_affine_combination
      (fun i hi => (hcov i hi).contMDiff) (fun i hi => (hf' i hi).contMDiffOn)

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.finite_affine_combination :=
  ContMDiffCovariantDerivative.finiteAffineCombination

Depends on / 依赖: ContMDiffCovariantDerivativeOn, ContMDiffCovariantDerivativeOn.finite_affine_combination, contMDiff, contMDiffOn, finite_affine_combination
-/
lemma ContMDiffCovariantDerivative.finiteAffineCombination [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {ι : Type*} {s : Finset ι} (cov : ι -> CovariantDerivative I F V) {f : ι -> M -> 𝕜}
    (hf : ∑ i in s, f i = 1) {n : Nat∞ω} (hf' : forall i in s, CMDiff n (f i))
    (hcov : forall i in s, ContMDiffCovariantDerivative (cov i) n) :
    ContMDiffCovariantDerivative (finiteAffineCombination cov hf) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.finite_affine_combination
      (fun i hi => (hcov i hi).contMDiff) (fun i hi => (hf' i hi).contMDiffOn)

@[deprecated (since := "2026-07-26")]
alias ContMDiffCovariantDerivative.finite_affine_combination :=
  ContMDiffCovariantDerivative.finiteAffineCombination

-- TODO: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

/--
Definition of `addOneForm` / `addOneForm` 的定义

English:
definition addOneForm
  signature: (cov : CovariantDerivative I F V)
  body: fun σ x => cov σ x + A x (σ x)
  isCovariantDerivativeOnUniv := cov.isCovariantDerivativeOnUniv.add_one_form A

中文:
定义 addOneForm
  签名: (cov : 余variantDerivative I F V)
  定义体: fun σ x => cov σ x + A x (σ x)
  isCovariantDerivativeOnUniv := cov.isCovariantDerivativeOnUniv.add_one_form A
-/
def addOneForm (cov : CovariantDerivative I F V)
    (A : Π (x : M), V x ->L[𝕜] TangentSpace I x ->L[𝕜] V x) : CovariantDerivative I F V where
  toFun := fun σ x => cov σ x + A x (σ x)
  isCovariantDerivativeOnUniv := cov.isCovariantDerivativeOnUniv.add_one_form A

section difference

-- We need more assumptions to use the tensoriality criterion in order to build the difference
-- operation.
variable [CompleteSpace 𝕜] [IsManifold I 1 M] [FiniteDimensional 𝕜 F]
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

/--
Definition of `difference` / `difference` 的定义

English:
definition difference
  signature: (cov cov' : CovariantDerivative I F V)
  body: cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv

中文:
定义 difference
  签名: (cov cov' : 余variantDerivative I F V)
  定义体: cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv

Depends on / 依赖: cov.isCovariantDerivativeOnUniv.difference, difference, isCovariantDerivativeOnUniv
-/
def difference (cov cov' : CovariantDerivative I F V) :
    Π (x : M), V x ->L[𝕜] TangentSpace I x ->L[𝕜] V x :=
  cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv

end difference
end operations

end CovariantDerivative
