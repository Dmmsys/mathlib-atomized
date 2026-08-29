/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.ContinuousMap.StarOrdered

/-!
# The continuous functional calculus

This file defines a generic API for the *continuous functional calculus* which is suitable in a wide
range of settings.

A continuous functional calculus for an element `a : A` in a topological `R`-algebra is a continuous
extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) to continuous `R`-valued
functions on `spectrum R a`. More precisely, it is a continuous star algebra homomorphism
`C(spectrum R a, R) →⋆ₐ[R] A` that sends `(ContinuousMap.id R).restrict (spectrum R a)` to
`a`. In all cases of interest (e.g., when `spectrum R a` is compact and `R` is `ℝ≥0`, `ℝ`, or `ℂ`),
this is sufficient to uniquely determine the continuous functional calculus which is encoded in the
`ContinuousMap.UniqueHom` class.

Although these properties suffice to uniquely determine the continuous functional calculus, we
choose to bundle more information into the class itself. Namely, we include that the star algebra
homomorphism is a closed embedding, and also that the spectrum of the image of
`f : C(spectrum R a, R)` under this morphism is the range of `f`. In addition, the class specifies
a collection of continuous functional calculi for elements satisfying a given predicate
`p : A → Prop`, and we require that this predicate is preserved by the functional calculus.

Although `cfcHom : p a → C(spectrum R a, R) →*ₐ[R] A` is a necessity for getting the full power
out of the continuous functional calculus, this declaration will generally not be accessed directly
by the user. One reason for this is that `cfcHom` requires a proof of `p a` (indeed, if the
spectrum is empty, there cannot exist a star algebra homomorphism like this). Instead, we provide
the completely unbundled `cfc : (R → R) → A → A` which operates on bare functions and provides junk
values when either `a` does not satisfy the property `p`, or else when the function which is the
argument to `cfc` is not continuous on the spectrum of `a`.

This completely unbundled approach may give up some conveniences, but it allows for tremendous
freedom. In particular, `cfc f a` makes sense for *any* `a : A` and `f : R → R`. This is quite
useful in a variety of settings, but perhaps the most important is the following.
Besides being a star algebra homomorphism sending the identity to `a`, the key property enjoyed
by the continuous functional calculus is the *composition property*, which guarantees that
`cfc (g ∘ f) a = cfc g (cfc f a)` under suitable hypotheses on `a`, `f` and `g`. Note that this
theorem is nearly impossible to state nicely in terms of `cfcHom` (see `cfcHom_comp`). An
additional advantage of the unbundled approach is that expressions like `fun x : R ↦ x⁻¹` are valid
arguments to `cfc`, and a bundled continuous counterpart can only make sense when the spectrum of
`a` does not contain zero and when we have an `⁻¹` operation on the domain.

A reader familiar with C⋆-algebra theory may be somewhat surprised at the level of abstraction here.
For instance, why not require `A` to be an actual C⋆-algebra? Why define separate continuous
functional calculi for `R := ℂ`, `ℝ` or `ℝ≥0` instead of simply using the continuous functional
calculus for normal elements? The reason for both can be explained with a simple example,
`A := Matrix n n ℝ`. In Mathlib, matrices are not equipped with a norm (nor even a metric), and so
requiring `A` to be a C⋆-algebra is far too stringent. Likewise, `A` is not a `ℂ`-algebra, and so
it is impossible to consider the `ℂ`-spectrum of `a : Matrix n n ℝ`.

There is another, more practical reason to define separate continuous functional calculi for
different scalar rings. It gives us the ability to use functions defined on these types, and the
algebra of functions on them. For example, for `R := ℝ` it is quite natural to consider the
functions `(·⁺ : ℝ → ℝ)` and `(·⁻ : ℝ → ℝ)` because the functions `ℝ → ℝ` form a lattice ordered
group. If `a : A` is selfadjoint, and we define `a⁺ := cfc (·⁺ : ℝ → ℝ) a`, and likewise for `a⁻`,
then the properties `a⁺ * a⁻ = 0 = a⁻ * a⁺` and `a = a⁺ - a⁻` are trivial consequences of the
corresponding facts for functions. In contrast, if we had to do this using functions on `ℂ`, the
proofs of these facts would be much more cumbersome.

## Example

The canonical example of the continuous functional calculus is when `A := Matrix n n ℂ`, `R := ℂ`
and `p := IsStarNormal`. In this case, `spectrum ℂ a` consists of the eigenvalues of the normal
matrix `a : Matrix n n ℂ`, and, because this set is discrete, any function is continuous on the
spectrum. The continuous functional calculus allows us to make sense of expressions like `log a`
(`:= cfc log a`), and when `0 ∉ spectrum ℂ a`, we get the nice property `exp (log a) = a`, which
arises from the composition property `cfc exp (cfc log a) = cfc (exp ∘ log) a = cfc id a = a`, since
`exp ∘ log = id` *on the spectrum of `a`*. Of course, there are other ways to make sense of `exp`
and `log` for matrices (power series), and these agree with the continuous functional calculus.
In fact, given `f : C(spectrum ℂ a, ℂ)`, `cfc f a` amounts to diagonalizing `a` (possible since `a`
is normal), and applying `f` to the resulting diagonal entries. That is, if `a = u * d * star u`
with `u` a unitary matrix and `d` diagonal, then `cfc f a = u * d.map f * star u`.

In addition, if `a : Matrix n n ℂ` is positive semidefinite, then the `ℂ`-spectrum of `a` is
contained in (the range of the coercion of) `ℝ≥0`. In this case, we get a continuous functional
calculus with `R := ℝ≥0`. From this we can define `√a := cfc a NNReal.sqrt`, which is also
positive semidefinite (because `cfc` preserves the predicate), and this is truly a square root since
```
√a * √a = cfc NNReal.sqrt a * cfc NNReal.sqrt a =
  cfc (NNReal.sqrt ^ 2) a = cfc id a = a
```
The composition property allows us to show that, in fact, this is the *unique* positive semidefinite
square root of `a` because, if `b` is any positive semidefinite square root, then
```
b = cfc id b = cfc (NNReal.sqrt ∘ (· ^ 2)) b =
  cfc NNReal.sqrt (cfc b (· ^ 2)) = cfc NNReal.sqrt a = √a
```

## Main declarations

+ `ContinuousFunctionalCalculus R A (p : A → Prop)`: a class stating that every `a : A` satisfying
  `p a` has a star algebra homomorphism from the continuous `R`-valued functions on the
  `R`-spectrum of `a` into the algebra `A`. This map is a closed embedding, and satisfies the
  **spectral mapping theorem**.
+ `cfcHom : p a → C(spectrum R a, R) →⋆ₐ[R] A`: the underlying star algebra homomorphism for an
  element satisfying property `p`.
+ `cfc : (R → R) → A → A`: an unbundled version of `cfcHom` which takes the junk value `0` when
  `cfcHom` is not defined.
+ `cfcUnits`: builds a unit from `cfc f a` when `f` is nonzero and continuous on the
  spectrum of `a`.

## Main theorems

+ `cfc_comp : cfc (x ↦ g (f x)) a = cfc g (cfc f a)`
+ `cfc_polynomial`: the continuous functional calculus extends the polynomial functional calculus.

## Implementation details

Instead of defining a class depending on a term `a : A`, we register it for an `outParam` predicate
`p : A → Prop`, and then any element of `A` satisfying this predicate has the associated star
algebra homomorphism with the specified properties. In so doing we avoid a common pitfall:
dependence of the class on a term. This avoids annoying situations where `a b : A` are
propositionally equal, but not definitionally so, and hence Lean would not be able to automatically
identify the continuous functional calculi associated to these elements. In order to guarantee
the necessary properties, we require that the continuous functional calculus preserves this
predicate. That is, `p a → p (cfc f a)` for any function `f` continuous on the spectrum of `a`.

As stated above, the unbundled approach to `cfc` has its advantages. For instance, given an
expression `cfc f a`, the user is free to rewrite either `a` or `f` as desired with no possibility
of the expression ceasing to be defined. However, this unbundling also has some potential downsides.
In particular, by unbundling, proof requirements are deferred until the user calls the lemmas, most
of which have hypotheses both of `p a` and of `ContinuousOn f (spectrum R a)`.

In order to minimize burden to the user, we provide `autoParams` in terms of two tactics. Goals
related to continuity are dispatched by (a small wrapper around) `fun_prop`. As for goals involving
the predicate `p`, it should be noted that these will only ever be of the form `IsStarNormal a`,
`IsSelfAdjoint a` or `0 ≤ a`. For the moment we provide a rudimentary tactic to deal with these
goals, but it can be modified to become more sophisticated as the need arises.
-/

@[expose] public section

open scoped Ring
open Topology ContinuousMap

section Basic

/--
Definition of `ContinuousFunctionalCalculus` / `ContinuousFunctionalCalculus` 的定义

English:
class ContinuousFunctionalCalculus
  parameters: (R A : Type*) (p : outParam (A -> Prop))
  axioms and operations (4):
    - predicate_zero : p 0
    - [compactSpace_spectrum((a : A)) : CompactSpace (spectrum R a)]
    - spectrum_nonempty([Nontrivial A] (a : A) (ha : p a)) : (spectrum R a).Nonempty
    - exists_cfc_of_predicate : forall a, p a -> exists φ : C(spectrum R a, R) ->⋆ₐ[R] A, Continuous φ ∧ Function.Injective φ ∧ φ ((ContinuousMap.id R).restrict <| spectrum R a) = a ∧ (forall f, spectrum R (φ f) = Set.range f) ∧ forall f, p (φ f)

中文:
类 余ntinuousFunctionalCalculus
  参数: (R A : 类型) (p : outParam (A -> 命题))
  公理与运算 (4 个):
    - predicate_zero : p 0
    - [compactSpace_spectrum((a : A)) : 紧空间 (spectrum R a)]
    - spectrum_nonempty([非平凡 A] (a : A) (ha : p a)) : (spectrum R a).非空
    - exists_cfc_of_predicate : 对任意 a, p a -> 存在 φ : C(spectrum R a, R) ->⋆ₐ[R] A, 连续 φ ∧ 函数.单射 φ ∧ φ ((连续映射.id R).restrict <| spectrum R a) = a ∧ (对任意 f, spectrum R (φ f) = 集合.range f) ∧ 对任意 f, p (φ f)
-/
class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A -> Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum R a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum R a).Nonempty
  exists_cfc_of_predicate : forall a, p a -> exists φ : C(spectrum R a, R) ->⋆ₐ[R] A,
    Continuous φ ∧ Function.Injective φ ∧ φ ((ContinuousMap.id R).restrict <| spectrum R a) = a ∧
      (forall f, spectrum R (φ f) = Set.range f) ∧ forall f, p (φ f)

-- this instance should not be activated everywhere but it is useful when developing generic API
-- for the continuous functional calculus
scoped[ContinuousFunctionalCalculus]
attribute [instance] ContinuousFunctionalCalculus.compactSpace_spectrum

/--
Definition of `ContinuousMap.UniqueHom` / `ContinuousMap.UniqueHom` 的定义

English:
class ContinuousMap.UniqueHom
  parameters: (R A : Type*) [CommSemiring R] [StarRing R]
  axioms and operations (1):
    - eq_of_continuous_of_map_id((s : Set R) [CompactSpace s] (φ ψ : C(s, R) ->⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R))) : φ = ψ

中文:
类 连续映射.唯一态射
  参数: (R A : 类型) [交换半环 R] [对合环 R]
  公理与运算 (1 个):
    - eq_of_continuous_of_map_id((s : 集合 R) [紧空间 s] (φ ψ : C(s, R) ->⋆ₐ[R] A) (hφ : 连续 φ) (hψ : 连续 ψ) (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R))) : φ = ψ
-/
class ContinuousMap.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s]
    (φ ψ : C(s, R) ->⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R)) :
    φ = ψ

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

include instCFC in
/--
lemma `ContinuousFunctionalCalculus.isCompact_spectrum` / 引理 `ContinuousFunctionalCalculus.isCompact_spectrum`

English:
lemma ContinuousFunctionalCalculus.isCompact_spectrum
  given: (a : A)
  proof: isCompact_iff_compactSpace.mpr inferInstance

中文:
引理 余ntinuousFunctionalCalculus.isCompact_spectrum
  条件: (a : A)
  证明: isCompact_iff_compactSpace.mpr inferInstance

Depends on / 依赖: isCompact_iff_compactSpace, isCompact_iff_compactSpace.mpr
-/
lemma ContinuousFunctionalCalculus.isCompact_spectrum (a : A) :
    IsCompact (spectrum R a) :=
  isCompact_iff_compactSpace.mpr inferInstance

/--
lemma `StarAlgHom.ext_continuousMap` / 引理 `StarAlgHom.ext_continuousMap`

English:
lemma StarAlgHom.ext_continuousMap
  statement: [UniqueHom R A]
  proof: UniqueHom.eq_of_continuous_of_map_id (spectrum R a) φ ψ hφ hψ h

中文:
引理 StarAlg态射.ext_continuousMap
  结论: [唯一态射 R A]
  证明: UniqueHom.eq_of_continuous_of_map_id (spectrum R a) φ ψ hφ hψ h

Depends on / 依赖: UniqueHom, UniqueHom.eq_of_continuous_of_map_id, eq_of_continuous_of_map_id, spectrum
-/
lemma StarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (spectrum R a)] (φ ψ : C(spectrum R a, R) ->⋆ₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict (spectrum R a) <| .id R) = ψ (.restrict (spectrum R a) <| .id R)) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id (spectrum R a) φ ψ hφ hψ h

section cfcHom

variable {a : A} (ha : p a)

-- Note: since `spectrum R a` is closed, we may always extend `f : C(spectrum R a, R)` to a function
-- of type `C(R, R)` by the Tietze extension theorem (assuming `R` is either `ℝ`, `ℂ` or `ℝ≥0`).

/--
Definition of `cfcHom` / `cfcHom` 的定义

English:
definition cfcHom
  signature: : C(spectrum R a, R) ->⋆ₐ[R] A
  body: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]

中文:
定义 cfcHom
  签名: : C(spectrum R a, R) ->⋆ₐ[R] A
  定义体: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.exists_cfc_of_predicate, exists_cfc_of_predicate
-/
noncomputable def cfcHom : C(spectrum R a, R) ->⋆ₐ[R] A :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]
/--
lemma `cfcHom_continuous` / 引理 `cfcHom_continuous`

English:
lemma cfcHom_continuous
  statement: Continuous (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A)
  proof: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

中文:
引理 cfcHom_continuous
  结论: 连续 (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A)
  证明: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcHom_continuous : Continuous (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

/--
lemma `cfcHom_injective` / 引理 `cfcHom_injective`

English:
lemma cfcHom_injective
  statement: Function.Injective (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A)
  proof: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

中文:
引理 cfcHom_injective
  结论: 函数.单射 (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A)
  证明: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcHom_injective : Function.Injective (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

/--
lemma `cfcHom_id` / 引理 `cfcHom_id`

English:
lemma cfcHom_id
  proof: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

中文:
引理 cfcHom_id
  证明: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcHom_id :
    cfcHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

/--
lemma `cfcHom_map_spectrum` / 引理 `cfcHom_map_spectrum`

English:
lemma cfcHom_map_spectrum
  given: (f : C(spectrum R a, R))
  proof: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f

中文:
引理 cfcHom_map_spectrum
  条件: (f : C(spectrum R a, R))
  证明: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcHom_map_spectrum (f : C(spectrum R a, R)) :
    spectrum R (cfcHom ha f) = Set.range f :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f

/--
lemma `cfcHom_predicate` / 引理 `cfcHom_predicate`

English:
lemma cfcHom_predicate
  given: (f : C(spectrum R a, R))
  proof: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

中文:
引理 cfcHom_predicate
  条件: (f : C(spectrum R a, R))
  证明: (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcHom_predicate (f : C(spectrum R a, R)) :
    p (cfcHom ha f) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

open scoped ContinuousFunctionalCalculus in
/--
lemma `cfcHom_eq_of_continuous_of_map_id` / 引理 `cfcHom_eq_of_continuous_of_map_id`

English:
lemma cfcHom_eq_of_continuous_of_map_id
  statement: [UniqueHom R A]
  proof: (cfcHom ha).ext_continuousMap a φ (cfcHom_continuous ha) hφ₁ by
    rw [cfcHom_id ha]; rw [hφ₂]

中文:
引理 cfcHom_eq_of_continuous_of_map_id
  结论: [唯一态射 R A]
  证明: (cfcHom ha).ext_continuousMap a φ (cfcHom_continuous ha) hφ₁ by
    rw [cfcHom_id ha]; rw [hφ₂]

Depends on / 依赖: cfcHom, cfcHom_continuous, cfcHom_id, ext_continuousMap
-/
lemma cfcHom_eq_of_continuous_of_map_id [UniqueHom R A]
    (φ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ₁ : Continuous φ)
    (hφ₂ : φ (.restrict (spectrum R a) <| .id R) = a) : cfcHom ha = φ :=
(cfcHom ha).ext_continuousMap a φ (cfcHom_continuous ha) hφ₁ by
    rw [cfcHom_id ha]; rw [hφ₂]

/--
theorem `cfcHom_comp` / 定理 `cfcHom_comp`

English:
theorem cfcHom_comp
  statement: [UniqueHom R A] (f : C(spectrum R a, R))
  proof: by
  let φ : C(spectrum R (cfcHom ha f), R) ->⋆ₐ[R] A :=
(cfcHom ha).comp ContinuousMap.compStarAlgHom' R R f'
  suffices cfcHom (cfcHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcHom_eq_of_continuous_of_map_id (cfcHom_predicate ha f) φ ?_ ?_
.comp f'.continuous_precomp · ex

中文:
定理 cfcHom_comp
  结论: [唯一态射 R A] (f : C(spectrum R a, R))
  证明: by
  let φ : C(spectrum R (cfcHom ha f), R) ->⋆ₐ[R] A :=
(cfcHom ha).comp ContinuousMap.compStarAlgHom' R R f'
  suffices cfcHom (cfcHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcHom_eq_of_continuous_of_map_id (cfcHom_predicate ha f) φ ?_ ?_
.comp f'.continuous_precomp · ex

Depends on / 依赖: ContinuousMap, ContinuousMap.compStarAlgHom, DFunLike, DFunLike.congr_fun, StarAlgHom, StarAlgHom.comp_apply, _apply, cfcHom, cfcHom_continuous, cfcHom_eq_of_continuous_of_map_id, cfcHom_predicate, compStarAlgHom, comp_apply, congr_fun, continuous_precomp, spectrum, this.symm
-/
theorem cfcHom_comp [UniqueHom R A] (f : C(spectrum R a, R))
    (f' : C(spectrum R a, spectrum R (cfcHom ha f)))
    (hff' : forall x, f x = f' x) (g : C(spectrum R (cfcHom ha f), R)) :
    cfcHom ha (g.comp f') = cfcHom (cfcHom_predicate ha f) g := by
  let φ : C(spectrum R (cfcHom ha f), R) ->⋆ₐ[R] A :=
(cfcHom ha).comp ContinuousMap.compStarAlgHom' R R f'
  suffices cfcHom (cfcHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcHom_eq_of_continuous_of_map_id (cfcHom_predicate ha f) φ ?_ ?_
.comp f'.continuous_precomp · exact cfcHom_continuous ha
  · simp only [φ, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
    congr
    ext x
    simp [hff']

end cfcHom

section cfcL

/-- `cfcHom` bundled as a continuous linear map. -/
@[simps apply]
/--
Definition of `cfcL` / `cfcL` 的定义

English:
definition cfcL
  signature: {a : A} (ha : p a)
  body: { cfcHom ha with
    toFun := cfcHom ha
    map_smul' := map_smul _ }

中文:
定义 cfcL
  签名: {a : A} (ha : p a)
  定义体: { cfcHom ha with
    toFun := cfcHom ha
    map_smul' := map_smul _ }

Depends on / 依赖: cfcHom, map_smul
-/
noncomputable def cfcL {a : A} (ha : p a) : C(spectrum R a, R) ->L[R] A :=
  { cfcHom ha with
    toFun := cfcHom ha
    map_smul' := map_smul _ }

end cfcL

section CFC

open scoped Classical in
/-- This is the *continuous functional calculus* of an element `a : A` applied to bare functions.
When either `a` does not satisfy the predicate `p` (i.e., `a` is not `IsStarNormal`,
`IsSelfAdjoint`, or `0 ≤ a` when `R` is `ℂ`, `ℝ`, or `ℝ≥0`, respectively), or when `f : R → R` is
not continuous on the spectrum of `a`, then `cfc f a` returns the junk value `0`.

This is the primary declaration intended for widespread use of the continuous functional calculus,
and all the API applies to this declaration. For more information, see the module documentation
for `Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`. -/
noncomputable irreducible_def cfc (f : R -> R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcHom h.1 ⟨_, h.2.domRestrict⟩
    else 0

variable (f g : R -> R) (a : A) (ha : p a := by cfc_tac)
variable (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
variable (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)

set_option backward.privateInPublic true in
/--
lemma `cfc_apply` / 引理 `cfc_apply`

English:
lemma cfc_apply
  statement: cfc f a = cfcHom (a := a) ha ⟨_, hf.domRestrict⟩
  proof: by
  rw [cfc_def]; rw [dif_pos ⟨ha]; rw [hf⟩]

中文:
引理 cfc_apply
  结论: cfc f a = cfcHom (a := a) ha ⟨_, hf.domRestrict⟩
  证明: by
  rw [cfc_def]; rw [dif_pos ⟨ha]; rw [hf⟩]

Depends on / 依赖: cfc_def, dif_pos, domRestrict, hf.domRestrict
-/
lemma cfc_apply : cfc f a = cfcHom (a := a) ha ⟨_, hf.domRestrict⟩ := by
  rw [cfc_def]; rw [dif_pos ⟨ha]; rw [hf⟩]

/--
lemma `cfc_apply_pi` / 引理 `cfc_apply_pi`

English:
lemma cfc_apply_pi
  statement: {ι : Type*} (f : ι -> R -> R) (a : A) (ha : p a := by cfc_tac)
  proof: by
  ext i
  simp only [cfc_apply (f i) a ha (hf i)]

中文:
引理 cfc_apply_pi
  结论: {ι : 类型} (f : ι -> R -> R) (a : A) (ha : p a := by cfc_tac)
  证明: by
  ext i
  simp only [cfc_apply (f i) a ha (hf i)]

Depends on / 依赖: ContinuousOn, cfcHom, cfc_apply, cfc_cont_tac, cfc_tac, domRestrict, spectrum
-/
lemma cfc_apply_pi {ι : Type*} (f : ι -> R -> R) (a : A) (ha : p a := by cfc_tac)
    (hf : forall i, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    (fun i => cfc (f i) a) = (fun i => cfcHom (a := a) ha ⟨_, (hf i).domRestrict⟩) := by
  ext i
  simp only [cfc_apply (f i) a ha (hf i)]

/--
lemma `cfc_apply_of_not_and` / 引理 `cfc_apply_of_not_and`

English:
lemma cfc_apply_of_not_and
  given: {f : R -> R} (a : A) (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a)))
  proof: by
  rw [cfc_def]; rw [dif_neg ha]

中文:
引理 cfc_apply_of_not_and
  条件: {f : R -> R} (a : A) (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a)))
  证明: by
  rw [cfc_def]; rw [dif_neg ha]

Depends on / 依赖: cfc_def, dif_neg
-/
lemma cfc_apply_of_not_and {f : R -> R} (a : A) (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))) :
    cfc f a = 0 := by
  rw [cfc_def]; rw [dif_neg ha]

/--
lemma `cfc_apply_of_not_predicate` / 引理 `cfc_apply_of_not_predicate`

English:
lemma cfc_apply_of_not_predicate
  given: {f : R -> R} (a : A) (ha : ¬ p a)
  proof: by
  rw [cfc_def]; rw [dif_neg (not_and_of_not_left _ ha)]

中文:
引理 cfc_apply_of_not_predicate
  条件: {f : R -> R} (a : A) (ha : ¬ p a)
  证明: by
  rw [cfc_def]; rw [dif_neg (not_and_of_not_left _ ha)]

Depends on / 依赖: cfc_def, dif_neg, not_and_of_not_left
-/
lemma cfc_apply_of_not_predicate {f : R -> R} (a : A) (ha : ¬ p a) :
    cfc f a = 0 := by
  rw [cfc_def]; rw [dif_neg (not_and_of_not_left _ ha)]

/--
lemma `cfc_apply_of_not_continuousOn` / 引理 `cfc_apply_of_not_continuousOn`

English:
lemma cfc_apply_of_not_continuousOn
  given: {f : R -> R} (a : A) (hf : ¬ ContinuousOn f (spectrum R a))
  proof: by
  rw [cfc_def]; rw [dif_neg (not_and_of_not_right _ hf)]

中文:
引理 cfc_apply_of_not_continuousOn
  条件: {f : R -> R} (a : A) (hf : ¬ ContinuousOn f (spectrum R a))
  证明: by
  rw [cfc_def]; rw [dif_neg (not_and_of_not_right _ hf)]

Depends on / 依赖: cfc_def, dif_neg, not_and_of_not_right
-/
lemma cfc_apply_of_not_continuousOn {f : R -> R} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) :
    cfc f a = 0 := by
  rw [cfc_def]; rw [dif_neg (not_and_of_not_right _ hf)]

/--
lemma `cfcHom_eq_cfc_extend` / 引理 `cfcHom_eq_cfc_extend`

English:
lemma cfcHom_eq_cfc_extend
  given: {a : A} (g : R -> R) (ha : p a) (f : C(spectrum R a, R))
  proof: by
  have h : f = (spectrum R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (spectrum R a) :=
continuousOn_iff_continuous_domRestrict.mpr h ▸ map_continuous f
  rw [cfc_apply ..]
  congr!

中文:
引理 cfcHom_eq_cfc_extend
  条件: {a : A} (g : R -> R) (ha : p a) (f : C(spectrum R a, R))
  证明: by
  have h : f = (spectrum R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (spectrum R a) :=
continuousOn_iff_continuous_domRestrict.mpr h ▸ map_continuous f
  rw [cfc_apply ..]
  congr!

Depends on / 依赖: ContinuousOn, Function, Function.extend, Subtype, Subtype.val, cfc_apply, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mpr, domRestrict, extend, map_continuous, spectrum
-/
lemma cfcHom_eq_cfc_extend {a : A} (g : R -> R) (ha : p a) (f : C(spectrum R a, R)) :
    cfcHom ha f = cfc (Function.extend Subtype.val f g) a := by
  have h : f = (spectrum R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (spectrum R a) :=
continuousOn_iff_continuous_domRestrict.mpr h ▸ map_continuous f
  rw [cfc_apply ..]
  congr!

/--
lemma `cfc_eq_cfcL` / 引理 `cfc_eq_cfcL`

English:
lemma cfc_eq_cfcL
  given: {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (spectrum R a))
  proof: by
  rw [cfc_def]; rw [dif_pos ⟨ha]; rw [hf⟩]; rw [cfcL_apply]

中文:
引理 cfc_eq_cfcL
  条件: {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (spectrum R a))
  证明: by
  rw [cfc_def]; rw [dif_pos ⟨ha]; rw [hf⟩]; rw [cfcL_apply]

Depends on / 依赖: cfcL_apply, cfc_def, dif_pos
-/
lemma cfc_eq_cfcL {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    cfc f a = cfcL ha ⟨_, hf.domRestrict⟩ := by
  rw [cfc_def]; rw [dif_pos ⟨ha]; rw [hf⟩]; rw [cfcL_apply]

set_option backward.privateInPublic true in
/--
lemma `cfc_apply_mkD` / 引理 `cfc_apply_mkD`

English:
lemma cfc_apply_mkD
  proof: by
  by_cases hf : ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a, mkD_of_continuousOn hf]
  · rw [cfc_apply_of_not_continuousOn a hf, mkD_of_not_continuousOn hf,
      map_zero]

中文:
引理 cfc_apply_mkD
  证明: by
  by_cases hf : ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a, mkD_of_continuousOn hf]
  · rw [cfc_apply_of_not_continuousOn a hf, mkD_of_not_continuousOn hf,
      map_zero]

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_continuousOn, domRestrict, map_zero, mkD_of_continuousOn, mkD_of_not_continuousOn, spectrum
-/
lemma cfc_apply_mkD :
    cfc f a = cfcHom (a := a) ha (mkD ((spectrum R a).domRestrict f) 0) := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a, mkD_of_continuousOn hf]
  · rw [cfc_apply_of_not_continuousOn a hf, mkD_of_not_continuousOn hf,
      map_zero]

set_option backward.privateInPublic true in
/--
lemma `cfc_eq_cfcL_mkD` / 引理 `cfc_eq_cfcL_mkD`

English:
lemma cfc_eq_cfcL_mkD
  proof: cfc_apply_mkD _ _

中文:
引理 cfc_eq_cfcL_mkD
  证明: cfc_apply_mkD _ _

Depends on / 依赖: domRestrict, spectrum
-/
lemma cfc_eq_cfcL_mkD :
    cfc f a = cfcL (a := a) ha (mkD ((spectrum R a).domRestrict f) 0) :=
  cfc_apply_mkD _ _

/--
lemma `cfc_cases` / 引理 `cfc_cases`

English:
lemma cfc_cases
  statement: (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0)
  proof: by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a h.1 h.2]
    exact haf h.2 h.1
  · simp only [not_and_or] at h
    obtain (h | h) := h
    · rwa [cfc_apply_of_not_predicate _ h]
    · rwa [cfc_apply_of_not_continuousOn _ h]

中文:
引理 cfc_cases
  结论: (P : A -> 命题) (a : A) (f : R -> R) (h₀ : P 0)
  证明: by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a h.1 h.2]
    exact haf h.2 h.1
  · simp only [not_and_or] at h
    obtain (h | h) := h
    · rwa [cfc_apply_of_not_predicate _ h]
    · rwa [cfc_apply_of_not_continuousOn _ h]

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_continuousOn, cfc_apply_of_not_predicate, not_and_or, spectrum
-/
lemma cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0)
    (haf : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.domRestrict⟩)) :
    P (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a h.1 h.2]
    exact haf h.2 h.1
  · simp only [not_and_or] at h
    obtain (h | h) := h
    · rwa [cfc_apply_of_not_predicate _ h]
    · rwa [cfc_apply_of_not_continuousOn _ h]

/--
lemma `cfc_commute_cfc` / 引理 `cfc_commute_cfc`

English:
lemma cfc_commute_cfc
  given: (f g : R -> R) (a : A)
  statement: Commute (cfc f a) (cfc g a)
  proof: by
  refine cfc_cases (fun x => Commute x (cfc g a)) a f (by simp) fun hf ha => ?_
  refine cfc_cases (fun x => Commute _ x) a g (by simp) fun hg _ => ?_
.map _ exact Commute.all _ _

中文:
引理 cfc_commute_cfc
  条件: (f g : R -> R) (a : A)
  结论: Commute (cfc f a) (cfc g a)
  证明: by
  refine cfc_cases (fun x => Commute x (cfc g a)) a f (by simp) fun hf ha => ?_
  refine cfc_cases (fun x => Commute _ x) a g (by simp) fun hg _ => ?_
.map _ exact Commute.all _ _

Depends on / 依赖: Commute, Commute.all, cfc_cases
-/
lemma cfc_commute_cfc (f g : R -> R) (a : A) : Commute (cfc f a) (cfc g a) := by
  refine cfc_cases (fun x => Commute x (cfc g a)) a f (by simp) fun hf ha => ?_
  refine cfc_cases (fun x => Commute _ x) a g (by simp) fun hg _ => ?_
.map _ exact Commute.all _ _

variable (R) in
/--
lemma `cfc_id` / 引理 `cfc_id`

English:
lemma cfc_id
  given: (ha : p a := by cfc_tac)
  statement: cfc (id : R -> R) a = a
  proof: cfc_apply (id : R -> R) a ▸ cfcHom_id (p := p) ha

中文:
引理 cfc_id
  条件: (ha : p a := by cfc_tac)
  结论: cfc (id : R -> R) a = a
  证明: cfc_apply (id : R -> R) a ▸ cfcHom_id (p := p) ha

Depends on / 依赖: cfcHom_id, cfc_apply, cfc_tac
-/
lemma cfc_id (ha : p a := by cfc_tac) : cfc (id : R -> R) a = a :=
  cfc_apply (id : R -> R) a ▸ cfcHom_id (p := p) ha

variable (R) in
/--
lemma `cfc_id'` / 引理 `cfc_id'`

English:
lemma cfc_id'
  given: (ha : p a := by cfc_tac)
  statement: cfc (fun x : R => x) a = a
  proof: cfc_id R a

中文:
引理 cfc_id'
  条件: (ha : p a := by cfc_tac)
  结论: cfc (fun x : R => x) a = a
  证明: cfc_id R a

Depends on / 依赖: cfc_id, cfc_tac
-/
lemma cfc_id' (ha : p a := by cfc_tac) : cfc (fun x : R => x) a = a := cfc_id R a

/--
lemma `cfc_map_spectrum` / 引理 `cfc_map_spectrum`

English:
lemma cfc_map_spectrum
  statement: (ha : p a := by cfc_tac)
  proof: by
  simp [cfc_apply f a, cfcHom_map_spectrum (p := p)]

中文:
引理 cfc_map_spectrum
  结论: (ha : p a := by cfc_tac)
  证明: by
  simp [cfc_apply f a, cfcHom_map_spectrum (p := p)]

Depends on / 依赖: ContinuousOn, cfcHom_map_spectrum, cfc_apply, cfc_cont_tac, cfc_tac, spectrum
-/
lemma cfc_map_spectrum (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    spectrum R (cfc f a) = f '' spectrum R a := by
  simp [cfc_apply f a, cfcHom_map_spectrum (p := p)]

/--
lemma `cfc_const` / 引理 `cfc_const`

English:
lemma cfc_const
  given: (r : R) (a : A) (ha : p a := by cfc_tac)
  proof: by
  rw [cfc_apply (fun _ : R => r) a]; rw [← AlgHomClass.commutes (cfcHom ha (p := p)) r]
  congr

中文:
引理 cfc_const
  条件: (r : R) (a : A) (ha : p a := by cfc_tac)
  证明: by
  rw [cfc_apply (fun _ : R => r) a]; rw [← AlgHomClass.commutes (cfcHom ha (p := p)) r]
  congr

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, algebraMap, cfcHom, cfc_apply, cfc_tac, commutes
-/
lemma cfc_const (r : R) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ => r) a = algebraMap R A r := by
  rw [cfc_apply (fun _ : R => r) a]; rw [← AlgHomClass.commutes (cfcHom ha (p := p)) r]
  congr

variable (R) in
include R in
/--
lemma `cfc_predicate_zero` / 引理 `cfc_predicate_zero`

English:
lemma cfc_predicate_zero
  statement: p 0
  proof: ContinuousFunctionalCalculus.predicate_zero (R := R)

中文:
引理 cfc_predicate_zero
  结论: p 0
  证明: ContinuousFunctionalCalculus.predicate_zero (R := R)

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.predicate_zero, predicate_zero
-/
lemma cfc_predicate_zero : p 0 :=
  ContinuousFunctionalCalculus.predicate_zero (R := R)

/--
lemma `cfc_predicate` / 引理 `cfc_predicate`

English:
lemma cfc_predicate
  given: (f : R -> R) (a : A)
  statement: p (cfc f a)
  proof: cfc_cases p a f (cfc_predicate_zero R) fun _ _ => cfcHom_predicate ..

中文:
引理 cfc_predicate
  条件: (f : R -> R) (a : A)
  结论: p (cfc f a)
  证明: cfc_cases p a f (cfc_predicate_zero R) fun _ _ => cfcHom_predicate ..

Depends on / 依赖: cfcHom_predicate, cfc_cases, cfc_predicate_zero
-/
lemma cfc_predicate (f : R -> R) (a : A) : p (cfc f a) :=
  cfc_cases p a f (cfc_predicate_zero R) fun _ _ => cfcHom_predicate ..

/--
lemma `cfc_predicate_algebraMap` / 引理 `cfc_predicate_algebraMap`

English:
lemma cfc_predicate_algebraMap
  given: (r : R)
  statement: p (algebraMap R A r)
  proof: cfc_const r (0 : A) (cfc_predicate_zero R) ▸ cfc_predicate (fun _ => r) 0

中文:
引理 cfc_predicate_algebraMap
  条件: (r : R)
  结论: p (algebraMap R A r)
  证明: cfc_const r (0 : A) (cfc_predicate_zero R) ▸ cfc_predicate (fun _ => r) 0

Depends on / 依赖: cfc_const, cfc_predicate, cfc_predicate_zero
-/
lemma cfc_predicate_algebraMap (r : R) : p (algebraMap R A r) :=
  cfc_const r (0 : A) (cfc_predicate_zero R) ▸ cfc_predicate (fun _ => r) 0

variable (R) in
include R in
/--
lemma `cfc_predicate_one` / 引理 `cfc_predicate_one`

English:
lemma cfc_predicate_one
  statement: p 1
  proof: map_one (algebraMap R A) ▸ cfc_predicate_algebraMap (1 : R)

中文:
引理 cfc_predicate_one
  结论: p 1
  证明: map_one (algebraMap R A) ▸ cfc_predicate_algebraMap (1 : R)

Depends on / 依赖: algebraMap, cfc_predicate_algebraMap, map_one
-/
lemma cfc_predicate_one : p 1 :=
  map_one (algebraMap R A) ▸ cfc_predicate_algebraMap (1 : R)

/--
lemma `cfc_congr` / 引理 `cfc_congr`

English:
lemma cfc_congr
  given: {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f g)
  proof: by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfc_apply (ha := h.1) (hf := h.2.congr hfg), cfc_apply (ha := h.1) (hf := h.2)]
    congr 2
    exact Set.domRestrict_eq_iff.mpr hfg
  · obtain (ha | hg) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_

中文:
引理 cfc_congr
  条件: {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f g)
  证明: by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfc_apply (ha := h.1) (hf := h.2.congr hfg), cfc_apply (ha := h.1) (hf := h.2)]
    congr 2
    exact Set.domRestrict_eq_iff.mpr hfg
  · obtain (ha | hg) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_

Depends on / 依赖: ContinuousOn, Set.domRestrict_eq_iff.mpr, cfc_apply, cfc_apply_of_not_continuousOn, cfc_apply_of_not_predicate, domRestrict_eq_iff, hf.congr, hfg.symm, not_and_or, not_and_or.mp, spectrum
-/
lemma cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f g) :
    cfc f a = cfc g a := by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfc_apply (ha := h.1) (hf := h.2.congr hfg), cfc_apply (ha := h.1) (hf := h.2)]
    congr 2
    exact Set.domRestrict_eq_iff.mpr hfg
  · obtain (ha | hg) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hg, cfc_apply_of_not_continuousOn]
      exact fun hf => hg (hf.congr hfg.symm)

/--
lemma `eqOn_of_cfc_eq_cfc` / 引理 `eqOn_of_cfc_eq_cfc`

English:
lemma eqOn_of_cfc_eq_cfc
  statement: {f g : R -> R} {a : A} (h : cfc f a = cfc g a)
  proof: by
  rw [cfc_apply f a]; rw [cfc_apply g a] at h
  exact fun x hx => congr($(cfcHom_injective ha h) ⟨x, hx⟩)

中文:
引理 eqOn_of_cfc_eq_cfc
  结论: {f g : R -> R} {a : A} (h : cfc f a = cfc g a)
  证明: by
  rw [cfc_apply f a]; rw [cfc_apply g a] at h
  exact fun x hx => congr($(cfcHom_injective ha h) ⟨x, hx⟩)

Depends on / 依赖: ContinuousOn, cfcHom_injective, cfc_apply, cfc_cont_tac, cfc_tac, spectrum
-/
lemma eqOn_of_cfc_eq_cfc {f g : R -> R} {a : A} (h : cfc f a = cfc g a)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (spectrum R a).EqOn f g := by
  rw [cfc_apply f a]; rw [cfc_apply g a] at h
  exact fun x hx => congr($(cfcHom_injective ha h) ⟨x, hx⟩)

set_option backward.privateInPublic true in
variable {a f g} in
include ha hf hg in
/--
lemma `cfc_eq_cfc_iff_eqOn` / 引理 `cfc_eq_cfc_iff_eqOn`

English:
lemma cfc_eq_cfc_iff_eqOn
  statement: cfc f a = cfc g a ↔ (spectrum R a).EqOn f g
  proof: ⟨eqOn_of_cfc_eq_cfc, cfc_congr⟩

中文:
引理 cfc_eq_cfc_iff_eqOn
  结论: cfc f a = cfc g a ↔ (spectrum R a).EqOn f g
  证明: ⟨eqOn_of_cfc_eq_cfc, cfc_congr⟩

Depends on / 依赖: cfc_congr, eqOn_of_cfc_eq_cfc
-/
lemma cfc_eq_cfc_iff_eqOn : cfc f a = cfc g a ↔ (spectrum R a).EqOn f g :=
  ⟨eqOn_of_cfc_eq_cfc, cfc_congr⟩

variable (R)

set_option backward.privateInPublic true in
include ha in
/--
lemma `cfc_one` / 引理 `cfc_one`

English:
lemma cfc_one
  statement: cfc (1 : R -> R) a = 1
  proof: cfc_apply (1 : R -> R) a ▸ map_one (cfcHom (show p a from ha))

中文:
引理 cfc_one
  结论: cfc (1 : R -> R) a = 1
  证明: cfc_apply (1 : R -> R) a ▸ map_one (cfcHom (show p a from ha))

Depends on / 依赖: cfcHom, cfc_apply, map_one
-/
lemma cfc_one : cfc (1 : R -> R) a = 1 :=
  cfc_apply (1 : R -> R) a ▸ map_one (cfcHom (show p a from ha))

set_option backward.privateInPublic true in
include ha in
/--
lemma `cfc_const_one` / 引理 `cfc_const_one`

English:
lemma cfc_const_one
  statement: cfc (fun _ : R => 1) a = 1
  proof: cfc_one R a

@[simp]

中文:
引理 cfc_const_one
  结论: cfc (fun _ : R => 1) a = 1
  证明: cfc_one R a

@[simp]

Depends on / 依赖: cfc_one
-/
lemma cfc_const_one : cfc (fun _ : R => 1) a = 1 := cfc_one R a

@[simp]
/--
lemma `cfc_zero` / 引理 `cfc_zero`

English:
lemma cfc_zero
  statement: cfc (0 : R -> R) a = 0
  proof: by
  by_cases ha : p a
  · exact cfc_apply (0 : R -> R) a ▸ map_zero (cfcHom ha)
  · rw [cfc_apply_of_not_predicate a ha]

@[simp]

中文:
引理 cfc_zero
  结论: cfc (0 : R -> R) a = 0
  证明: by
  by_cases ha : p a
  · exact cfc_apply (0 : R -> R) a ▸ map_zero (cfcHom ha)
  · rw [cfc_apply_of_not_predicate a ha]

@[simp]

Depends on / 依赖: cfcHom, cfc_apply, cfc_apply_of_not_predicate, map_zero
-/
lemma cfc_zero : cfc (0 : R -> R) a = 0 := by
  by_cases ha : p a
  · exact cfc_apply (0 : R -> R) a ▸ map_zero (cfcHom ha)
  · rw [cfc_apply_of_not_predicate a ha]

@[simp]
/--
lemma `cfc_const_zero` / 引理 `cfc_const_zero`

English:
lemma cfc_const_zero
  statement: cfc (fun _ : R => 0) a = 0
  proof: cfc_zero R a

中文:
引理 cfc_const_zero
  结论: cfc (fun _ : R => 0) a = 0
  证明: cfc_zero R a

Depends on / 依赖: cfc_zero
-/
lemma cfc_const_zero : cfc (fun _ : R => 0) a = 0 :=
  cfc_zero R a

variable {R}

/--
lemma `cfc_mul` / 引理 `cfc_mul`

English:
lemma cfc_mul
  statement: (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  proof: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_mul, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

中文:
引理 cfc_mul
  结论: (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  证明: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_mul, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_predicate, cfc_cont_tac, map_mul, spectrum
-/
lemma cfc_mul (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x => f x * g x) a = cfc f a * cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_mul, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

/--
lemma `cfc_pow` / 引理 `cfc_pow`

English:
lemma cfc_pow
  statement: (f : R -> R) (n : Nat) (a : A)
  proof: by
  rw [cfc_apply f a]; rw [← map_pow]; rw [cfc_apply _ a]
  congr

中文:
引理 cfc_pow
  结论: (f : R -> R) (n : 自然数) (a : A)
  证明: by
  rw [cfc_apply f a]; rw [← map_pow]; rw [cfc_apply _ a]
  congr

Depends on / 依赖: cfc_apply, cfc_cont_tac, cfc_tac, map_pow
-/
lemma cfc_pow (f : R -> R) (n : Nat) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => (f x) ^ n) a = cfc f a ^ n := by
  rw [cfc_apply f a]; rw [← map_pow]; rw [cfc_apply _ a]
  congr

/--
lemma `cfc_add` / 引理 `cfc_add`

English:
lemma cfc_add
  statement: (f g : R -> R) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  proof: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_add, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

中文:
引理 cfc_add
  结论: (f g : R -> R) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  证明: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_add, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_predicate, cfc_cont_tac, map_add, spectrum
-/
lemma cfc_add (f g : R -> R) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x => f x + g x) a = cfc f a + cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_add, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

/--
lemma `cfc_const_add` / 引理 `cfc_const_add`

English:
lemma cfc_const_add
  statement: (r : R) (f : R -> R) (a : A)
  proof: by
  have : (fun z => r + f z) = (fun z => (fun _ => r) z + f z) := by ext; simp
  rw [this]; rw [cfc_add a _ _ (continuousOn_const (c := r)) hf]; rw [cfc_const r a ha]

中文:
引理 cfc_const_add
  结论: (r : R) (f : R -> R) (a : A)
  证明: by
  have : (fun z => r + f z) = (fun z => (fun _ => r) z + f z) := by ext; simp
  rw [this]; rw [cfc_add a _ _ (continuousOn_const (c := r)) hf]; rw [cfc_const r a ha]

Depends on / 依赖: algebraMap, cfc_add, cfc_const, cfc_cont_tac, cfc_tac, continuousOn_const
-/
lemma cfc_const_add (r : R) (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => r + f x) a = algebraMap R A r + cfc f a := by
  have : (fun z => r + f z) = (fun z => (fun _ => r) z + f z) := by ext; simp
  rw [this]; rw [cfc_add a _ _ (continuousOn_const (c := r)) hf]; rw [cfc_const r a ha]

/--
lemma `cfc_add_const` / 引理 `cfc_add_const`

English:
lemma cfc_add_const
  statement: (r : R) (f : R -> R) (a : A)
  proof: by
  rw [add_comm (cfc f a)]
  conv_lhs => simp only [add_comm]
  exact cfc_const_add r f a hf ha

中文:
引理 cfc_add_const
  结论: (r : R) (f : R -> R) (a : A)
  证明: by
  rw [add_comm (cfc f a)]
  conv_lhs => simp only [add_comm]
  exact cfc_const_add r f a hf ha

Depends on / 依赖: add_comm, algebraMap, cfc_const_add, cfc_cont_tac, cfc_tac, conv_lhs
-/
lemma cfc_add_const (r : R) (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => f x + r) a = cfc f a + algebraMap R A r := by
  rw [add_comm (cfc f a)]
  conv_lhs => simp only [add_comm]
  exact cfc_const_add r f a hf ha

open Finset in
/--
lemma `cfc_sum` / 引理 `cfc_sum`

English:
lemma cfc_sum
  statement: {ι : Type*} (f : ι -> R -> R) (a : A) (s : Finset ι)
  proof: by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i in s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (spectrum R a) := by
      rw [sum_coe_sort s]; rw [hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s]; rw [← sum_coe_sort s]
   

中文:
引理 cfc_sum
  结论: {ι : 类型} (f : ι -> R -> R) (a : A) (s : 有限集 ι)
  证明: by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i in s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (spectrum R a) := by
      rw [sum_coe_sort s]; rw [hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s]; rw [← sum_coe_sort s]
   

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_predicate, cfc_apply_pi, cfc_cont_tac, continuousOn_finsetSum, map_sum, s.sum, spectrum, sum_coe_sort
-/
lemma cfc_sum {ι : Type*} (f : ι -> R -> R) (a : A) (s : Finset ι)
    (hf : forall i in s, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    cfc (∑ i in s, f i) a = ∑ i in s, cfc (f i) a := by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i in s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (spectrum R a) := by
      rw [sum_coe_sort s]; rw [hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s]; rw [← sum_coe_sort s]
    rw [cfc_apply_pi _ a ha (fun ⟨i]; rw [hi⟩ => hf i hi)]; rw [← map_sum]; rw [cfc_apply _ a ha hf']
    congr 1
    ext
    simp
  · simp [cfc_apply_of_not_predicate a ha]

open Finset in
/--
lemma `cfc_sum_univ` / 引理 `cfc_sum_univ`

English:
lemma cfc_sum_univ
  statement: {ι : Type*} [Fintype ι] (f : ι -> R -> R) (a : A)
  proof: cfc_sum f a _ fun i _ => hf i

中文:
引理 cfc_sum_univ
  结论: {ι : 类型} [有限类型 ι] (f : ι -> R -> R) (a : A)
  证明: cfc_sum f a _ fun i _ => hf i

Depends on / 依赖: cfc_cont_tac, cfc_sum
-/
lemma cfc_sum_univ {ι : Type*} [Fintype ι] (f : ι -> R -> R) (a : A)
    (hf : forall i, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    cfc (∑ i, f i) a = ∑ i, cfc (f i) a :=
  cfc_sum f a _ fun i _ => hf i

/--
lemma `cfc_smul` / 引理 `cfc_smul`

English:
lemma cfc_smul
  statement: {S : Type*} [SMul S R] [ContinuousConstSMul S R]
  proof: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

中文:
引理 cfc_smul
  结论: {S : 类型} [标量乘法 S R] [连续常数标量乘法 S R]
  证明: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

Depends on / 依赖: Pi.smul_def, cfc_apply, cfc_apply_of_not_predicate, cfc_cont_tac, map_smul, simp_rw, smul_def, smul_one_smul
-/
lemma cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)]
    (s : S) (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x => s • f x) a = s • cfc f a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

/--
lemma `cfc_const_mul` / 引理 `cfc_const_mul`

English:
lemma cfc_const_mul
  statement: (r : R) (f : R -> R) (a : A)
  proof: cfc_smul r f a

中文:
引理 cfc_const_mul
  结论: (r : R) (f : R -> R) (a : A)
  证明: cfc_smul r f a

Depends on / 依赖: cfc_cont_tac, cfc_smul
-/
lemma cfc_const_mul (r : R) (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x => r * f x) a = r • cfc f a :=
  cfc_smul r f a

/--
lemma `cfc_star` / 引理 `cfc_star`

English:
lemma cfc_star
  given: (f : R -> R) (a : A)
  statement: cfc (fun x => star (f x)) a = star (cfc f a)
  proof: by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a]; rw [← map_star]; rw [cfc_apply _ a]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_con

中文:
引理 cfc_star
  条件: (f : R -> R) (a : A)
  结论: cfc (fun x => star (f x)) a = star (cfc f a)
  证明: by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a]; rw [← map_star]; rw [cfc_apply _ a]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_con

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_continuousOn, cfc_apply_of_not_predicate, hf_star, hf_star.star, map_star, not_and_or, not_and_or.mp, spectrum, star_zero
-/
lemma cfc_star (f : R -> R) (a : A) : cfc (fun x => star (f x)) a = star (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a]; rw [← map_star]; rw [cfc_apply _ a]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_continuousOn, star_zero]
exact fun hf_star => hf by simpa using hf_star.star

/--
lemma `cfc_pow_id` / 引理 `cfc_pow_id`

English:
lemma cfc_pow_id
  given: (a : A) (n : Nat) (ha : p a := by cfc_tac)
  statement: cfc (· ^ n : R -> R) a = a ^ n
  proof: by
  rw [cfc_pow ..]; rw [cfc_id' ..]

中文:
引理 cfc_pow_id
  条件: (a : A) (n : 自然数) (ha : p a := by cfc_tac)
  结论: cfc (· ^ n : R -> R) a = a ^ n
  证明: by
  rw [cfc_pow ..]; rw [cfc_id' ..]

Depends on / 依赖: cfc_id, cfc_pow, cfc_tac
-/
lemma cfc_pow_id (a : A) (n : Nat) (ha : p a := by cfc_tac) : cfc (· ^ n : R -> R) a = a ^ n := by
  rw [cfc_pow ..]; rw [cfc_id' ..]

/--
lemma `cfc_smul_id` / 引理 `cfc_smul_id`

English:
lemma cfc_smul_id
  statement: {S : Type*} [SMul S R] [ContinuousConstSMul S R]
  proof: by
  rw [cfc_smul ..]; rw [cfc_id' ..]

中文:
引理 cfc_smul_id
  结论: {S : 类型} [标量乘法 S R] [连续常数标量乘法 S R]
  证明: by
  rw [cfc_smul ..]; rw [cfc_id' ..]

Depends on / 依赖: cfc_id, cfc_smul, cfc_tac
-/
lemma cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfc (s • · : R -> R) a = s • a := by
  rw [cfc_smul ..]; rw [cfc_id' ..]

/--
lemma `cfc_const_mul_id` / 引理 `cfc_const_mul_id`

English:
lemma cfc_const_mul_id
  given: (r : R) (a : A) (ha : p a := by cfc_tac)
  statement: cfc (r * ·) a = r • a
  proof: cfc_smul_id r a

中文:
引理 cfc_const_mul_id
  条件: (r : R) (a : A) (ha : p a := by cfc_tac)
  结论: cfc (r * ·) a = r • a
  证明: cfc_smul_id r a

Depends on / 依赖: cfc_smul_id, cfc_tac
-/
lemma cfc_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfc (r * ·) a = r • a :=
  cfc_smul_id r a

set_option backward.privateInPublic true in
include ha in
/--
lemma `cfc_star_id` / 引理 `cfc_star_id`

English:
lemma cfc_star_id
  statement: cfc (star · : R -> R) a = star a
  proof: by
  rw [cfc_star ..]; rw [cfc_id' ..]

中文:
引理 cfc_star_id
  结论: cfc (star · : R -> R) a = star a
  证明: by
  rw [cfc_star ..]; rw [cfc_id' ..]

Depends on / 依赖: cfc_id, cfc_star
-/
lemma cfc_star_id : cfc (star · : R -> R) a = star a := by
  rw [cfc_star ..]; rw [cfc_id' ..]

variable (R) in
/--
theorem `range_cfc_eq_range_cfcHom` / 定理 `range_cfc_eq_range_cfcHom`

English:
theorem range_cfc_eq_range_cfcHom
  given: [StarModule R A] {a : A} (ha : p a)
  proof: by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfc_cases _ a f (zero_mem _) fun hf ha => ⟨_, rfl⟩
.symm⟩ · exact ⟨Subtype.val.extend f 0, cfcHom_eq_cfc_extend _ ha _

中文:
定理 range_cfc_eq_range_cfcHom
  条件: [对合模 R A] {a : A} (ha : p a)
  证明: by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfc_cases _ a f (zero_mem _) fun hf ha => ⟨_, rfl⟩
.symm⟩ · exact ⟨Subtype.val.extend f 0, cfcHom_eq_cfc_extend _ ha _

Depends on / 依赖: Subtype, Subtype.val.extend, all_goals, cfcHom, cfcHom_eq_cfc_extend, cfc_cases, extend, zero_mem
-/
theorem range_cfc_eq_range_cfcHom [StarModule R A] {a : A} (ha : p a) :
    Set.range (cfc (R := R) · a) = (cfcHom ha (R := R)).range := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfc_cases _ a f (zero_mem _) fun hf ha => ⟨_, rfl⟩
.symm⟩ · exact ⟨Subtype.val.extend f 0, cfcHom_eq_cfc_extend _ ha _

section Polynomial
open Polynomial

/--
lemma `cfc_eval_X` / 引理 `cfc_eval_X`

English:
lemma cfc_eval_X
  given: (ha : p a := by cfc_tac)
  statement: cfc (X : R[X]).eval a = a
  proof: by
  simpa using! cfc_id R a

中文:
引理 cfc_eval_X
  条件: (ha : p a := by cfc_tac)
  结论: cfc (X : R[X]).eval a = a
  证明: by
  simpa using! cfc_id R a

Depends on / 依赖: cfc_id, cfc_tac
-/
lemma cfc_eval_X (ha : p a := by cfc_tac) : cfc (X : R[X]).eval a = a := by
  simpa using! cfc_id R a

/--
lemma `cfc_eval_C` / 引理 `cfc_eval_C`

English:
lemma cfc_eval_C
  given: (r : R) (a : A) (ha : p a := by cfc_tac)
  proof: by
  simp [cfc_const r a]

中文:
引理 cfc_eval_C
  条件: (r : R) (a : A) (ha : p a := by cfc_tac)
  证明: by
  simp [cfc_const r a]

Depends on / 依赖: algebraMap, cfc_const, cfc_tac
-/
lemma cfc_eval_C (r : R) (a : A) (ha : p a := by cfc_tac) :
    cfc (C r).eval a = algebraMap R A r := by
  simp [cfc_const r a]

/--
lemma `cfc_map_polynomial` / 引理 `cfc_map_polynomial`

English:
lemma cfc_map_polynomial
  statement: (q : R[X]) (f : R -> R) (a : A) (ha : p a := by cfc_tac)
  proof: by
  induction q using Polynomial.induction_on with
  | C r => simp [cfc_const r a]
  | add q₁ q₂ hq₁ hq₂ =>
    simp only [eval_add, map_add, ← hq₁, ← hq₂, cfc_add a (q₁.eval <| f ·) (q₂.eval <| f ·)]
  | monomial n r _ =>
    simp only [eval_mul, eval_C, eval_X_pow, map_mul, aeval_C, map_pow, aeva

中文:
引理 cfc_map_polynomial
  结论: (q : R[X]) (f : R -> R) (a : A) (ha : p a := by cfc_tac)
  证明: by
  induction q using Polynomial.induction_on with
  | C r => simp [cfc_const r a]
  | add q₁ q₂ hq₁ hq₂ =>
    simp only [eval_add, map_add, ← hq₁, ← hq₂, cfc_add a (q₁.eval <| f ·) (q₂.eval <| f ·)]
  | monomial n r _ =>
    simp only [eval_mul, eval_C, eval_X_pow, map_mul, aeval_C, map_pow, aeva

Depends on / 依赖: ContinuousOn, Polynomial, Polynomial.induction_on, aeval_C, aeval_X, algebraMap_smul, cfc_add, cfc_const, cfc_const_mul, cfc_cont_tac, cfc_pow, cfc_tac, eval_C, eval_X_pow, eval_add, eval_mul, induction_on, map_add, map_mul, map_pow
-/
lemma cfc_map_polynomial (q : R[X]) (f : R -> R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x => q.eval (f x)) a = aeval (cfc f a) q := by
  induction q using Polynomial.induction_on with
  | C r => simp [cfc_const r a]
  | add q₁ q₂ hq₁ hq₂ =>
    simp only [eval_add, map_add, ← hq₁, ← hq₂, cfc_add a (q₁.eval <| f ·) (q₂.eval <| f ·)]
  | monomial n r _ =>
    simp only [eval_mul, eval_C, eval_X_pow, map_mul, aeval_C, map_pow, aeval_X]
    rw [cfc_const_mul ..]; rw [cfc_pow _ (n + 1) _]; rw [← smul_eq_mul]; rw [algebraMap_smul]

/--
lemma `cfc_polynomial` / 引理 `cfc_polynomial`

English:
lemma cfc_polynomial
  given: (q : R[X]) (a : A) (ha : p a := by cfc_tac)
  proof: by
  rw [cfc_map_polynomial ..]; rw [cfc_id' ..]

中文:
引理 cfc_polynomial
  条件: (q : R[X]) (a : A) (ha : p a := by cfc_tac)
  证明: by
  rw [cfc_map_polynomial ..]; rw [cfc_id' ..]

Depends on / 依赖: cfc_id, cfc_map_polynomial, cfc_tac, q.eval
-/
lemma cfc_polynomial (q : R[X]) (a : A) (ha : p a := by cfc_tac) :
    cfc q.eval a = aeval a q := by
  rw [cfc_map_polynomial ..]; rw [cfc_id' ..]

end Polynomial

section Comp

variable [UniqueHom R A]

/--
lemma `cfc_comp` / 引理 `cfc_comp`

English:
lemma cfc_comp
  statement: (g f : R -> R) (a : A) (ha : p a := by cfc_tac)
  proof: by
have := hg.comp hf (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcHom (show p a from ha) (ContinuousMap.mk _ hf.domRestrict)) =
      f '' (spectrum R a) := by
    rw [cfcHom_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply ..]; rw [cfc_apply f a]; rw [cfc_apply _ _ (cf

中文:
引理 cfc_comp
  结论: (g f : R -> R) (a : A) (ha : p a := by cfc_tac)
  证明: by
have := hg.comp hf (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcHom (show p a from ha) (ContinuousMap.mk _ hf.domRestrict)) =
      f '' (spectrum R a) := by
    rw [cfcHom_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply ..]; rw [cfc_apply f a]; rw [cfc_apply _ _ (cf

Depends on / 依赖: ContinuousMap, ContinuousMap.mk, ContinuousOn, cfcHom, cfcHom_map_spectrum, cfcHom_predicate, cfc_apply, cfc_cont_tac, cfc_tac, convert, domRestrict, hf.domRestrict, hg.comp, mapsTo_image, sp_eq, spectrum
-/
lemma cfc_comp (g f : R -> R) (a : A) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (g ∘ f) a = cfc g (cfc f a) := by
have := hg.comp hf (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcHom (show p a from ha) (ContinuousMap.mk _ hf.domRestrict)) =
      f '' (spectrum R a) := by
    rw [cfcHom_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply ..]; rw [cfc_apply f a]; rw [cfc_apply _ _ (cfcHom_predicate (show p a from ha) _) (by convert! hg)]; rw [← cfcHom_comp _ _]
  swap
· exact ContinuousMap.mk _ hf.domRestrict.codRestrict fun x => by rw [sp_eq]; use x.1; simp
  · congr
  · exact fun _ => rfl

/--
lemma `cfc_comp'` / 引理 `cfc_comp'`

English:
lemma cfc_comp'
  statement: (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
  proof: cfc_comp g f a

中文:
引理 cfc_comp'
  结论: (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
  证明: cfc_comp g f a

Depends on / 依赖: ContinuousOn, cfc_comp, cfc_cont_tac, cfc_tac, spectrum
-/
lemma cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (g <| f ·) a = cfc g (cfc f a) :=
  cfc_comp g f a

/--
lemma `cfc_comp_pow` / 引理 `cfc_comp_pow`

English:
lemma cfc_comp_pow
  statement: (f : R -> R) (n : Nat) (a : A)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_pow_id ..]

中文:
引理 cfc_comp_pow
  结论: (f : R -> R) (n : 自然数) (a : A)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_pow_id ..]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_pow_id, cfc_tac
-/
lemma cfc_comp_pow (f : R -> R) (n : Nat) (a : A)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| · ^ n) a = cfc f (a ^ n) := by
  rw [cfc_comp' ..]; rw [cfc_pow_id ..]

/--
lemma `cfc_comp_smul` / 引理 `cfc_comp_smul`

English:
lemma cfc_comp_smul
  statement: {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroClass S A]
  proof: by
  rw [cfc_comp' ..]; rw [cfc_smul_id ..]

中文:
引理 cfc_comp_smul
  结论: {S : 类型} [标量乘法 S R] [连续常数标量乘法 S R] [SMulZero类 S A]
  证明: by
  rw [cfc_comp' ..]; rw [cfc_smul_id ..]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_smul_id, cfc_tac
-/
lemma cfc_comp_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroClass S A]
    [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (f : R -> R) (a : A)
    (hf : ContinuousOn f ((s • ·) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| s • ·) a = cfc f (s • a) := by
  rw [cfc_comp' ..]; rw [cfc_smul_id ..]

/--
lemma `cfc_comp_const_mul` / 引理 `cfc_comp_const_mul`

English:
lemma cfc_comp_const_mul
  statement: (r : R) (f : R -> R) (a : A)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_const_mul_id ..]

中文:
引理 cfc_comp_const_mul
  结论: (r : R) (f : R -> R) (a : A)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_const_mul_id ..]

Depends on / 依赖: cfc_comp, cfc_const_mul_id, cfc_cont_tac, cfc_tac
-/
lemma cfc_comp_const_mul (r : R) (f : R -> R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| r * ·) a = cfc f (r • a) := by
  rw [cfc_comp' ..]; rw [cfc_const_mul_id ..]

/--
lemma `cfc_comp_star` / 引理 `cfc_comp_star`

English:
lemma cfc_comp_star
  statement: (f : R -> R) (a : A)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_star_id ..]

中文:
引理 cfc_comp_star
  结论: (f : R -> R) (a : A)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_star_id ..]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_star_id, cfc_tac
-/
lemma cfc_comp_star (f : R -> R) (a : A)
    (hf : ContinuousOn f (star '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| star ·) a = cfc f (star a) := by
  rw [cfc_comp' ..]; rw [cfc_star_id ..]

open Polynomial in
/--
lemma `cfc_comp_polynomial` / 引理 `cfc_comp_polynomial`

English:
lemma cfc_comp_polynomial
  statement: (q : R[X]) (f : R -> R) (a : A)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_polynomial ..]

中文:
引理 cfc_comp_polynomial
  结论: (q : R[X]) (f : R -> R) (a : A)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_polynomial ..]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_polynomial, cfc_tac, q.eval
-/
lemma cfc_comp_polynomial (q : R[X]) (f : R -> R) (a : A)
    (hf : ContinuousOn f (q.eval '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| q.eval ·) a = cfc f (aeval a q) := by
  rw [cfc_comp' ..]; rw [cfc_polynomial ..]

end Comp

/--
lemma `CFC.eq_algebraMap_of_spectrum_subset_singleton` / 引理 `CFC.eq_algebraMap_of_spectrum_subset_singleton`

English:
lemma CFC.eq_algebraMap_of_spectrum_subset_singleton
  statement: (r : R) (h_spec : spectrum R a subseteq {r})
  proof: by
  simpa [cfc_id R a, cfc_const r a] using
    cfc_congr (f := id) (g := fun _ : R => r) (a := a) fun x hx => by simpa using h_spec hx

中文:
引理 CFC.eq_algebraMap_of_spectrum_subset_singleton
  结论: (r : R) (h_spec : spectrum R a subseteq {r})
  证明: by
  simpa [cfc_id R a, cfc_const r a] using
    cfc_congr (f := id) (g := fun _ : R => r) (a := a) fun x hx => by simpa using h_spec hx

Depends on / 依赖: algebraMap, cfc_congr, cfc_const, cfc_id, cfc_tac, h_spec
-/
lemma CFC.eq_algebraMap_of_spectrum_subset_singleton (r : R) (h_spec : spectrum R a subseteq {r})
    (ha : p a := by cfc_tac) : a = algebraMap R A r := by
  simpa [cfc_id R a, cfc_const r a] using
    cfc_congr (f := id) (g := fun _ : R => r) (a := a) fun x hx => by simpa using h_spec hx

/--
lemma `CFC.eq_zero_of_spectrum_subset_zero` / 引理 `CFC.eq_zero_of_spectrum_subset_zero`

English:
lemma CFC.eq_zero_of_spectrum_subset_zero
  given: (h_spec : spectrum R a subseteq {0}) (ha : p a := by cfc_tac)
  proof: by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 0 h_spec

中文:
引理 CFC.eq_zero_of_spectrum_subset_zero
  条件: (h_spec : spectrum R a subseteq {0}) (ha : p a := by cfc_tac)
  证明: by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 0 h_spec

Depends on / 依赖: cfc_tac, eq_algebraMap_of_spectrum_subset_singleton, h_spec
-/
lemma CFC.eq_zero_of_spectrum_subset_zero (h_spec : spectrum R a subseteq {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 0 h_spec

/--
lemma `CFC.eq_one_of_spectrum_subset_one` / 引理 `CFC.eq_one_of_spectrum_subset_one`

English:
lemma CFC.eq_one_of_spectrum_subset_one
  given: (h_spec : spectrum R a subseteq {1}) (ha : p a := by cfc_tac)
  proof: by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 1 h_spec

include instCFC in

中文:
引理 CFC.eq_one_of_spectrum_subset_one
  条件: (h_spec : spectrum R a subseteq {1}) (ha : p a := by cfc_tac)
  证明: by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 1 h_spec

include instCFC in

Depends on / 依赖: cfc_tac, eq_algebraMap_of_spectrum_subset_singleton, h_spec
-/
lemma CFC.eq_one_of_spectrum_subset_one (h_spec : spectrum R a subseteq {1}) (ha : p a := by cfc_tac) :
    a = 1 := by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 1 h_spec

include instCFC in
/--
lemma `CFC.spectrum_algebraMap_subset` / 引理 `CFC.spectrum_algebraMap_subset`

English:
lemma CFC.spectrum_algebraMap_subset
  given: (r : R)
  statement: spectrum R (algebraMap R A r) subseteq {r}
  proof: by
  rw [← cfc_const r 0 (cfc_predicate_zero R)]; rw [cfc_map_spectrum (fun _ => r) 0 (cfc_predicate_zero R)]
  rintro - ⟨x, -, rfl⟩
  simp

include instCFC in

中文:
引理 CFC.spectrum_algebraMap_subset
  条件: (r : R)
  结论: spectrum R (algebraMap R A r) subseteq {r}
  证明: by
  rw [← cfc_const r 0 (cfc_predicate_zero R)]; rw [cfc_map_spectrum (fun _ => r) 0 (cfc_predicate_zero R)]
  rintro - ⟨x, -, rfl⟩
  simp

include instCFC in

Depends on / 依赖: cfc_const, cfc_map_spectrum, cfc_predicate_zero
-/
lemma CFC.spectrum_algebraMap_subset (r : R) : spectrum R (algebraMap R A r) subseteq {r} := by
  rw [← cfc_const r 0 (cfc_predicate_zero R)]; rw [cfc_map_spectrum (fun _ => r) 0 (cfc_predicate_zero R)]
  rintro - ⟨x, -, rfl⟩
  simp

include instCFC in
/--
lemma `CFC.spectrum_algebraMap_eq` / 引理 `CFC.spectrum_algebraMap_eq`

English:
lemma CFC.spectrum_algebraMap_eq
  given: [Nontrivial A] (r : R)
  proof: by
  have hp : p 0 := cfc_predicate_zero R
  rw [← cfc_const r 0 hp]; rw [cfc_map_spectrum (fun _ => r) 0 hp]
  exact Set.Nonempty.image_const (⟨0, spectrum.zero_mem (R := R) not_isUnit_zero⟩) _

include instCFC in

中文:
引理 CFC.spectrum_algebraMap_eq
  条件: [非平凡 A] (r : R)
  证明: by
  have hp : p 0 := cfc_predicate_zero R
  rw [← cfc_const r 0 hp]; rw [cfc_map_spectrum (fun _ => r) 0 hp]
  exact Set.Nonempty.image_const (⟨0, spectrum.zero_mem (R := R) not_isUnit_zero⟩) _

include instCFC in

Depends on / 依赖: Nonempty, Set.Nonempty.image_const, cfc_const, cfc_map_spectrum, cfc_predicate_zero, image_const, not_isUnit_zero, spectrum, spectrum.zero_mem, zero_mem
-/
lemma CFC.spectrum_algebraMap_eq [Nontrivial A] (r : R) :
    spectrum R (algebraMap R A r) = {r} := by
  have hp : p 0 := cfc_predicate_zero R
  rw [← cfc_const r 0 hp]; rw [cfc_map_spectrum (fun _ => r) 0 hp]
  exact Set.Nonempty.image_const (⟨0, spectrum.zero_mem (R := R) not_isUnit_zero⟩) _

include instCFC in
/--
lemma `CFC.spectrum_zero_eq` / 引理 `CFC.spectrum_zero_eq`

English:
lemma CFC.spectrum_zero_eq
  given: [Nontrivial A]
  proof: by
  have : (0 : A) = algebraMap R A 0 := Eq.symm (map_zero (algebraMap R A))
  rw [this]; rw [spectrum_algebraMap_eq]

include instCFC in

中文:
引理 CFC.spectrum_zero_eq
  条件: [非平凡 A]
  证明: by
  have : (0 : A) = algebraMap R A 0 := Eq.symm (map_zero (algebraMap R A))
  rw [this]; rw [spectrum_algebraMap_eq]

include instCFC in

Depends on / 依赖: Eq.symm, algebraMap, map_zero, spectrum_algebraMap_eq
-/
lemma CFC.spectrum_zero_eq [Nontrivial A] :
    spectrum R (0 : A) = {0} := by
  have : (0 : A) = algebraMap R A 0 := Eq.symm (map_zero (algebraMap R A))
  rw [this]; rw [spectrum_algebraMap_eq]

include instCFC in
/--
lemma `CFC.spectrum_one_eq` / 引理 `CFC.spectrum_one_eq`

English:
lemma CFC.spectrum_one_eq
  given: [Nontrivial A]
  proof: by
  have : (1 : A) = algebraMap R A 1 := Eq.symm (map_one (algebraMap R A))
  rw [this]; rw [spectrum_algebraMap_eq]

@[simp]

中文:
引理 CFC.spectrum_one_eq
  条件: [非平凡 A]
  证明: by
  have : (1 : A) = algebraMap R A 1 := Eq.symm (map_one (algebraMap R A))
  rw [this]; rw [spectrum_algebraMap_eq]

@[simp]

Depends on / 依赖: Eq.symm, algebraMap, map_one, spectrum_algebraMap_eq
-/
lemma CFC.spectrum_one_eq [Nontrivial A] :
    spectrum R (1 : A) = {1} := by
  have : (1 : A) = algebraMap R A 1 := Eq.symm (map_one (algebraMap R A))
  rw [this]; rw [spectrum_algebraMap_eq]

@[simp]
/--
lemma `cfc_algebraMap` / 引理 `cfc_algebraMap`

English:
lemma cfc_algebraMap
  given: (r : R) (f : R -> R)
  statement: cfc f (algebraMap R A r) = algebraMap R A (f r)
  proof: by
  have h₁ : ContinuousOn f (spectrum R (algebraMap R A r)) :=
.mono CFC.spectrum_algebraMap_subset r continuousOn_singleton _ _
  rw [cfc_apply f (algebraMap R A r) (cfc_predicate_algebraMap r)]; rw [← AlgHomClass.commutes (cfcHom (p := p) (cfc_predicate_algebraMap r)) (f r)]
  congr
  ext ⟨x, hx

中文:
引理 cfc_algebraMap
  条件: (r : R) (f : R -> R)
  结论: cfc f (algebraMap R A r) = algebraMap R A (f r)
  证明: by
  have h₁ : ContinuousOn f (spectrum R (algebraMap R A r)) :=
.mono CFC.spectrum_algebraMap_subset r continuousOn_singleton _ _
  rw [cfc_apply f (algebraMap R A r) (cfc_predicate_algebraMap r)]; rw [← AlgHomClass.commutes (cfcHom (p := p) (cfc_predicate_algebraMap r)) (f r)]
  congr
  ext ⟨x, hx

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, CFC.spectrum_algebraMap_subset, ContinuousOn, algebraMap, cfcHom, cfc_apply, cfc_predicate_algebraMap, commutes, continuousOn_singleton, spectrum, spectrum_algebraMap_subset
-/
lemma cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap R A r) = algebraMap R A (f r) := by
  have h₁ : ContinuousOn f (spectrum R (algebraMap R A r)) :=
.mono CFC.spectrum_algebraMap_subset r continuousOn_singleton _ _
  rw [cfc_apply f (algebraMap R A r) (cfc_predicate_algebraMap r)]; rw [← AlgHomClass.commutes (cfcHom (p := p) (cfc_predicate_algebraMap r)) (f r)]
  congr
  ext ⟨x, hx⟩
  apply CFC.spectrum_algebraMap_subset r at hx
  simp_all

/--
lemma `cfc_apply_zero` / 引理 `cfc_apply_zero`

English:
lemma cfc_apply_zero
  given: {f : R -> R}
  statement: cfc f (0 : A) = algebraMap R A (f 0)
  proof: by
  simpa using cfc_algebraMap (A := A) 0 f

中文:
引理 cfc_apply_zero
  条件: {f : R -> R}
  结论: cfc f (0 : A) = algebraMap R A (f 0)
  证明: by
  simpa using cfc_algebraMap (A := A) 0 f
-/
@[simp] lemma cfc_apply_zero {f : R -> R} : cfc f (0 : A) = algebraMap R A (f 0) := by
  simpa using cfc_algebraMap (A := A) 0 f

/--
lemma `cfc_apply_one` / 引理 `cfc_apply_one`

English:
lemma cfc_apply_one
  given: {f : R -> R}
  statement: cfc f (1 : A) = algebraMap R A (f 1)
  proof: by
  simpa using cfc_algebraMap (A := A) 1 f

@[simp]

中文:
引理 cfc_apply_one
  条件: {f : R -> R}
  结论: cfc f (1 : A) = algebraMap R A (f 1)
  证明: by
  simpa using cfc_algebraMap (A := A) 1 f

@[simp]
-/
@[simp] lemma cfc_apply_one {f : R -> R} : cfc f (1 : A) = algebraMap R A (f 1) := by
  simpa using cfc_algebraMap (A := A) 1 f

@[simp]
/--
Instance `IsStarNormal.cfc_map` / 实例 `IsStarNormal.cfc_map`

English:
instance IsStarNormal.cfc_map
  signature: (f : R -> R) (a : A)
  body: by
    rw [Commute]; rw [SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

中文:
实例 是StarNormal.cfc_map
  签名: (f : R -> R) (a : A)
  定义体: by
    rw [Commute]; rw [SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

Depends on / 依赖: Commute, ContinuousOn, SemiconjBy, cfc_apply_of_not_continuousOn, cfc_mul, cfc_star, mul_comm, spectrum
-/
instance IsStarNormal.cfc_map (f : R -> R) (a : A) : IsStarNormal (cfc f a) where
  star_comm_self := by
    rw [Commute]; rw [SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

-- The following two lemmas are just `cfc_predicate`, but specific enough for the `@[simp]` tag.
@[simp]
/--
lemma `IsSelfAdjoint.cfc` / 引理 `IsSelfAdjoint.cfc`

English:
lemma IsSelfAdjoint.cfc
  statement: [ContinuousFunctionalCalculus R A IsSelfAdjoint]
  proof: cfc_predicate _ _

@[simp]

中文:
引理 IsSelfAdjoint.cfc
  结论: [余ntinuousFunctionalCalculus R A IsSelfAdjoint]
  证明: cfc_predicate _ _

@[simp]
-/
protected lemma IsSelfAdjoint.cfc [ContinuousFunctionalCalculus R A IsSelfAdjoint]
    {f : R -> R} {a : A} : IsSelfAdjoint (cfc f a) :=
  cfc_predicate _ _

@[simp]
/--
lemma `cfc_nonneg_of_predicate` / 引理 `cfc_nonneg_of_predicate`

English:
lemma cfc_nonneg_of_predicate
  statement: [LE A]
  proof: cfc_predicate _ _

中文:
引理 cfc_nonneg_of_predicate
  结论: [LE A]
  证明: cfc_predicate _ _

Depends on / 依赖: cfc_predicate
-/
lemma cfc_nonneg_of_predicate [LE A]
    [ContinuousFunctionalCalculus R A (0 <= ·)] {f : R -> R} {a : A} : 0 <= cfc f a :=
  cfc_predicate _ _

variable (R) in
/-- In an `R`-algebra with a continuous functional calculus, every element satisfying the predicate
has nonempty `R`-spectrum. -/
@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead."
  (since := "2026-03-08")]
/--
lemma `CFC.spectrum_nonempty` / 引理 `CFC.spectrum_nonempty`

English:
lemma CFC.spectrum_nonempty
  given: [Nontrivial A] (a : A) (ha : p a := by cfc_tac)
  proof: ContinuousFunctionalCalculus.spectrum_nonempty a ha

中文:
引理 CFC.spectrum_nonempty
  条件: [非平凡 A] (a : A) (ha : p a := by cfc_tac)
  证明: ContinuousFunctionalCalculus.spectrum_nonempty a ha

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.spectrum_nonempty, Nonempty, cfc_tac, spectrum, spectrum_nonempty
-/
lemma CFC.spectrum_nonempty [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    (spectrum R a).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty a ha

end CFC

end Basic

section Inv

variable {R A : Type*} {p : A -> Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/--
lemma `isUnit_cfc_iff` / 引理 `isUnit_cfc_iff`

English:
lemma isUnit_cfc_iff
  statement: (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  proof: by
  rw [← spectrum.zero_notMem_iff R]; rw [cfc_map_spectrum ..]
  simp

alias ⟨_, isUnit_cfc⟩ := isUnit_cfc_iff

中文:
引理 isUnit_cfc_iff
  结论: (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  证明: by
  rw [← spectrum.zero_notMem_iff R]; rw [cfc_map_spectrum ..]
  simp

alias ⟨_, isUnit_cfc⟩ := isUnit_cfc_iff

Depends on / 依赖: IsUnit, cfc_cont_tac, cfc_map_spectrum, cfc_tac, spectrum, spectrum.zero_notMem_iff, zero_notMem_iff
-/
lemma isUnit_cfc_iff (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : IsUnit (cfc f a) ↔ forall x in spectrum R a, f x != 0 := by
  rw [← spectrum.zero_notMem_iff R]; rw [cfc_map_spectrum ..]
  simp

alias ⟨_, isUnit_cfc⟩ := isUnit_cfc_iff

variable [ContinuousInv₀ R] (f : R -> R) (a : A)

/-- Bundle `cfc f a` into a unit given a proof that `f` is nonzero on the spectrum of `a`. -/
@[simps]
/--
Definition of `cfcUnits` / `cfcUnits` 的定义

English:
definition cfcUnits
  signature: (hf' : forall x in spectrum R a, f x != 0)
  body: cfc f a
  inv := cfc (fun x => (f x)⁻¹) a
  val_inv := by
    rw [← cfc_mul ..]; rw [← cfc_one R a]
    exact cfc_congr fun _ _ => by aesop
  inv_val := by
    rw [← cfc_mul ..]; rw [← cfc_one R a]
    exact cfc_congr fun _ _ => by aesop

中文:
定义 cfcUnits
  签名: (hf' : 对任意 x in spectrum R a, f x != 0)
  定义体: cfc f a
  inv := cfc (fun x => (f x)⁻¹) a
  val_inv := by
    rw [← cfc_mul ..]; rw [← cfc_one R a]
    exact cfc_congr fun _ _ => by aesop
  inv_val := by
    rw [← cfc_mul ..]; rw [← cfc_one R a]
    exact cfc_congr fun _ _ => by aesop

Depends on / 依赖: cfc_congr, cfc_cont_tac, cfc_mul, cfc_one, cfc_tac, inv_val, val_inv
-/
noncomputable def cfcUnits (hf' : forall x in spectrum R a, f x != 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) : Aˣ where
  val := cfc f a
  inv := cfc (fun x => (f x)⁻¹) a
  val_inv := by
    rw [← cfc_mul ..]; rw [← cfc_one R a]
    exact cfc_congr fun _ _ => by aesop
  inv_val := by
    rw [← cfc_mul ..]; rw [← cfc_one R a]
    exact cfc_congr fun _ _ => by aesop

/--
lemma `cfcUnits_pow` / 引理 `cfcUnits_pow`

English:
lemma cfcUnits_pow
  statement: (hf' : forall x in spectrum R a, f x != 0) (n : Nat)
  proof: by
  ext
  cases n with
  | zero => simp [cfc_const_one R a]
  | succ n => simp [cfc_pow f _ a]

中文:
引理 cfcUnits_pow
  结论: (hf' : 对任意 x in spectrum R a, f x != 0) (n : 自然数)
  证明: by
  ext
  cases n with
  | zero => simp [cfc_const_one R a]
  | succ n => simp [cfc_pow f _ a]

Depends on / 依赖: cfcUnits, cfc_const_one, cfc_cont_tac, cfc_pow, cfc_tac, fun_pow, hf.fun_pow, pow_ne_zero
-/
lemma cfcUnits_pow (hf' : forall x in spectrum R a, f x != 0) (n : Nat)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (cfcUnits f a hf') ^ n =
      cfcUnits _ _ (forall₂_imp (fun _ _ => pow_ne_zero n) hf') (hf := hf.fun_pow n) := by
  ext
  cases n with
  | zero => simp [cfc_const_one R a]
  | succ n => simp [cfc_pow f _ a]

/--
lemma `cfc_inv` / 引理 `cfc_inv`

English:
lemma cfc_inv
  statement: (hf' : forall x in spectrum R a, f x != 0)
  proof: by
  rw [← val_inv_cfcUnits f a hf']; rw [← val_cfcUnits f a hf']; rw [Ring.inverse_unit]

中文:
引理 cfc_inv
  结论: (hf' : 对任意 x in spectrum R a, f x != 0)
  证明: by
  rw [← val_inv_cfcUnits f a hf']; rw [← val_cfcUnits f a hf']; rw [Ring.inverse_unit]

Depends on / 依赖: Ring.inverse_unit, cfc_cont_tac, cfc_tac, inverse_unit, val_cfcUnits, val_inv_cfcUnits
-/
lemma cfc_inv (hf' : forall x in spectrum R a, f x != 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => (f x)⁻¹) a = (cfc f a)⁻¹ʳ := by
  rw [← val_inv_cfcUnits f a hf']; rw [← val_cfcUnits f a hf']; rw [Ring.inverse_unit]

/--
lemma `cfc_inv_id` / 引理 `cfc_inv_id`

English:
lemma cfc_inv_id
  given: (a : Aˣ) (ha : p a := by cfc_tac)
  proof: by
  rw [← Ring.inverse_unit]
  convert! cfc_inv (id : R -> R) (a : A) ?_
  · exact (cfc_id R (a : A)).symm
  · rintro x hx rfl
    exact spectrum.zero_notMem R a.isUnit hx

中文:
引理 cfc_inv_id
  条件: (a : Aˣ) (ha : p a := by cfc_tac)
  证明: by
  rw [← Ring.inverse_unit]
  convert! cfc_inv (id : R -> R) (a : A) ?_
  · exact (cfc_id R (a : A)).symm
  · rintro x hx rfl
    exact spectrum.zero_notMem R a.isUnit hx

Depends on / 依赖: Ring.inverse_unit, a.isUnit, cfc_id, cfc_inv, cfc_tac, convert, inverse_unit, isUnit, spectrum, spectrum.zero_notMem, zero_notMem
-/
lemma cfc_inv_id (a : Aˣ) (ha : p a := by cfc_tac) :
    cfc (fun x => x⁻¹ : R -> R) (a : A) = a⁻¹ := by
  rw [← Ring.inverse_unit]
  convert! cfc_inv (id : R -> R) (a : A) ?_
  · exact (cfc_id R (a : A)).symm
  · rintro x hx rfl
    exact spectrum.zero_notMem R a.isUnit hx

/--
lemma `cfc_ringInverse_id` / 引理 `cfc_ringInverse_id`

English:
lemma cfc_ringInverse_id
  given: (ha_unit : IsUnit a) (ha : p a := by cfc_tac)
  proof: by
  rw [Ring.inverse_of_isUnit ha_unit]
  change cfc (fun x => x⁻¹ : R -> R) (ha_unit.unit : A) = ha_unit.unit⁻¹
  exact cfc_inv_id _ ha

中文:
引理 cfc_ringInverse_id
  条件: (ha_unit : 是单位 a) (ha : p a := by cfc_tac)
  证明: by
  rw [Ring.inverse_of_isUnit ha_unit]
  change cfc (fun x => x⁻¹ : R -> R) (ha_unit.unit : A) = ha_unit.unit⁻¹
  exact cfc_inv_id _ ha

Depends on / 依赖: Ring.inverse_of_isUnit, cfc_inv_id, cfc_tac, ha_unit, ha_unit.unit, inverse_of_isUnit
-/
lemma cfc_ringInverse_id (ha_unit : IsUnit a) (ha : p a := by cfc_tac) :
    cfc (fun x => x⁻¹ : R -> R) a = a⁻¹ʳ := by
  rw [Ring.inverse_of_isUnit ha_unit]
  change cfc (fun x => x⁻¹ : R -> R) (ha_unit.unit : A) = ha_unit.unit⁻¹
  exact cfc_inv_id _ ha

/--
lemma `cfc_map_div` / 引理 `cfc_map_div`

English:
lemma cfc_map_div
  statement: (f g : R -> R) (a : A) (hg' : forall x in spectrum R a, g x != 0)
  proof: by
  simp only [div_eq_mul_inv]
  rw [cfc_mul ..]; rw [cfc_inv g a hg']

中文:
引理 cfc_map_div
  结论: (f g : R -> R) (a : A) (hg' : 对任意 x in spectrum R a, g x != 0)
  证明: by
  simp only [div_eq_mul_inv]
  rw [cfc_mul ..]; rw [cfc_inv g a hg']

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_inv, cfc_mul, cfc_tac, div_eq_mul_inv, spectrum
-/
lemma cfc_map_div (f g : R -> R) (a : A) (hg' : forall x in spectrum R a, g x != 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => f x / g x) a = cfc f a * (cfc g a)⁻¹ʳ := by
  simp only [div_eq_mul_inv]
  rw [cfc_mul ..]; rw [cfc_inv g a hg']

section ContinuousOnInvSpectrum
-- TODO: this section should probably be moved to another file altogether

variable {R A : Type*} [Semifield R] [Ring A] [TopologicalSpace R] [ContinuousInv₀ R]
variable [Algebra R A]

@[fun_prop]
/--
lemma `Units.continuousOn_inv₀_spectrum` / 引理 `Units.continuousOn_inv₀_spectrum`

English:
lemma Units.continuousOn_inv₀_spectrum
  given: (a : Aˣ)
  statement: ContinuousOn (· ⁻¹) (spectrum R (a : A))
  proof: continuousOn_inv₀.mono by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

@[fun_prop]

中文:
引理 单位群.continuousOn_inv₀_spectrum
  条件: (a : Aˣ)
  结论: ContinuousOn (· ⁻¹) (spectrum R (a : A))
  证明: continuousOn_inv₀.mono by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

@[fun_prop]

Depends on / 依赖: Set.subset_compl_singleton_iff, SubfieldClass, SubfieldClass.toNormedField, a.isUnit, isUnit, spectrum, spectrum.zero_notMem, subset_compl_singleton_iff, toNormedField, zero_notMem
-/
lemma Units.continuousOn_inv₀_spectrum (a : Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A)) :=
continuousOn_inv₀.mono by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

@[fun_prop]
/--
lemma `Units.continuousOn_zpow₀_spectrum` / 引理 `Units.continuousOn_zpow₀_spectrum`

English:
lemma Units.continuousOn_zpow₀_spectrum
  given: [ContinuousMul R] (a : Aˣ) (n : Int)
  proof: (continuousOn_zpow₀ n).mono by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

中文:
引理 单位群.continuousOn_zpow₀_spectrum
  条件: [连续乘法 R] (a : Aˣ) (n : 整数)
  证明: (continuousOn_zpow₀ n).mono by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

Depends on / 依赖: Set.subset_compl_singleton_iff, a.isUnit, isUnit, spectrum, spectrum.zero_notMem, subset_compl_singleton_iff, zero_notMem
-/
lemma Units.continuousOn_zpow₀_spectrum [ContinuousMul R] (a : Aˣ) (n : Int) :
    ContinuousOn (· ^ n) (spectrum R (a : A)) :=
(continuousOn_zpow₀ n).mono by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

end ContinuousOnInvSpectrum

/--
lemma `cfcUnits_zpow` / 引理 `cfcUnits_zpow`

English:
lemma cfcUnits_zpow
  statement: (hf' : forall x in spectrum R a, f x != 0) (n : Int)
  proof: by
  cases n with
  | ofNat _ => simpa using! cfcUnits_pow f a hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
.symm exact cfc_pow (hf := hf.inv₀ hf') ..

中文:
引理 cfcUnits_zpow
  结论: (hf' : 对任意 x in spectrum R a, f x != 0) (n : 整数)
  证明: by
  cases n with
  | ofNat _ => simpa using! cfcUnits_pow f a hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
.symm exact cfc_pow (hf := hf.inv₀ hf') ..

Depends on / 依赖: Or.inl, cfcUnits, cfcUnits_pow, cfc_cont_tac, cfc_pow, cfc_tac, hf.inv, hf.zpow, inv_pow, negSucc, zpow_ne_zero, zpow_negSucc
-/
lemma cfcUnits_zpow (hf' : forall x in spectrum R a, f x != 0) (n : Int)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (cfcUnits f a hf') ^ n =
      cfcUnits (f ^ n) a (forall₂_imp (fun _ _ => zpow_ne_zero n) hf')
        (hf.zpow₀ n (forall₂_imp (fun _ _ => Or.inl) hf')) := by
  cases n with
  | ofNat _ => simpa using! cfcUnits_pow f a hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
.symm exact cfc_pow (hf := hf.inv₀ hf') ..

/--
lemma `cfc_zpow` / 引理 `cfc_zpow`

English:
lemma cfc_zpow
  given: (a : Aˣ) (n : Int) (ha : p a := by cfc_tac)
  proof: by
  cases n with
  | ofNat n => simpa using cfc_pow_id (a : A) n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfc_pow (fun x => x⁻¹ : R -> R) (n + 1) (a : A)
exact this.trans congr($(cfc_inv_id a) ^ (n + 1))

中文:
引理 cfc_zpow
  条件: (a : Aˣ) (n : 整数) (ha : p a := by cfc_tac)
  证明: by
  cases n with
  | ofNat n => simpa using cfc_pow_id (a : A) n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfc_pow (fun x => x⁻¹ : R -> R) (n + 1) (a : A)
exact this.trans congr($(cfc_inv_id a) ^ (n + 1))

Depends on / 依赖: Units.val_pow_eq_pow_val, cfc_inv_id, cfc_pow, cfc_pow_id, cfc_tac, inv_pow, negSucc, this.trans, val_pow_eq_pow_val, zpow_negSucc
-/
lemma cfc_zpow (a : Aˣ) (n : Int) (ha : p a := by cfc_tac) :
    cfc (fun x : R => x ^ n) (a : A) = ↑(a ^ n) := by
  cases n with
  | ofNat n => simpa using cfc_pow_id (a : A) n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfc_pow (fun x => x⁻¹ : R -> R) (n + 1) (a : A)
exact this.trans congr($(cfc_inv_id a) ^ (n + 1))

variable [UniqueHom R A]

/--
lemma `cfc_comp_inv` / 引理 `cfc_comp_inv`

English:
lemma cfc_comp_inv
  statement: (f : R -> R) (a : Aˣ)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_inv_id _]

中文:
引理 cfc_comp_inv
  结论: (f : R -> R) (a : Aˣ)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_inv_id _]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_inv_id, cfc_tac
-/
lemma cfc_comp_inv (f : R -> R) (a : Aˣ)
    (hf : ContinuousOn f ((·⁻¹) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc (fun x => f x⁻¹) (a : A) = cfc f (↑a⁻¹ : A) := by
  rw [cfc_comp' ..]; rw [cfc_inv_id _]

/--
lemma `cfc_comp_zpow` / 引理 `cfc_comp_zpow`

English:
lemma cfc_comp_zpow
  statement: (f : R -> R) (n : Int) (a : Aˣ)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_zpow a]

中文:
引理 cfc_comp_zpow
  结论: (f : R -> R) (n : 整数) (a : Aˣ)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_zpow a]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_tac, cfc_zpow
-/
lemma cfc_comp_zpow (f : R -> R) (n : Int) (a : Aˣ)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc (fun x => f (x ^ n)) (a : A) = cfc f (↑(a ^ n) : A) := by
  rw [cfc_comp' ..]; rw [cfc_zpow a]

end Inv

section Neg

variable {R A : Type*} {p : A -> Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
variable (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
variable (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)

set_option backward.privateInPublic true in
include hf hg in
/--
lemma `cfc_sub` / 引理 `cfc_sub`

English:
lemma cfc_sub
  statement: cfc (fun x => f x - g x) a = cfc f a - cfc g a
  proof: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_sub, cfc_apply ..]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

中文:
引理 cfc_sub
  结论: cfc (fun x => f x - g x) a = cfc f a - cfc g a
  证明: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_sub, cfc_apply ..]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

Depends on / 依赖: cfc_apply, cfc_apply_of_not_predicate, map_sub
-/
lemma cfc_sub : cfc (fun x => f x - g x) a = cfc f a - cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_sub, cfc_apply ..]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

/--
lemma `cfc_neg` / 引理 `cfc_neg`

English:
lemma cfc_neg
  statement: cfc (fun x => -(f x)) a = -(cfc f a)
  proof: by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a]; rw [← map_neg]; rw [cfc_apply ..]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_conti

中文:
引理 cfc_neg
  结论: cfc (fun x => -(f x)) a = -(cfc f a)
  证明: by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a]; rw [← map_neg]; rw [cfc_apply ..]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_conti

Depends on / 依赖: ContinuousOn, cfc_apply, cfc_apply_of_not_continuousOn, cfc_apply_of_not_predicate, fun_neg, hf_neg, hf_neg.fun_neg, map_neg, neg_zero, not_and_or, not_and_or.mp, spectrum
-/
lemma cfc_neg : cfc (fun x => -(f x)) a = -(cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a]; rw [← map_neg]; rw [cfc_apply ..]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_continuousOn, neg_zero]
exact fun hf_neg => hf by simpa using hf_neg.fun_neg

/--
lemma `cfc_neg'` / 引理 `cfc_neg'`

English:
lemma cfc_neg'
  statement: cfc (-f) = (-cfc f : A -> A)
  proof: by ext1 a; exact cfc_neg f a

中文:
引理 cfc_neg'
  结论: cfc (-f) = (-cfc f : A -> A)
  证明: by ext1 a; exact cfc_neg f a

Depends on / 依赖: cfc_neg
-/
lemma cfc_neg' : cfc (-f) = (-cfc f : A -> A) := by ext1 a; exact cfc_neg f a

/--
lemma `cfc_neg_id` / 引理 `cfc_neg_id`

English:
lemma cfc_neg_id
  given: (ha : p a := by cfc_tac)
  statement: cfc (- · : R -> R) a = -a
  proof: by
  rw [cfc_neg _ a]; rw [cfc_id' R a]

中文:
引理 cfc_neg_id
  条件: (ha : p a := by cfc_tac)
  结论: cfc (- · : R -> R) a = -a
  证明: by
  rw [cfc_neg _ a]; rw [cfc_id' R a]

Depends on / 依赖: cfc_id, cfc_neg, cfc_tac
-/
lemma cfc_neg_id (ha : p a := by cfc_tac) : cfc (- · : R -> R) a = -a := by
  rw [cfc_neg _ a]; rw [cfc_id' R a]

variable [UniqueHom R A]

/--
lemma `cfc_comp_neg` / 引理 `cfc_comp_neg`

English:
lemma cfc_comp_neg
  statement: (hf : ContinuousOn f ((-·) '' (spectrum R (a : A))) := by cfc_cont_tac)
  proof: by
  rw [cfc_comp' ..]; rw [cfc_neg_id _]

中文:
引理 cfc_comp_neg
  结论: (hf : ContinuousOn f ((-·) '' (spectrum R (a : A))) := by cfc_cont_tac)
  证明: by
  rw [cfc_comp' ..]; rw [cfc_neg_id _]

Depends on / 依赖: cfc_comp, cfc_cont_tac, cfc_neg_id, cfc_tac
-/
lemma cfc_comp_neg (hf : ContinuousOn f ((-·) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (f <| - ·) a = cfc f (-a) := by
  rw [cfc_comp' ..]; rw [cfc_neg_id _]

end Neg

section Order

section Semiring

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [PartialOrder R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

/--
lemma `cfcHom_mono` / 引理 `cfcHom_mono`

English:
lemma cfcHom_mono
  given: {a : A} (ha : p a) {f g : C(spectrum R a, R)} (hfg : f <= g)
  proof: OrderHomClass.mono (cfcHom ha) hfg

中文:
引理 cfcHom_mono
  条件: {a : A} (ha : p a) {f g : C(spectrum R a, R)} (hfg : f <= g)
  证明: OrderHomClass.mono (cfcHom ha) hfg

Depends on / 依赖: OrderHomClass, OrderHomClass.mono, cfcHom
-/
lemma cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (hfg : f <= g) :
    cfcHom ha f <= cfcHom ha g :=
  OrderHomClass.mono (cfcHom ha) hfg

/--
lemma `cfcHom_nonneg_iff` / 引理 `cfcHom_nonneg_iff`

English:
lemma cfcHom_nonneg_iff
  given: [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(spectrum R a, R)}
  proof: by
  constructor
  · exact fun hf x => (cfcHom_map_spectrum ha (R := R) _ ▸ spectrum_nonneg_of_nonneg hf) ⟨x, rfl⟩
  · simpa using (cfcHom_mono ha (f := 0) (g := f) ·)

中文:
引理 cfcHom_nonneg_iff
  条件: [NonnegSpectrum类 R A] {a : A} (ha : p a) {f : C(spectrum R a, R)}
  证明: by
  constructor
  · exact fun hf x => (cfcHom_map_spectrum ha (R := R) _ ▸ spectrum_nonneg_of_nonneg hf) ⟨x, rfl⟩
  · simpa using (cfcHom_mono ha (f := 0) (g := f) ·)

Depends on / 依赖: cfcHom_map_spectrum, cfcHom_mono, spectrum_nonneg_of_nonneg
-/
lemma cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(spectrum R a, R)} :
    0 <= cfcHom ha f ↔ 0 <= f := by
  constructor
  · exact fun hf x => (cfcHom_map_spectrum ha (R := R) _ ▸ spectrum_nonneg_of_nonneg hf) ⟨x, rfl⟩
  · simpa using (cfcHom_mono ha (f := 0) (g := f) ·)

/--
lemma `cfcHom_isStrictlyPositive_iff` / 引理 `cfcHom_isStrictlyPositive_iff`

English:
lemma cfcHom_isStrictlyPositive_iff
  statement: [NonnegSpectrumClass R A] {a : A} (ha : p a)
  proof: by
refine ⟨fun hf x => hf.spectrum_pos cfcHom_map_spectrum (R := R) ha _ ▸ Set.mem_range_self x,
.mpr fun x => le_of_lt (h x), ?_⟩⟩ fun h => ⟨cfcHom_nonneg_iff _
  apply spectrum.isUnit_of_zero_notMem (R := R)
  grind [cfcHom_map_spectrum, ne_of_lt]

中文:
引理 cfcHom_isStrictlyPositive_iff
  结论: [NonnegSpectrum类 R A] {a : A} (ha : p a)
  证明: by
refine ⟨fun hf x => hf.spectrum_pos cfcHom_map_spectrum (R := R) ha _ ▸ Set.mem_range_self x,
.mpr fun x => le_of_lt (h x), ?_⟩⟩ fun h => ⟨cfcHom_nonneg_iff _
  apply spectrum.isUnit_of_zero_notMem (R := R)
  grind [cfcHom_map_spectrum, ne_of_lt]

Depends on / 依赖: Set.mem_range_self, cfcHom_map_spectrum, cfcHom_nonneg_iff, hf.spectrum_pos, isUnit_of_zero_notMem, le_of_lt, mem_range_self, ne_of_lt, spectrum, spectrum.isUnit_of_zero_notMem, spectrum_pos
-/
lemma cfcHom_isStrictlyPositive_iff [NonnegSpectrumClass R A] {a : A} (ha : p a)
    {f : C(spectrum R a, R)} : IsStrictlyPositive (cfcHom ha f) ↔ forall x, 0 < f x := by
refine ⟨fun hf x => hf.spectrum_pos cfcHom_map_spectrum (R := R) ha _ ▸ Set.mem_range_self x,
.mpr fun x => le_of_lt (h x), ?_⟩⟩ fun h => ⟨cfcHom_nonneg_iff _
  apply spectrum.isUnit_of_zero_notMem (R := R)
  grind [cfcHom_map_spectrum, ne_of_lt]

/--
lemma `cfc_mono` / 引理 `cfc_mono`

English:
lemma cfc_mono
  statement: {f g : R -> R} {a : A} (h : forall x in spectrum R a, f x <= g x)
  proof: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a]
    exact cfcHom_mono ha fun x => h x.1 x.2
  · simp only [cfc_apply_of_not_predicate _ ha, le_rfl]

中文:
引理 cfc_mono
  结论: {f g : R -> R} {a : A} (h : 对任意 x in spectrum R a, f x <= g x)
  证明: by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a]
    exact cfcHom_mono ha fun x => h x.1 x.2
  · simp only [cfc_apply_of_not_predicate _ ha, le_rfl]

Depends on / 依赖: ContinuousOn, cfcHom_mono, cfc_apply, cfc_apply_of_not_predicate, cfc_cont_tac, le_rfl, spectrum
-/
lemma cfc_mono {f g : R -> R} {a : A} (h : forall x in spectrum R a, f x <= g x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc f a <= cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a]
    exact cfcHom_mono ha fun x => h x.1 x.2
  · simp only [cfc_apply_of_not_predicate _ ha, le_rfl]

/--
lemma `cfc_nonneg_iff` / 引理 `cfc_nonneg_iff`

English:
lemma cfc_nonneg_iff
  statement: [NonnegSpectrumClass R A] (f : R -> R) (a : A)
  proof: by
  rw [cfc_apply ..]; rw [cfcHom_nonneg_iff]; rw [ContinuousMap.le_def]
  simp

中文:
引理 cfc_nonneg_iff
  结论: [NonnegSpectrum类 R A] (f : R -> R) (a : A)
  证明: by
  rw [cfc_apply ..]; rw [cfcHom_nonneg_iff]; rw [ContinuousMap.le_def]
  simp

Depends on / 依赖: ContinuousMap, ContinuousMap.le_def, cfcHom_nonneg_iff, cfc_apply, cfc_cont_tac, cfc_tac, le_def, spectrum
-/
lemma cfc_nonneg_iff [NonnegSpectrumClass R A] (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : 0 <= cfc f a ↔ forall x in spectrum R a, 0 <= f x := by
  rw [cfc_apply ..]; rw [cfcHom_nonneg_iff]; rw [ContinuousMap.le_def]
  simp

/--
lemma `StarOrderedRing.nonneg_iff_spectrum_nonneg` / 引理 `StarOrderedRing.nonneg_iff_spectrum_nonneg`

English:
lemma StarOrderedRing.nonneg_iff_spectrum_nonneg
  statement: [NonnegSpectrumClass R A] (a : A)
  proof: by
  have := cfc_nonneg_iff (id : R -> R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

中文:
引理 StarOrdered环.nonneg_iff_spectrum_nonneg
  结论: [NonnegSpectrum类 R A] (a : A)
  证明: by
  have := cfc_nonneg_iff (id : R -> R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

Depends on / 依赖: cfc_id, cfc_nonneg_iff, cfc_tac, fun_prop, spectrum
-/
lemma StarOrderedRing.nonneg_iff_spectrum_nonneg [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : 0 <= a ↔ forall x in spectrum R a, 0 <= x := by
  have := cfc_nonneg_iff (id : R -> R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

/--
lemma `cfc_isStrictlyPositive_iff` / 引理 `cfc_isStrictlyPositive_iff`

English:
lemma cfc_isStrictlyPositive_iff
  statement: [NonnegSpectrumClass R A] (f : R -> R) (a : A)
  proof: by
  rw [cfc_apply ..]; rw [cfcHom_isStrictlyPositive_iff]
  simp

中文:
引理 cfc_isStrictlyPositive_iff
  结论: [NonnegSpectrum类 R A] (f : R -> R) (a : A)
  证明: by
  rw [cfc_apply ..]; rw [cfcHom_isStrictlyPositive_iff]
  simp

Depends on / 依赖: IsStrictlyPositive, cfcHom_isStrictlyPositive_iff, cfc_apply, cfc_cont_tac, cfc_tac, spectrum
-/
lemma cfc_isStrictlyPositive_iff [NonnegSpectrumClass R A] (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : IsStrictlyPositive (cfc f a) ↔ forall x in spectrum R a, 0 < f x := by
  rw [cfc_apply ..]; rw [cfcHom_isStrictlyPositive_iff]
  simp

/--
lemma `StarOrderedRing.isStrictlyPositive_iff_spectrum_pos` / 引理 `StarOrderedRing.isStrictlyPositive_iff_spectrum_pos`

English:
lemma StarOrderedRing.isStrictlyPositive_iff_spectrum_pos
  statement: [NonnegSpectrumClass R A] (a : A)
  proof: by
  have := cfc_isStrictlyPositive_iff (id : R -> R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

中文:
引理 StarOrdered环.isStrictlyPositive_iff_spectrum_pos
  结论: [NonnegSpectrum类 R A] (a : A)
  证明: by
  have := cfc_isStrictlyPositive_iff (id : R -> R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

Depends on / 依赖: IsStrictlyPositive, cfc_id, cfc_isStrictlyPositive_iff, cfc_tac, fun_prop, spectrum
-/
lemma StarOrderedRing.isStrictlyPositive_iff_spectrum_pos [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : IsStrictlyPositive a ↔ forall x in spectrum R a, 0 < x := by
  have := cfc_isStrictlyPositive_iff (id : R -> R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

/--
lemma `cfc_nonneg` / 引理 `cfc_nonneg`

English:
lemma cfc_nonneg
  given: {f : R -> R} {a : A} (h : forall x in spectrum R a, 0 <= f x)
  proof: by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

中文:
引理 cfc_nonneg
  条件: {f : R -> R} {a : A} (h : 对任意 x in spectrum R a, 0 <= f x)
  证明: by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

Depends on / 依赖: ContinuousOn, cfc_apply_of_not_continuousOn, cfc_mono, le_rfl, spectrum
-/
lemma cfc_nonneg {f : R -> R} {a : A} (h : forall x in spectrum R a, 0 <= f x) :
    0 <= cfc f a := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

/--
lemma `cfc_nonpos` / 引理 `cfc_nonpos`

English:
lemma cfc_nonpos
  given: (f : R -> R) (a : A) (h : forall x in spectrum R a, f x <= 0)
  proof: by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

中文:
引理 cfc_nonpos
  条件: (f : R -> R) (a : A) (h : 对任意 x in spectrum R a, f x <= 0)
  证明: by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

Depends on / 依赖: ContinuousOn, cfc_apply_of_not_continuousOn, cfc_mono, le_rfl, spectrum
-/
lemma cfc_nonpos (f : R -> R) (a : A) (h : forall x in spectrum R a, f x <= 0) :
    cfc f a <= 0 := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

/--
lemma `cfc_le_algebraMap` / 引理 `cfc_le_algebraMap`

English:
lemma cfc_le_algebraMap
  statement: (f : R -> R) (r : R) (a : A) (h : forall x in spectrum R a, f x <= r)
  proof: cfc_const r a ▸ cfc_mono h

中文:
引理 cfc_le_algebraMap
  结论: (f : R -> R) (r : R) (a : A) (h : 对任意 x in spectrum R a, f x <= r)
  证明: cfc_const r a ▸ cfc_mono h

Depends on / 依赖: algebraMap, cfc_const, cfc_cont_tac, cfc_mono, cfc_tac
-/
lemma cfc_le_algebraMap (f : R -> R) (r : R) (a : A) (h : forall x in spectrum R a, f x <= r)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a <= algebraMap R A r :=
  cfc_const r a ▸ cfc_mono h

/--
lemma `algebraMap_le_cfc` / 引理 `algebraMap_le_cfc`

English:
lemma algebraMap_le_cfc
  statement: (f : R -> R) (r : R) (a : A) (h : forall x in spectrum R a, r <= f x)
  proof: cfc_const r a ▸ cfc_mono h

中文:
引理 algebraMap_le_cfc
  结论: (f : R -> R) (r : R) (a : A) (h : 对任意 x in spectrum R a, r <= f x)
  证明: cfc_const r a ▸ cfc_mono h

Depends on / 依赖: algebraMap, cfc_const, cfc_cont_tac, cfc_mono, cfc_tac
-/
lemma algebraMap_le_cfc (f : R -> R) (r : R) (a : A) (h : forall x in spectrum R a, r <= f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    algebraMap R A r <= cfc f a :=
  cfc_const r a ▸ cfc_mono h

/--
lemma `le_algebraMap_of_spectrum_le` / 引理 `le_algebraMap_of_spectrum_le`

English:
lemma le_algebraMap_of_spectrum_le
  statement: {r : R} {a : A} (h : forall x in spectrum R a, x <= r)
  proof: by
  rw [← cfc_id R a]
  exact cfc_le_algebraMap id r a h

中文:
引理 le_algebraMap_of_spectrum_le
  结论: {r : R} {a : A} (h : 对任意 x in spectrum R a, x <= r)
  证明: by
  rw [← cfc_id R a]
  exact cfc_le_algebraMap id r a h

Depends on / 依赖: algebraMap, cfc_id, cfc_le_algebraMap, cfc_tac
-/
lemma le_algebraMap_of_spectrum_le {r : R} {a : A} (h : forall x in spectrum R a, x <= r)
    (ha : p a := by cfc_tac) : a <= algebraMap R A r := by
  rw [← cfc_id R a]
  exact cfc_le_algebraMap id r a h

/--
lemma `algebraMap_le_of_le_spectrum` / 引理 `algebraMap_le_of_le_spectrum`

English:
lemma algebraMap_le_of_le_spectrum
  statement: {r : R} {a : A} (h : forall x in spectrum R a, r <= x)
  proof: by
  rw [← cfc_id R a]
  exact algebraMap_le_cfc id r a h

中文:
引理 algebraMap_le_of_le_spectrum
  结论: {r : R} {a : A} (h : 对任意 x in spectrum R a, r <= x)
  证明: by
  rw [← cfc_id R a]
  exact algebraMap_le_cfc id r a h

Depends on / 依赖: algebraMap, algebraMap_le_cfc, cfc_id, cfc_tac
-/
lemma algebraMap_le_of_le_spectrum {r : R} {a : A} (h : forall x in spectrum R a, r <= x)
    (ha : p a := by cfc_tac) : algebraMap R A r <= a := by
  rw [← cfc_id R a]
  exact algebraMap_le_cfc id r a h

/--
lemma `cfc_le_one` / 引理 `cfc_le_one`

English:
lemma cfc_le_one
  given: (f : R -> R) (a : A) (h : forall x in spectrum R a, f x <= 1)
  statement: cfc f a <= 1
  proof: by
  apply cfc_cases (· <= 1) _ _ (by simp) fun hf ha => ?_
  rw [← map_one (cfcHom ha (R := R))]
  apply cfcHom_mono ha
  simpa [ContinuousMap.le_def] using h

中文:
引理 cfc_le_one
  条件: (f : R -> R) (a : A) (h : 对任意 x in spectrum R a, f x <= 1)
  结论: cfc f a <= 1
  证明: by
  apply cfc_cases (· <= 1) _ _ (by simp) fun hf ha => ?_
  rw [← map_one (cfcHom ha (R := R))]
  apply cfcHom_mono ha
  simpa [ContinuousMap.le_def] using h

Depends on / 依赖: ContinuousMap, ContinuousMap.le_def, cfcHom, cfcHom_mono, cfc_cases, le_def, map_one
-/
lemma cfc_le_one (f : R -> R) (a : A) (h : forall x in spectrum R a, f x <= 1) : cfc f a <= 1 := by
  apply cfc_cases (· <= 1) _ _ (by simp) fun hf ha => ?_
  rw [← map_one (cfcHom ha (R := R))]
  apply cfcHom_mono ha
  simpa [ContinuousMap.le_def] using h

/--
lemma `one_le_cfc` / 引理 `one_le_cfc`

English:
lemma one_le_cfc
  statement: (f : R -> R) (a : A) (h : forall x in spectrum R a, 1 <= f x)
  proof: by
  simpa using algebraMap_le_cfc f 1 a h

中文:
引理 one_le_cfc
  结论: (f : R -> R) (a : A) (h : 对任意 x in spectrum R a, 1 <= f x)
  证明: by
  simpa using algebraMap_le_cfc f 1 a h

Depends on / 依赖: algebraMap_le_cfc, cfc_cont_tac, cfc_tac
-/
lemma one_le_cfc (f : R -> R) (a : A) (h : forall x in spectrum R a, 1 <= f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    1 <= cfc f a := by
  simpa using algebraMap_le_cfc f 1 a h

/--
lemma `CFC.le_one` / 引理 `CFC.le_one`

English:
lemma CFC.le_one
  given: {a : A} (h : forall x in spectrum R a, x <= 1) (ha : p a := by cfc_tac)
  proof: by
  simpa using le_algebraMap_of_spectrum_le h

中文:
引理 CFC.le_one
  条件: {a : A} (h : 对任意 x in spectrum R a, x <= 1) (ha : p a := by cfc_tac)
  证明: by
  simpa using le_algebraMap_of_spectrum_le h

Depends on / 依赖: cfc_tac, le_algebraMap_of_spectrum_le
-/
lemma CFC.le_one {a : A} (h : forall x in spectrum R a, x <= 1) (ha : p a := by cfc_tac) :
    a <= 1 := by
  simpa using le_algebraMap_of_spectrum_le h

/--
lemma `CFC.one_le` / 引理 `CFC.one_le`

English:
lemma CFC.one_le
  given: {a : A} (h : forall x in spectrum R a, 1 <= x) (ha : p a := by cfc_tac)
  proof: by
  simpa using algebraMap_le_of_le_spectrum h

中文:
引理 CFC.one_le
  条件: {a : A} (h : 对任意 x in spectrum R a, 1 <= x) (ha : p a := by cfc_tac)
  证明: by
  simpa using algebraMap_le_of_le_spectrum h

Depends on / 依赖: algebraMap_le_of_le_spectrum, cfc_tac
-/
lemma CFC.one_le {a : A} (h : forall x in spectrum R a, 1 <= x) (ha : p a := by cfc_tac) :
    1 <= a := by
  simpa using algebraMap_le_of_le_spectrum h

end Semiring

section NNReal

open scoped NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  [Algebra Real>=0 A] [ContinuousFunctionalCalculus Real>=0 A (0 <= ·)]

/--
lemma `CFC.inv_nonneg_of_nonneg` / 引理 `CFC.inv_nonneg_of_nonneg`

English:
lemma CFC.inv_nonneg_of_nonneg
  given: (a : Aˣ) (ha : (0 : A) <= a := by cfc_tac)
  statement: (0 : A) <= a⁻¹
  proof: cfc_inv_id (R := Real>=0) a ▸ cfc_predicate _ (a : A)

中文:
引理 CFC.inv_nonneg_of_nonneg
  条件: (a : Aˣ) (ha : (0 : A) <= a := by cfc_tac)
  结论: (0 : A) <= a⁻¹
  证明: cfc_inv_id (R := Real>=0) a ▸ cfc_predicate _ (a : A)

Depends on / 依赖: cfc_inv_id, cfc_predicate, cfc_tac
-/
lemma CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A) <= a := by cfc_tac) : (0 : A) <= a⁻¹ :=
  cfc_inv_id (R := Real>=0) a ▸ cfc_predicate _ (a : A)

/--
lemma `CFC.inv_nonneg` / 引理 `CFC.inv_nonneg`

English:
lemma CFC.inv_nonneg
  given: (a : Aˣ)
  statement: (0 : A) <= a⁻¹ ↔ (0 : A) <= a
  proof: ⟨fun _ => inv_inv a ▸ inv_nonneg_of_nonneg a⁻¹, fun _ => inv_nonneg_of_nonneg a⟩

中文:
引理 CFC.inv_nonneg
  条件: (a : Aˣ)
  结论: (0 : A) <= a⁻¹ ↔ (0 : A) <= a
  证明: ⟨fun _ => inv_inv a ▸ inv_nonneg_of_nonneg a⁻¹, fun _ => inv_nonneg_of_nonneg a⟩

Depends on / 依赖: inv_inv, inv_nonneg_of_nonneg
-/
lemma CFC.inv_nonneg (a : Aˣ) : (0 : A) <= a⁻¹ ↔ (0 : A) <= a :=
  ⟨fun _ => inv_inv a ▸ inv_nonneg_of_nonneg a⁻¹, fun _ => inv_nonneg_of_nonneg a⟩

end NNReal

section Ring

variable {R A : Type*} {p : A -> Prop} [CommRing R] [PartialOrder R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]
variable [NonnegSpectrumClass R A]

/--
lemma `cfcHom_le_iff` / 引理 `cfcHom_le_iff`

English:
lemma cfcHom_le_iff
  given: {a : A} (ha : p a) {f g : C(spectrum R a, R)}
  proof: by
  rw [← sub_nonneg]; rw [← map_sub]; rw [cfcHom_nonneg_iff]; rw [sub_nonneg]

中文:
引理 cfcHom_le_iff
  条件: {a : A} (ha : p a) {f g : C(spectrum R a, R)}
  证明: by
  rw [← sub_nonneg]; rw [← map_sub]; rw [cfcHom_nonneg_iff]; rw [sub_nonneg]

Depends on / 依赖: cfcHom_nonneg_iff, map_sub, sub_nonneg
-/
lemma cfcHom_le_iff {a : A} (ha : p a) {f g : C(spectrum R a, R)} :
    cfcHom ha f <= cfcHom ha g ↔ f <= g := by
  rw [← sub_nonneg]; rw [← map_sub]; rw [cfcHom_nonneg_iff]; rw [sub_nonneg]

/--
lemma `cfc_le_iff` / 引理 `cfc_le_iff`

English:
lemma cfc_le_iff
  statement: (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  proof: by
  rw [cfc_apply f a]; rw [cfc_apply g a]; rw [cfcHom_le_iff (show p a from ha)]; rw [ContinuousMap.le_def]
  simp

中文:
引理 cfc_le_iff
  结论: (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  证明: by
  rw [cfc_apply f a]; rw [cfc_apply g a]; rw [cfcHom_le_iff (show p a from ha)]; rw [ContinuousMap.le_def]
  simp

Depends on / 依赖: ContinuousMap, ContinuousMap.le_def, ContinuousOn, cfcHom_le_iff, cfc_apply, cfc_cont_tac, cfc_tac, le_def, spectrum
-/
lemma cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a <= cfc g a ↔ forall x in spectrum R a, f x <= g x := by
  rw [cfc_apply f a]; rw [cfc_apply g a]; rw [cfcHom_le_iff (show p a from ha)]; rw [ContinuousMap.le_def]
  simp

/--
lemma `cfc_nonpos_iff` / 引理 `cfc_nonpos_iff`

English:
lemma cfc_nonpos_iff
  statement: (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  proof: by
  simp_rw [← neg_nonneg, ← cfc_neg]
  exact cfc_nonneg_iff (fun x => -f x) a

中文:
引理 cfc_nonpos_iff
  结论: (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
  证明: by
  simp_rw [← neg_nonneg, ← cfc_neg]
  exact cfc_nonneg_iff (fun x => -f x) a

Depends on / 依赖: cfc_cont_tac, cfc_neg, cfc_nonneg_iff, cfc_tac, neg_nonneg, simp_rw, spectrum
-/
lemma cfc_nonpos_iff (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc f a <= 0 ↔ forall x in spectrum R a, f x <= 0 := by
  simp_rw [← neg_nonneg, ← cfc_neg]
  exact cfc_nonneg_iff (fun x => -f x) a

/--
lemma `cfc_le_algebraMap_iff` / 引理 `cfc_le_algebraMap_iff`

English:
lemma cfc_le_algebraMap_iff
  statement: (f : R -> R) (r : R) (a : A)
  proof: by
  rw [← cfc_const r a]; rw [cfc_le_iff ..]

中文:
引理 cfc_le_algebraMap_iff
  结论: (f : R -> R) (r : R) (a : A)
  证明: by
  rw [← cfc_const r a]; rw [cfc_le_iff ..]

Depends on / 依赖: algebraMap, cfc_const, cfc_cont_tac, cfc_le_iff, cfc_tac, spectrum
-/
lemma cfc_le_algebraMap_iff (f : R -> R) (r : R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a <= algebraMap R A r ↔ forall x in spectrum R a, f x <= r := by
  rw [← cfc_const r a]; rw [cfc_le_iff ..]

/--
lemma `algebraMap_le_cfc_iff` / 引理 `algebraMap_le_cfc_iff`

English:
lemma algebraMap_le_cfc_iff
  statement: (f : R -> R) (r : R) (a : A)
  proof: by
  rw [← cfc_const r a]; rw [cfc_le_iff ..]

中文:
引理 algebraMap_le_cfc_iff
  结论: (f : R -> R) (r : R) (a : A)
  证明: by
  rw [← cfc_const r a]; rw [cfc_le_iff ..]

Depends on / 依赖: algebraMap, cfc_const, cfc_cont_tac, cfc_le_iff, cfc_tac, spectrum
-/
lemma algebraMap_le_cfc_iff (f : R -> R) (r : R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    algebraMap R A r <= cfc f a ↔ forall x in spectrum R a, r <= f x := by
  rw [← cfc_const r a]; rw [cfc_le_iff ..]

/--
lemma `le_algebraMap_iff_spectrum_le` / 引理 `le_algebraMap_iff_spectrum_le`

English:
lemma le_algebraMap_iff_spectrum_le
  given: {r : R} {a : A} (ha : p a := by cfc_tac)
  proof: by
  nth_rw 1 [← cfc_id R a]
  exact cfc_le_algebraMap_iff id r a

中文:
引理 le_algebraMap_iff_spectrum_le
  条件: {r : R} {a : A} (ha : p a := by cfc_tac)
  证明: by
  nth_rw 1 [← cfc_id R a]
  exact cfc_le_algebraMap_iff id r a

Depends on / 依赖: algebraMap, cfc_id, cfc_le_algebraMap_iff, cfc_tac, nth_rw, spectrum
-/
lemma le_algebraMap_iff_spectrum_le {r : R} {a : A} (ha : p a := by cfc_tac) :
    a <= algebraMap R A r ↔ forall x in spectrum R a, x <= r := by
  nth_rw 1 [← cfc_id R a]
  exact cfc_le_algebraMap_iff id r a

/--
lemma `algebraMap_le_iff_le_spectrum` / 引理 `algebraMap_le_iff_le_spectrum`

English:
lemma algebraMap_le_iff_le_spectrum
  given: {r : R} {a : A} (ha : p a := by cfc_tac)
  proof: by
  nth_rw 1 [← cfc_id R a]
  exact algebraMap_le_cfc_iff id r a

中文:
引理 algebraMap_le_iff_le_spectrum
  条件: {r : R} {a : A} (ha : p a := by cfc_tac)
  证明: by
  nth_rw 1 [← cfc_id R a]
  exact algebraMap_le_cfc_iff id r a

Depends on / 依赖: algebraMap, algebraMap_le_cfc_iff, cfc_id, cfc_tac, nth_rw, spectrum
-/
lemma algebraMap_le_iff_le_spectrum {r : R} {a : A} (ha : p a := by cfc_tac) :
    algebraMap R A r <= a ↔ forall x in spectrum R a, r <= x := by
  nth_rw 1 [← cfc_id R a]
  exact algebraMap_le_cfc_iff id r a

/--
lemma `cfc_le_one_iff` / 引理 `cfc_le_one_iff`

English:
lemma cfc_le_one_iff
  statement: (f : R -> R) (a : A)
  proof: by
  simpa using cfc_le_algebraMap_iff f 1 a

中文:
引理 cfc_le_one_iff
  结论: (f : R -> R) (a : A)
  证明: by
  simpa using cfc_le_algebraMap_iff f 1 a

Depends on / 依赖: cfc_cont_tac, cfc_le_algebraMap_iff, cfc_tac, spectrum
-/
lemma cfc_le_one_iff (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a <= 1 ↔ forall x in spectrum R a, f x <= 1 := by
  simpa using cfc_le_algebraMap_iff f 1 a

/--
lemma `one_le_cfc_iff` / 引理 `one_le_cfc_iff`

English:
lemma one_le_cfc_iff
  statement: (f : R -> R) (a : A)
  proof: by
  simpa using algebraMap_le_cfc_iff f 1 a

中文:
引理 one_le_cfc_iff
  结论: (f : R -> R) (a : A)
  证明: by
  simpa using algebraMap_le_cfc_iff f 1 a

Depends on / 依赖: algebraMap_le_cfc_iff, cfc_cont_tac, cfc_tac, spectrum
-/
lemma one_le_cfc_iff (f : R -> R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    1 <= cfc f a ↔ forall x in spectrum R a, 1 <= f x := by
  simpa using algebraMap_le_cfc_iff f 1 a

/--
lemma `CFC.le_one_iff` / 引理 `CFC.le_one_iff`

English:
lemma CFC.le_one_iff
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  simpa using le_algebraMap_iff_spectrum_le (r := (1 : R)) (a := a)

中文:
引理 CFC.le_one_iff
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  simpa using le_algebraMap_iff_spectrum_le (r := (1 : R)) (a := a)

Depends on / 依赖: cfc_tac, le_algebraMap_iff_spectrum_le, spectrum
-/
lemma CFC.le_one_iff (a : A) (ha : p a := by cfc_tac) :
    a <= 1 ↔ forall x in spectrum R a, x <= 1 := by
  simpa using le_algebraMap_iff_spectrum_le (r := (1 : R)) (a := a)

/--
lemma `CFC.one_le_iff` / 引理 `CFC.one_le_iff`

English:
lemma CFC.one_le_iff
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  simpa using algebraMap_le_iff_le_spectrum (r := (1 : R)) (a := a)

中文:
引理 CFC.one_le_iff
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  simpa using algebraMap_le_iff_le_spectrum (r := (1 : R)) (a := a)

Depends on / 依赖: algebraMap_le_iff_le_spectrum, cfc_tac, spectrum
-/
lemma CFC.one_le_iff (a : A) (ha : p a := by cfc_tac) :
    1 <= a ↔ forall x in spectrum R a, 1 <= x := by
  simpa using algebraMap_le_iff_le_spectrum (r := (1 : R)) (a := a)

end Ring

end Order

/-! ### `cfcHom` on a superset of the spectrum -/

section Superset

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

/-- The composition of `cfcHom` with the natural embedding `C(s, R) → C(spectrum R a, R)`
whenever `spectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions applied to multiple
distinct elements, with the added constraint that `cfc` does not suffice. This can occur, for
example, if it is necessary to use uniqueness of this continuous functional calculus. -/
@[simps!]
/--
Definition of `cfcHomSuperset` / `cfcHomSuperset` 的定义

English:
definition cfcHomSuperset
  signature: {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq s)
  body: .comp ContinuousMap.compStarAlgHom' R R ⟨_, continuous_id.subtype_map hs⟩ cfcHom ha

中文:
定义 cfcHomSuperset
  签名: {a : A} (ha : p a) {s : 集合 R} (hs : spectrum R a subseteq s)
  定义体: .comp ContinuousMap.compStarAlgHom' R R ⟨_, continuous_id.subtype_map hs⟩ cfcHom ha

Depends on / 依赖: ContinuousMap, ContinuousMap.compStarAlgHom, cfcHom, compStarAlgHom, continuous_id, continuous_id.subtype_map, subtype_map
-/
noncomputable def cfcHomSuperset {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq s) :
    C(s, R) ->⋆ₐ[R] A :=
.comp ContinuousMap.compStarAlgHom' R R ⟨_, continuous_id.subtype_map hs⟩ cfcHom ha

/--
lemma `cfcHomSuperset_continuous` / 引理 `cfcHomSuperset_continuous`

English:
lemma cfcHomSuperset_continuous
  given: {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq s)
  proof: (cfcHom_continuous ha).comp ContinuousMap.continuous_precomp _

中文:
引理 cfcHomSuperset_continuous
  条件: {a : A} (ha : p a) {s : 集合 R} (hs : spectrum R a subseteq s)
  证明: (cfcHom_continuous ha).comp ContinuousMap.continuous_precomp _

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_precomp, cfcHom_continuous, continuous_precomp
-/
lemma cfcHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq s) :
    Continuous (cfcHomSuperset ha hs) :=
(cfcHom_continuous ha).comp ContinuousMap.continuous_precomp _

/--
lemma `cfcHomSuperset_id` / 引理 `cfcHomSuperset_id`

English:
lemma cfcHomSuperset_id
  given: {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq s)
  proof: cfcHom_id ha

中文:
引理 cfcHomSuperset_id
  条件: {a : A} (ha : p a) {s : 集合 R} (hs : spectrum R a subseteq s)
  证明: cfcHom_id ha

Depends on / 依赖: cfcHom_id
-/
lemma cfcHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq s) :
    cfcHomSuperset ha hs (.restrict s <| .id R) = a :=
  cfcHom_id ha

end Superset

section IsClosedEmbedding

/--
Definition of `ClosedEmbeddingContinuousFunctionalCalculus` / `ClosedEmbeddingContinuousFunctionalCalculus` 的定义

English:
class ClosedEmbeddingContinuousFunctionalCalculus
  parameters: (R A : Type*) (p : outParam (A -> Prop))
  axioms and operations (1):
    - isClosedEmbedding((a : A) (ha : p a)) : Topology.IsClosedEmbedding (cfcHom (R := R) ha)

中文:
类 ClosedEmbeddingContinuousFunctionalCalculus
  参数: (R A : 类型) (p : outParam (A -> 命题))
  公理与运算 (1 个):
    - isClosedEmbedding((a : A) (ha : p a)) : 拓扑.是闭嵌入 (cfcHom (R := R) ha)
-/
class ClosedEmbeddingContinuousFunctionalCalculus (R A : Type*) (p : outParam (A -> Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] extends
    ContinuousFunctionalCalculus R A p where
  isClosedEmbedding (a : A) (ha : p a) : Topology.IsClosedEmbedding (cfcHom (R := R) ha)

/--
lemma `cfcHom_isClosedEmbedding` / 引理 `cfcHom_isClosedEmbedding`

English:
lemma cfcHom_isClosedEmbedding
  statement: {R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R]
  proof: ClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

中文:
引理 cfcHom_isClosedEmbedding
  结论: {R A : 类型} {p : A -> 命题} [交换半环 R] [对合环 R]
  证明: ClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

Depends on / 依赖: ClosedEmbeddingContinuousFunctionalCalculus, ClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding, isClosedEmbedding
-/
lemma cfcHom_isClosedEmbedding {R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [instCFC : ClosedEmbeddingContinuousFunctionalCalculus R A p]
{a : A} (ha : p a) : IsClosedEmbedding (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A) :=
  ClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

end IsClosedEmbedding
