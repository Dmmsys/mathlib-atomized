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

/-- A star `R`-algebra `A` has a *continuous functional calculus* for elements satisfying the
property `p : A → Prop` if

+ for every such element `a : A` there is a star algebra homomorphism
  `cfcHom : C(spectrum R a, R) →⋆ₐ[R] A` sending the (restriction of) the identity map to `a`.
+ `cfcHom` is continuous and injective and the spectrum of the image of function `f` is its range.
+ `cfcHom` preserves the property `p`.
+ `p 0` is true, which ensures among other things that `p ≠ fun _ ↦ False`.

The property `p` is marked as an `outParam` so that the user need not specify it. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this approach
prevents diamonds or problems arising from multiple instances. -/
/-
**ContinuousFunctionalCalculus** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     outParam (A → Prop) →       [inst 
: CommSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSp
ace R] →             [IsTopologicalSemiring R] →               [ContinuousStar R
] → [inst_5 : Ring A] → [StarRing A] → [TopologicalSpace A] → [Algebra R A] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A star `R`-algebra `A` has a *continuous functional calculus* for elements satis
fying the
property `p : A → Prop` if

+ for every such element `a : A` there is a star algebra homomorphism
  `cfcHom : C(spectrum R a, R) →⋆ₐ[R] A` sending the (restriction of) the identi
ty map to `a`.
+ `cfcHom` is continuous and injective and the spectrum of the image of function
 `f` is its range.
+ `cfcHom` preserves the property `p`.
+ `p 0` is true, which ensures among other things that `p ≠ fun _ ↦ False`.

The property `p` is marked as an `outParam` so that the user need not specify it
. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all
 relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this ap
proach
prevents diamonds or problems arising from multiple instances.
-/
class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum R a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum R a).Nonempty
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(spectrum R a, R) →⋆ₐ[R] A,
    Continuous φ ∧ Function.Injective φ ∧ φ ((ContinuousMap.id R).restrict <| spectrum R a) = a ∧
      (∀ f, spectrum R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

-- this instance should not be activated everywhere but it is useful when developing generic API
-- for the continuous functional calculus
scoped[ContinuousFunctionalCalculus]
attribute [instance] ContinuousFunctionalCalculus.compactSpace_spectrum

/-- A class guaranteeing that the continuous functional calculus is uniquely determined by the
properties that it is a continuous star algebra homomorphism mapping the (restriction of) the
identity to `a`. This is the necessary tool used to establish `cfcHom_comp` and the more common
variant `cfc_comp`.

This class has instances, which can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean`, in each of the common
cases `ℂ`, `ℝ` and `ℝ≥0` as a consequence of the Stone-Weierstrass theorem.

This class is separate from `ContinuousFunctionalCalculus` primarily because we will later use
`SpectrumRestricts` to derive an instance of `ContinuousFunctionalCalculus` on a scalar subring
from one on a larger ring (i.e., to go from a continuous functional calculus over `ℂ` for normal
elements to one over `ℝ` for selfadjoint elements), and proving this additional property is
preserved would be burdensome or impossible. -/
/-
**ContinuousMap.UniqueHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousMap`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : CommSemiring R] →       [i
nst_1 : StarRing R] →         [inst_2 : MetricSpace R] →           [IsTopologica
lSemiring R] →             [ContinuousStar R] → [inst_5 : Ring A] → [StarRing A]
 → [TopologicalSpace A] → [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class guaranteeing that the continuous functional calculus is uniquely determi
ned by the
properties that it is a continuous star algebra homomorphism mapping the (restri
ction of) the
identity to `a`. This is the necessary tool used to establish `cfcHom_comp` and 
the more common
variant `cfc_comp`.

This class has instances, which can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean`, in eac
h of the common
cases `ℂ`, `ℝ` and `ℝ≥0` as a consequence of the Stone-Weierstrass theorem.

This class is separate from `ContinuousFunctionalCalculus` primarily because we 
will later use
`SpectrumRestricts` to derive an instance of `ContinuousFunctionalCalculus` on a
 scalar subring
from one on a larger ring (i.e., to go from a continuous functional calculus ove
r `ℂ` for normal
elements to one over `ℝ` for selfadjoint elements), and proving this additional 
property is
preserved would be burdensome or impossible.
-/
class ContinuousMap.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s]
    (φ ψ : C(s, R) →⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R)) :
    φ = ψ

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

include instCFC in
/-
**ContinuousFunctionalCalculus.isCompact_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousFunctionalCalculus.isCompact_spectrum (a : A) : IsCompact (spect
rum R a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
-/
lemma ContinuousFunctionalCalculus.isCompact_spectrum (a : A) :
    IsCompact (spectrum R a) :=
  isCompact_iff_compactSpace.mpr inferInstance
/-
**StarAlgHom.ext_continuousMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StarAlgHom.ext_continuousMap [UniqueHom R A] (a : A) [CompactSpace (spectr
um R a)] (φ ψ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuo
us ψ) (h : φ (.restrict (spectrum R a) <| .id R) = ψ (.restrict (spectrum R a) <
| .id R)) : φ = ψ
参数：a : A；spectrum R a；φ ψ : C(spectrum R a, R) ->⋆ₐ[R] A；hφ : Continuous φ；hψ : 
Continuous ψ；h : φ (.restrict (spectrum R a) <| .id R) = ψ (.restrict (spectrum 
R a) <| .id R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.UniqueHom.eq_of_continuous_of_map_id`：∀ {R : Type u_1} {A 
: Type u_2} {inst : CommSemiring R} {inst_1 : StarRing R} {inst_2 : MetricSpace 
R}   {inst_3 : IsTopologicalSemiring R} …
-/
lemma StarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (spectrum R a)] (φ ψ : C(spectrum R a, R) →⋆ₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict (spectrum R a) <| .id R) = ψ (.restrict (spectrum R a) <| .id R)) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id (spectrum R a) φ ψ hφ hψ h

section cfcHom

variable {a : A} (ha : p a)

-- Note: since `spectrum R a` is closed, we may always extend `f : C(spectrum R a, R)` to a function
-- of type `C(R, R)` by the Tietze extension theorem (assuming `R` is either `ℝ`, `ℂ` or `ℝ≥0`).

/-- The star algebra homomorphism underlying an instance of the continuous functional calculus;
a version for continuous functions on the spectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`, for otherwise it
may be the case that no star algebra homomorphism exists. For instance if `R := ℝ` and `a` is an
element whose spectrum (in `ℂ`) is disjoint from `ℝ`, then `spectrum ℝ a = ∅` and so there can be
no star algebra homomorphism between these spaces.

While `ContinuousFunctionalCalculus` is stated in terms of these homomorphisms, in practice the
user should instead prefer `cfc` over `cfcHom`.
-/
/-
**cfcHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cfcHom : C(spectrum R a, R) ->⋆ₐ[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousFunctionalCalculus.exists_cfc_of_predicate`：∀ {R : Type u_1} {
A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRi
ng R}   {inst_2 : MetricSpace R} {inst_3 :…

--- 原说明 ---
The star algebra homomorphism underlying an instance of the continuous functiona
l calculus;
a version for continuous functions on the spectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`
, for otherwise it
may be the case that no star algebra homomorphism exists. For instance if `R := 
ℝ` and `a` is an
element whose spectrum (in `ℂ`) is disjoint from `ℝ`, then `spectrum ℝ a = ∅` an
d so there can be
no star algebra homomorphism between these spaces.

While `ContinuousFunctionalCalculus` is stated in terms of these homomorphisms, 
in practice the
user should instead prefer `cfc` over `cfcHom`.
-/
noncomputable def cfcHom : C(spectrum R a, R) →⋆ₐ[R] A :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]
/-
**cfcHom_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_continuous : Continuous (cfcHom ha : C(spectrum R a, R) ->⋆ₐ[R] A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousFunctionalCalculus.exists_cfc_of_predicate`：∀ {R : Type u_1} {
A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRi
ng R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma cfcHom_continuous : Continuous (cfcHom ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1
/-
**cfcHom_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_injective : Function.Injective (cfcHom ha : C(spectrum R a, R) ->⋆ₐ
[R] A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousFunctionalCalculus.exists_cfc_of_predicate`：∀ {R : Type u_1} {
A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRi
ng R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma cfcHom_injective : Function.Injective (cfcHom ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1
/-
**cfcHom_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousFunctionalCalculus.exists_cfc_of_predicate`：∀ {R : Type u_1} {
A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRi
ng R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma cfcHom_id :
    cfcHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
/-
**cfcHom_map_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_map_spectrum (f : C(spectrum R a, R)) : spectrum R (cfcHom ha f) = 
Set.range f
参数：f : C(spectrum R a, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousFunctionalCalculus.exists_cfc_of_predicate`：∀ {R : Type u_1} {
A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRi
ng R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
The **spectral mapping theorem** for the continuous functional calculus.
-/
lemma cfcHom_map_spectrum (f : C(spectrum R a, R)) :
    spectrum R (cfcHom ha f) = Set.range f :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f
/-
**cfcHom_predicate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_predicate (f : C(spectrum R a, R)) : p (cfcHom ha f)
参数：f : C(spectrum R a, R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousFunctionalCalculus.exists_cfc_of_predicate`：∀ {R : Type u_1} {
A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRi
ng R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma cfcHom_predicate (f : C(spectrum R a, R)) :
    p (cfcHom ha f) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

open scoped ContinuousFunctionalCalculus in
/-
**cfcHom_eq_of_continuous_of_map_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_eq_of_continuous_of_map_id [UniqueHom R A] (φ : C(spectrum R a, R) 
->⋆ₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.restrict (spectrum R a) <| .id R) = a
) : cfcHom ha = φ
参数：φ : C(spectrum R a, R) ->⋆ₐ[R] A；hφ₁ : Continuous φ；hφ₂ : φ (.restrict (spect
rum R a) <| .id R) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StarAlgHom.ext_continuousMap`：StarAlgHom.ext_continuousMap [UniqueHom R 
A] (a : A) [CompactSpace (spectrum R a)] (φ ψ : C(spectrum R a, R) ->⋆ₐ[R] A) (h
φ : Continuous φ) …
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
-/
lemma cfcHom_eq_of_continuous_of_map_id [UniqueHom R A]
    (φ : C(spectrum R a, R) →⋆ₐ[R] A) (hφ₁ : Continuous φ)
    (hφ₂ : φ (.restrict (spectrum R a) <| .id R) = a) : cfcHom ha = φ :=
  (cfcHom ha).ext_continuousMap a φ (cfcHom_continuous ha) hφ₁ <| by
    rw [cfcHom_id ha, hφ₂]
/-
**cfcHom_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cfcHom_comp [UniqueHom R A] (f : C(spectrum R a, R)) (f' : C(spectrum R a,
 spectrum R (cfcHom ha f))) (hff' : forall x, f x = f' x) (g : C(spectrum R (cfc
Hom ha f), R)) : cfcHom ha (g.comp f') = cfcHom (cfcHom_predicate ha f) g
参数：f : C(spectrum R a, R)；f' : C(spectrum R a, spectrum R (cfcHom ha f))；hff' : 
forall x, f x = f' x；g : C(spectrum R (cfcHom ha f), R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfcHom_predicate`：cfcHom_predicate (f : C(spectrum R a, R)) : p (cfcHom 
ha f)
· 使用引理 `cfcHom_eq_of_continuous_of_map_id`：cfcHom_eq_of_continuous_of_map_id [Un
iqueHom R A] (φ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.
restrict (spectrum R a)…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.compStarAlgHom'_apply`：∀ {X : Type u_1} {Y : Type u_2} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (𝕜 : Type u_4)   [inst_2 
: CommSemiring 𝕜] (A : Ty…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cfcHom_comp [UniqueHom R A] (f : C(spectrum R a, R))
    (f' : C(spectrum R a, spectrum R (cfcHom ha f)))
    (hff' : ∀ x, f x = f' x) (g : C(spectrum R (cfcHom ha f), R)) :
    cfcHom ha (g.comp f') = cfcHom (cfcHom_predicate ha f) g := by
  let φ : C(spectrum R (cfcHom ha f), R) →⋆ₐ[R] A :=
    (cfcHom ha).comp <| ContinuousMap.compStarAlgHom' R R f'
  suffices cfcHom (cfcHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcHom_eq_of_continuous_of_map_id (cfcHom_predicate ha f) φ ?_ ?_
  · exact cfcHom_continuous ha |>.comp f'.continuous_precomp
  · simp only [φ, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
    congr
    ext x
    simp [hff']

end cfcHom

section cfcL

/-- `cfcHom` bundled as a continuous linear map. -/
@[simps apply]
/-
**cfcL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cfcL {a : A} (ha : p a) : C(spectrum R a, R) ->L[R] A
参数：ha : p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cfcHom` bundled as a continuous linear map.
-/
noncomputable def cfcL {a : A} (ha : p a) : C(spectrum R a, R) →L[R] A :=
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
noncomputable irreducible_def cfc (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcHom h.1 ⟨_, h.2.domRestrict⟩
    else 0

variable (f g : R → R) (a : A) (ha : p a := by cfc_tac)
variable (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
variable (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)

set_option backward.privateInPublic true in
/-
**cfc_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_apply : cfc f a = cfcHom (a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_def`：∀ {R : Type u_3} {A : Type u_4} {p : A → Prop} [inst : CommSemi
ring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma cfc_apply : cfc f a = cfcHom (a := a) ha ⟨_, hf.domRestrict⟩ := by
  rw [cfc_def, dif_pos ⟨ha, hf⟩]
/-
**cfc_apply_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_apply_pi {ι : Type*} (f : ι -> R -> R) (a : A) (ha : p a
参数：f : ι -> R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_apply_pi {ι : Type*} (f : ι → R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ∀ i, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    (fun i => cfc (f i) a) = (fun i => cfcHom (a := a) ha ⟨_, (hf i).domRestrict⟩) := by
  ext i
  simp only [cfc_apply (f i) a ha (hf i)]
/-
**cfc_apply_of_not_and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_apply_of_not_and {f : R -> R} (a : A) (ha : ¬ (p a ∧ ContinuousOn f (s
pectrum R a))) : cfc f a = 0
参数：a : A；ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_def`：∀ {R : Type u_3} {A : Type u_4} {p : A → Prop} [inst : CommSemi
ring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma cfc_apply_of_not_and {f : R → R} (a : A) (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))) :
    cfc f a = 0 := by
  rw [cfc_def, dif_neg ha]
/-
**cfc_apply_of_not_predicate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_apply_of_not_predicate {f : R -> R} (a : A) (ha : ¬ p a) : cfc f a = 0
参数：a : A；ha : ¬ p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_def`：∀ {R : Type u_3} {A : Type u_4} {p : A → Prop} [inst : CommSemi
ring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
lemma cfc_apply_of_not_predicate {f : R → R} (a : A) (ha : ¬ p a) :
    cfc f a = 0 := by
  rw [cfc_def, dif_neg (not_and_of_not_left _ ha)]
/-
**cfc_apply_of_not_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_apply_of_not_continuousOn {f : R -> R} (a : A) (hf : ¬ ContinuousOn f 
(spectrum R a)) : cfc f a = 0
参数：a : A；hf : ¬ ContinuousOn f (spectrum R a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_def`：∀ {R : Type u_3} {A : Type u_4} {p : A → Prop} [inst : CommSemi
ring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_and_of_not_right`：∀ (a : Prop) {b : Prop}, ¬b → ¬(a ∧ b)
-/
lemma cfc_apply_of_not_continuousOn {f : R → R} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) :
    cfc f a = 0 := by
  rw [cfc_def, dif_neg (not_and_of_not_right _ hf)]
/-
**cfcHom_eq_cfc_extend** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_eq_cfc_extend {a : A} (g : R -> R) (ha : p a) (f : C(spectrum R a, 
R)) : cfcHom ha f = cfc (Function.extend Subtype.val f g) a
参数：g : R -> R；ha : p a；f : C(spectrum R a, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
lemma cfcHom_eq_cfc_extend {a : A} (g : R → R) (ha : p a) (f : C(spectrum R a, R)) :
    cfcHom ha f = cfc (Function.extend Subtype.val f g) a := by
  have h : f = (spectrum R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (spectrum R a) :=
    continuousOn_iff_continuous_domRestrict.mpr <| h ▸ map_continuous f
  rw [cfc_apply ..]
  congr!
/-
**cfc_eq_cfcL** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_eq_cfcL {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (spectrum
 R a)) : cfc f a = cfcL ha ⟨_, hf.domRestrict⟩
参数：ha : p a；hf : ContinuousOn f (spectrum R a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_def`：∀ {R : Type u_3} {A : Type u_4} {p : A → Prop} [inst : CommSemi
ring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `cfcL_apply`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : CommS
emiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi
…
-/
lemma cfc_eq_cfcL {a : A} {f : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    cfc f a = cfcL ha ⟨_, hf.domRestrict⟩ := by
  rw [cfc_def, dif_pos ⟨ha, hf⟩, cfcL_apply]

set_option backward.privateInPublic true in
/-- A version of `cfc_apply` in terms of `ContinuousMap.mkD` -/
/-
**cfc_apply_mkD** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_apply_mkD : cfc f a = cfcHom (a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `ContinuousMap.mkD_of_continuousOn`：mkD_of_continuousOn {s : Set α} {f : 
α -> β} {g : C(s, β)} (hf : ContinuousOn f s) : mkD (s.domRestrict f) g = ⟨s.dom
Restrict f, hf.domRestr…
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
· 使用引理 `ContinuousMap.mkD_of_not_continuousOn`：mkD_of_not_continuousOn {s : Set 
α} {f : α -> β} {g : C(s, β)} (hf : ¬ ContinuousOn f s) : mkD (s.domRestrict f) 
g = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…

--- 原说明 ---
A version of `cfc_apply` in terms of `ContinuousMap.mkD`
-/
lemma cfc_apply_mkD :
    cfc f a = cfcHom (a := a) ha (mkD ((spectrum R a).domRestrict f) 0) := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a, mkD_of_continuousOn hf]
  · rw [cfc_apply_of_not_continuousOn a hf, mkD_of_not_continuousOn hf,
      map_zero]

set_option backward.privateInPublic true in
/-- A version of `cfc_eq_cfcL` in terms of `ContinuousMapZero.mkD` -/
/-
**cfc_eq_cfcL_mkD** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_eq_cfcL_mkD : cfc f a = cfcL (a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_apply_mkD`：cfc_apply_mkD : cfc f a = cfcHom (a

--- 原说明 ---
A version of `cfc_eq_cfcL` in terms of `ContinuousMapZero.mkD`
-/
lemma cfc_eq_cfcL_mkD :
    cfc f a = cfcL (a := a) ha (mkD ((spectrum R a).domRestrict f) 0) :=
  cfc_apply_mkD _ _
/-
**cfc_cases** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (haf : (hf : Con
tinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.domRestrict⟩)) 
: P (cfc f a)
参数：P : A -> Prop；a : A；f : R -> R；h₀ : P 0；haf : (hf : ContinuousOn f (spectrum 
R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.domRestrict⟩)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
-/
lemma cfc_cases (P : A → Prop) (a : A) (f : R → R) (h₀ : P 0)
    (haf : (hf : ContinuousOn f (spectrum R a)) → (ha : p a) → P (cfcHom ha ⟨_, hf.domRestrict⟩)) :
    P (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a h.1 h.2]
    exact haf h.2 h.1
  · simp only [not_and_or] at h
    obtain (h | h) := h
    · rwa [cfc_apply_of_not_predicate _ h]
    · rwa [cfc_apply_of_not_continuousOn _ h]
/-
**cfc_commute_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_commute_cfc (f g : R -> R) (a : A) : Commute (cfc f a) (cfc g a)
参数：f g : R -> R；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma cfc_commute_cfc (f g : R → R) (a : A) : Commute (cfc f a) (cfc g a) := by
  refine cfc_cases (fun x ↦ Commute x (cfc g a)) a f (by simp) fun hf ha ↦ ?_
  refine cfc_cases (fun x ↦ Commute _ x) a g (by simp) fun hg _ ↦ ?_
  exact Commute.all _ _ |>.map _

variable (R) in
/-
**cfc_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_id (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
-/
lemma cfc_id (ha : p a := by cfc_tac) : cfc (id : R → R) a = a :=
  cfc_apply (id : R → R) a ▸ cfcHom_id (p := p) ha

variable (R) in
/-
**cfc_id'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_id' (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_id`：cfc_id (ha : p a
-/
lemma cfc_id' (ha : p a := by cfc_tac) : cfc (fun x : R ↦ x) a = a := cfc_id R a

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
/-
**cfc_map_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_map_spectrum (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_map_spectrum`：cfcHom_map_spectrum (f : C(spectrum R a, R)) : spec
trum R (cfcHom ha f) = Set.range f
· 使用定理 `Set.range_domRestrict`：range_domRestrict (f : α -> β) (s : Set α) : Set.
range (s.domRestrict f) = f '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **spectral mapping theorem** for the continuous functional calculus.
-/
lemma cfc_map_spectrum (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    spectrum R (cfc f a) = f '' spectrum R a := by
  simp [cfc_apply f a, cfcHom_map_spectrum (p := p)]
/-
**cfc_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_const (r : R) (a : A) (ha : p a
参数：r : R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
-/
lemma cfc_const (r : R) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ ↦ r) a = algebraMap R A r := by
  rw [cfc_apply (fun _ : R ↦ r) a, ← AlgHomClass.commutes (cfcHom ha (p := p)) r]
  congr

variable (R) in
include R in
/-
**cfc_predicate_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_predicate_zero : p 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousFunctionalCalculus.predicate_zero`：∀ (R : Type u_1) {A : Type 
u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R}   {
inst_2 : MetricSpace R} {inst_3 :…
-/
lemma cfc_predicate_zero : p 0 :=
  ContinuousFunctionalCalculus.predicate_zero (R := R)
/-
**cfc_predicate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
参数：f : R -> R；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用引理 `cfc_predicate_zero`：cfc_predicate_zero : p 0
· 使用引理 `cfcHom_predicate`：cfcHom_predicate (f : C(spectrum R a, R)) : p (cfcHom 
ha f)
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
-/
lemma cfc_predicate (f : R → R) (a : A) : p (cfc f a) :=
  cfc_cases p a f (cfc_predicate_zero R) fun _ _ ↦ cfcHom_predicate ..
/-
**cfc_predicate_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_predicate_algebraMap (r : R) : p (algebraMap R A r)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_predicate`：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用引理 `cfc_predicate_zero`：cfc_predicate_zero : p 0
-/
lemma cfc_predicate_algebraMap (r : R) : p (algebraMap R A r) :=
  cfc_const r (0 : A) (cfc_predicate_zero R) ▸ cfc_predicate (fun _ ↦ r) 0

variable (R) in
include R in
/-
**cfc_predicate_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_predicate_one : p 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_predicate_algebraMap`：cfc_predicate_algebraMap (r : R) : p (algebraM
ap R A r)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma cfc_predicate_one : p 1 :=
  map_one (algebraMap R A) ▸ cfc_predicate_algebraMap (1 : R)
/-
**cfc_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f g) : cfc f a
 = cfc g a
参数：hfg : (spectrum R a).EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.domRestrict_eq_iff`：domRestrict_eq_iff {f : forall a, π a} {s : Set 
α} {g : forall a : s, π a} : domRestrict s f = g ↔ forall (a) (ha : a in s), f a
 = g ⟨a, ha⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
lemma cfc_congr {f g : R → R} {a : A} (hfg : (spectrum R a).EqOn f g) :
    cfc f a = cfc g a := by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfc_apply (ha := h.1) (hf := h.2.congr hfg), cfc_apply (ha := h.1) (hf := h.2)]
    congr 2
    exact Set.domRestrict_eq_iff.mpr hfg
  · obtain (ha | hg) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hg, cfc_apply_of_not_continuousOn]
      exact fun hf ↦ hg (hf.congr hfg.symm)
/-
**eqOn_of_cfc_eq_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eqOn_of_cfc_eq_cfc {f g : R -> R} {a : A} (h : cfc f a = cfc g a) (hf : Co
ntinuousOn f (spectrum R a)
参数：h : cfc f a = cfc g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用引理 `cfcHom_injective`：cfcHom_injective : Function.Injective (cfcHom ha : C(s
pectrum R a, R) ->⋆ₐ[R] A)
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
-/
lemma eqOn_of_cfc_eq_cfc {f g : R → R} {a : A} (h : cfc f a = cfc g a)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (spectrum R a).EqOn f g := by
  rw [cfc_apply f a, cfc_apply g a] at h
  exact fun x hx ↦ congr($(cfcHom_injective ha h) ⟨x, hx⟩)

set_option backward.privateInPublic true in
variable {a f g} in
include ha hf hg in
/-
**cfc_eq_cfc_iff_eqOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_eq_cfc_iff_eqOn : cfc f a = cfc g a ↔ (spectrum R a).EqOn f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eqOn_of_cfc_eq_cfc`：eqOn_of_cfc_eq_cfc {f g : R -> R} {a : A} (h : cfc f
 a = cfc g a) (hf : ContinuousOn f (spectrum R a)
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
-/
lemma cfc_eq_cfc_iff_eqOn : cfc f a = cfc g a ↔ (spectrum R a).EqOn f g :=
  ⟨eqOn_of_cfc_eq_cfc, cfc_congr⟩

variable (R)

set_option backward.privateInPublic true in
include ha in
/-
**cfc_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_one : cfc (1 : R -> R) a = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_one`：continuous_one [TopologicalSpace M] [One M] : Continuous
 (1 : X -> M)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
-/
lemma cfc_one : cfc (1 : R → R) a = 1 :=
  cfc_apply (1 : R → R) a ▸ map_one (cfcHom (show p a from ha))

set_option backward.privateInPublic true in
include ha in
/-
**cfc_const_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_const_one : cfc (fun _ : R => 1) a = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_one`：cfc_one : cfc (1 : R -> R) a = 1
-/
lemma cfc_const_one : cfc (fun _ : R ↦ 1) a = 1 := cfc_one R a

@[simp]
/-
**cfc_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_zero : cfc (0 : R -> R) a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
-/
lemma cfc_zero : cfc (0 : R → R) a = 0 := by
  by_cases ha : p a
  · exact cfc_apply (0 : R → R) a ▸ map_zero (cfcHom ha)
  · rw [cfc_apply_of_not_predicate a ha]

@[simp]
/-
**cfc_const_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_const_zero : cfc (fun _ : R => 0) a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_zero`：cfc_zero : cfc (0 : R -> R) a = 0
-/
lemma cfc_const_zero : cfc (fun _ : R ↦ 0) a = 0 :=
  cfc_zero R a

variable {R}
/-
**cfc_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_mul (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f g : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `ContinuousOn.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_mul (f g : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_mul, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]
/-
**cfc_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；n : Nat；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
-/
lemma cfc_pow (f : R → R) (n : ℕ) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ (f x) ^ n) a = cfc f a ^ n := by
  rw [cfc_apply f a, ← map_pow, cfc_apply _ a]
  congr
/-
**cfc_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_add (f g : R -> R) (hf : ContinuousOn f (spectrum R a)
参数：f g : R -> R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `ContinuousOn.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_add (f g : R → R) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x + g x) a = cfc f a + cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_add, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]
/-
**cfc_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_const_add (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum 
R a)
参数：r : R；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_add`：cfc_add (f g : R -> R) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
-/
lemma cfc_const_add (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => r + f x) a = algebraMap R A r + cfc f a := by
  have : (fun z => r + f z) = (fun z => (fun _ => r) z + f z) := by ext; simp
  rw [this, cfc_add a _ _ (continuousOn_const (c := r)) hf, cfc_const r a ha]
/-
**cfc_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_add_const (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum 
R a)
参数：r : R；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `cfc_const_add`：cfc_const_add (r : R) (f : R -> R) (a : A) (hf : Continuo
usOn f (spectrum R a)
-/
lemma cfc_add_const (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => f x + r) a = cfc f a + algebraMap R A r := by
  rw [add_comm (cfc f a)]
  conv_lhs => simp only [add_comm]
  exact cfc_const_add r f a hf ha

open Finset in
/-
**cfc_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_sum {ι : Type*} (f : ι -> R -> R) (a : A) (s : Finset ι) (hf : forall 
i in s, ContinuousOn (f i) (spectrum R a)
参数：f : ι -> R -> R；a : A；s : Finset ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `continuousOn_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMono
id M] [Conti…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用引理 `cfc_apply_pi`：cfc_apply_pi {ι : Type*} (f : ι -> R -> R) (a : A) (ha : p
 a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.coe_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommMonoid β]   [inst_3 : 
ContinuousA…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
lemma cfc_sum {ι : Type*} (f : ι → R → R) (a : A) (s : Finset ι)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    cfc (∑ i ∈ s, f i) a = ∑ i ∈ s, cfc (f i) a := by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i ∈ s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (spectrum R a) := by
      rw [sum_coe_sort s, hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s, ← sum_coe_sort s]
    rw [cfc_apply_pi _ a ha (fun ⟨i, hi⟩ => hf i hi), ← map_sum, cfc_apply _ a ha hf']
    congr 1
    ext
    simp
  · simp [cfc_apply_of_not_predicate a ha]

open Finset in
/-
**cfc_sum_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_sum_univ {ι : Type*} [Fintype ι] (f : ι -> R -> R) (a : A) (hf : foral
l i, ContinuousOn (f i) (spectrum R a)
参数：f : ι -> R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_sum`：cfc_sum {ι : Type*} (f : ι -> R -> R) (a : A) (s : Finset ι) (h
f : forall i in s, ContinuousOn (f i) (spectrum R a)
-/
lemma cfc_sum_univ {ι : Type*} [Fintype ι] (f : ι → R → R) (a : A)
    (hf : ∀ i, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    cfc (∑ i, f i) a = ∑ i, cfc (f i) a :=
  cfc_sum f a _ fun i _ ↦ hf i
/-
**cfc_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroClass S
 A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (f : R -> R) (a :
 A) (hf : ContinuousOn f (spectrum R a)
参数：R -> R；s : S；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousOn.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   
[inst_3 : Topolog…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ s • f x) a = s • cfc f a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfc_apply_of_not_predicate a ha]
/-
**cfc_const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_const_mul (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum 
R a)
参数：r : R；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_smul`：cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMu
lZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (f …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma cfc_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ r * f x) a = r • cfc f a :=
  cfc_smul r f a
/-
**cfc_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_star (f : R -> R) (a : A) : cfc (fun x => star (f x)) a = star (cfc f 
a)
参数：f : R -> R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `ContinuousOn.star`：ContinuousOn.star (hf : ContinuousOn f s) : Continuou
sOn (fun x => star (f x)) s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
lemma cfc_star (f : R → R) (a : A) : cfc (fun x ↦ star (f x)) a = star (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a, ← map_star, cfc_apply _ a]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_continuousOn, star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star
/-
**cfc_pow_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_pow_id (a : A) (n : Nat) (ha : p a
参数：a : A；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_pow`：cfc_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f (sp
ectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
-/
lemma cfc_pow_id (a : A) (n : ℕ) (ha : p a := by cfc_tac) : cfc (· ^ n : R → R) a = a ^ n := by
  rw [cfc_pow .., cfc_id' ..]
/-
**cfc_smul_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroClas
s S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (a : A) (ha : 
p a
参数：R -> R；s : S；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_smul`：cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMu
lZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (f …
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
-/
lemma cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfc (s • · : R → R) a = s • a := by
  rw [cfc_smul .., cfc_id' ..]
/-
**cfc_const_mul_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_const_mul_id (r : R) (a : A) (ha : p a
参数：r : R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_smul_id`：cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R
] [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S)
 …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma cfc_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfc (r * ·) a = r • a :=
  cfc_smul_id r a

set_option backward.privateInPublic true in
include ha in
/-
**cfc_star_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_star_id : cfc (star · : R -> R) a = star a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_star`：cfc_star (f : R -> R) (a : A) : cfc (fun x => star (f x)) a = 
star (cfc f a)
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
-/
lemma cfc_star_id : cfc (star · : R → R) a = star a := by
  rw [cfc_star .., cfc_id' ..]

variable (R) in
/-
**range_cfc_eq_range_cfcHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_cfc_eq_range_cfcHom [StarModule R A] {a : A} (ha : p a) : Set.range 
(cfc (R
参数：ha : p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcHom_eq_cfc_extend`：cfcHom_eq_cfc_extend {a : A} (g : R -> R) (ha : p 
a) (f : C(spectrum R a, R)) : cfcHom ha f = cfc (Function.extend Subtype.val f g
) a
-/
theorem range_cfc_eq_range_cfcHom [StarModule R A] {a : A} (ha : p a) :
    Set.range (cfc (R := R) · a) = (cfcHom ha (R := R)).range := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfc_cases _ a f (zero_mem _) fun hf ha ↦ ⟨_, rfl⟩
  · exact ⟨Subtype.val.extend f 0, cfcHom_eq_cfc_extend _ ha _ |>.symm⟩

section Polynomial
open Polynomial

/-
**cfc_eval_X** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_eval_X (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用引理 `cfc_id`：cfc_id (ha : p a
-/
lemma cfc_eval_X (ha : p a := by cfc_tac) : cfc (X : R[X]).eval a = a := by
  simpa using! cfc_id R a
/-
**cfc_eval_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_eval_C (r : R) (a : A) (ha : p a
参数：r : R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_eval_C (r : R) (a : A) (ha : p a := by cfc_tac) :
    cfc (C r).eval a = algebraMap R A r := by
  simp [cfc_const r a]
/-
**cfc_map_polynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_map_polynomial (q : R[X]) (f : R -> R) (a : A) (ha : p a
参数：q : R[X]；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用引理 `cfc_add`：cfc_add (f g : R -> R) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
（共 37 条，此处仅展示前 30 条）
-/
lemma cfc_map_polynomial (q : R[X]) (f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ q.eval (f x)) a = aeval (cfc f a) q := by
  induction q using Polynomial.induction_on with
  | C r => simp [cfc_const r a]
  | add q₁ q₂ hq₁ hq₂ =>
    simp only [eval_add, map_add, ← hq₁, ← hq₂, cfc_add a (q₁.eval <| f ·) (q₂.eval <| f ·)]
  | monomial n r _ =>
    simp only [eval_mul, eval_C, eval_X_pow, map_mul, aeval_C, map_pow, aeval_X]
    rw [cfc_const_mul .., cfc_pow _ (n + 1) _, ← smul_eq_mul, algebraMap_smul]
/-
**cfc_polynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_polynomial (q : R[X]) (a : A) (ha : p a
参数：q : R[X]；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_map_polynomial`：cfc_map_polynomial (q : R[X]) (f : R -> R) (a : A) (
ha : p a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
-/
lemma cfc_polynomial (q : R[X]) (a : A) (ha : p a := by cfc_tac) :
    cfc q.eval a = aeval a q := by
  rw [cfc_map_polynomial .., cfc_id' ..]

end Polynomial

section Comp

variable [UniqueHom R A]

/-
**cfc_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp (g f : R -> R) (a : A) (ha : p a
参数：g f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcHom_map_spectrum`：cfcHom_map_spectrum (f : C(spectrum R a, R)) : spec
trum R (cfcHom ha f) = Set.range f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_domRestrict`：range_domRestrict (f : α -> β) (s : Set α) : Set.
range (s.domRestrict f) = f '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_predicate`：cfcHom_predicate (f : C(spectrum R a, R)) : p (cfcHom 
ha f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `cfcHom_comp`：cfcHom_comp [UniqueHom R A] (f : C(spectrum R a, R)) (f' : 
C(spectrum R a, spectrum R (cfcHom ha f))) (hff' : forall x, f x = f' x) (g : C(
s…
-/
lemma cfc_comp (g f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (g ∘ f) a = cfc g (cfc f a) := by
  have := hg.comp hf <| (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcHom (show p a from ha) (ContinuousMap.mk _ hf.domRestrict)) =
      f '' (spectrum R a) := by
    rw [cfcHom_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply .., cfc_apply f a,
    cfc_apply _ _ (cfcHom_predicate (show p a from ha) _) (by convert! hg), ← cfcHom_comp _ _]
  swap
  · exact ContinuousMap.mk _ <| hf.domRestrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp
  · congr
  · exact fun _ ↦ rfl
/-
**cfc_comp'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' spectrum R a)
参数：g f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_comp`：cfc_comp (g f : R -> R) (a : A) (ha : p a
-/
lemma cfc_comp' (g f : R → R) (a : A) (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (g <| f ·) a = cfc g (cfc f a) :=
  cfc_comp g f a
/-
**cfc_comp_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f ((· ^ n) 
'' (spectrum R a))
参数：f : R -> R；n : Nat；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
-/
lemma cfc_comp_pow (f : R → R) (n : ℕ) (a : A)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| · ^ n) a = cfc f (a ^ n) := by
  rw [cfc_comp' .., cfc_pow_id ..]
/-
**cfc_comp_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroCl
ass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (f : R -> R)
 (a : A) (hf : ContinuousOn f ((s • ·) '' (spectrum R a))
参数：R -> R；s : S；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `ContinuousOn.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   
[inst_3 : Topolog…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_smul_id`：cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R
] [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S)
 …
-/
lemma cfc_comp_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroClass S A]
    [IsScalarTower S R A] [IsScalarTower S R (R → R)] (s : S) (f : R → R) (a : A)
    (hf : ContinuousOn f ((s • ·) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| s • ·) a = cfc f (s • a) := by
  rw [cfc_comp' .., cfc_smul_id ..]
/-
**cfc_comp_const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_const_mul (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f ((r *
 ·) '' (spectrum R a))
参数：r : R；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `ContinuousOn.const_mul`：ContinuousOn.const_mul (hf : ContinuousOn f s) (
b : M) : ContinuousOn (b * f ·) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_const_mul_id`：cfc_const_mul_id (r : R) (a : A) (ha : p a
-/
lemma cfc_comp_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| r * ·) a = cfc f (r • a) := by
  rw [cfc_comp' .., cfc_const_mul_id ..]
/-
**cfc_comp_star** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_star (f : R -> R) (a : A) (hf : ContinuousOn f (star '' (spectrum
 R a))
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `ContinuousOn.star`：ContinuousOn.star (hf : ContinuousOn f s) : Continuou
sOn (fun x => star (f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_star_id`：cfc_star_id : cfc (star · : R -> R) a = star a
-/
lemma cfc_comp_star (f : R → R) (a : A)
    (hf : ContinuousOn f (star '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| star ·) a = cfc f (star a) := by
  rw [cfc_comp' .., cfc_star_id ..]

open Polynomial in
/-
**cfc_comp_polynomial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_polynomial (q : R[X]) (f : R -> R) (a : A) (hf : ContinuousOn f (
q.eval '' (spectrum R a))
参数：q : R[X]；f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `Polynomial.continuousOn`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : 
TopologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R)   {s : Set R}, 
ContinuousOn …
· 使用引理 `cfc_polynomial`：cfc_polynomial (q : R[X]) (a : A) (ha : p a
-/
lemma cfc_comp_polynomial (q : R[X]) (f : R → R) (a : A)
    (hf : ContinuousOn f (q.eval '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| q.eval ·) a = cfc f (aeval a q) := by
  rw [cfc_comp' .., cfc_polynomial ..]

end Comp

/-
**CFC.eq_algebraMap_of_spectrum_subset_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.eq_algebraMap_of_spectrum_subset_singleton (r : R) (h_spec : spectrum 
R a subseteq {r}) (ha : p a
参数：r : R；h_spec : spectrum R a subseteq {r}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
-/
lemma CFC.eq_algebraMap_of_spectrum_subset_singleton (r : R) (h_spec : spectrum R a ⊆ {r})
    (ha : p a := by cfc_tac) : a = algebraMap R A r := by
  simpa [cfc_id R a, cfc_const r a] using
    cfc_congr (f := id) (g := fun _ : R ↦ r) (a := a) fun x hx ↦ by simpa using h_spec hx
/-
**CFC.eq_zero_of_spectrum_subset_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.eq_zero_of_spectrum_subset_zero (h_spec : spectrum R a subseteq {0}) (
ha : p a
参数：h_spec : spectrum R a subseteq {0}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `CFC.eq_algebraMap_of_spectrum_subset_singleton`：CFC.eq_algebraMap_of_spe
ctrum_subset_singleton (r : R) (h_spec : spectrum R a subseteq {r}) (ha : p a
-/
lemma CFC.eq_zero_of_spectrum_subset_zero (h_spec : spectrum R a ⊆ {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 0 h_spec
/-
**CFC.eq_one_of_spectrum_subset_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.eq_one_of_spectrum_subset_one (h_spec : spectrum R a subseteq {1}) (ha
 : p a
参数：h_spec : spectrum R a subseteq {1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `CFC.eq_algebraMap_of_spectrum_subset_singleton`：CFC.eq_algebraMap_of_spe
ctrum_subset_singleton (r : R) (h_spec : spectrum R a subseteq {r}) (ha : p a
-/
lemma CFC.eq_one_of_spectrum_subset_one (h_spec : spectrum R a ⊆ {1}) (ha : p a := by cfc_tac) :
    a = 1 := by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 1 h_spec

include instCFC in
/-
**CFC.spectrum_algebraMap_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.spectrum_algebraMap_subset (r : R) : spectrum R (algebraMap R A r) sub
seteq {r}
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用引理 `cfc_predicate_zero`：cfc_predicate_zero : p 0
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CFC.spectrum_algebraMap_subset (r : R) : spectrum R (algebraMap R A r) ⊆ {r} := by
  rw [← cfc_const r 0 (cfc_predicate_zero R),
    cfc_map_spectrum (fun _ ↦ r) 0 (cfc_predicate_zero R)]
  rintro - ⟨x, -, rfl⟩
  simp

include instCFC in
/-
**CFC.spectrum_algebraMap_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.spectrum_algebraMap_eq [Nontrivial A] (r : R) : spectrum R (algebraMap
 R A r) = {r}
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_predicate_zero`：cfc_predicate_zero : p 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `spectrum.zero_mem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [
inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   ¬IsUnit a → 0 ∈ spectrum R a
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
-/
lemma CFC.spectrum_algebraMap_eq [Nontrivial A] (r : R) :
    spectrum R (algebraMap R A r) = {r} := by
  have hp : p 0 := cfc_predicate_zero R
  rw [← cfc_const r 0 hp, cfc_map_spectrum (fun _ => r) 0 hp]
  exact Set.Nonempty.image_const (⟨0, spectrum.zero_mem (R := R) not_isUnit_zero⟩) _

include instCFC in
/-
**CFC.spectrum_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.spectrum_zero_eq [Nontrivial A] : spectrum R (0 : A) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.spectrum_algebraMap_eq`：CFC.spectrum_algebraMap_eq [Nontrivial A] (r
 : R) : spectrum R (algebraMap R A r) = {r}
-/
lemma CFC.spectrum_zero_eq [Nontrivial A] :
    spectrum R (0 : A) = {0} := by
  have : (0 : A) = algebraMap R A 0 := Eq.symm (map_zero (algebraMap R A))
  rw [this, spectrum_algebraMap_eq]

include instCFC in
/-
**CFC.spectrum_one_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.spectrum_one_eq [Nontrivial A] : spectrum R (1 : A) = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.spectrum_algebraMap_eq`：CFC.spectrum_algebraMap_eq [Nontrivial A] (r
 : R) : spectrum R (algebraMap R A r) = {r}
-/
lemma CFC.spectrum_one_eq [Nontrivial A] :
    spectrum R (1 : A) = {1} := by
  have : (1 : A) = algebraMap R A 1 := Eq.symm (map_one (algebraMap R A))
  rw [this, spectrum_algebraMap_eq]

@[simp]
/-
**cfc_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap R A r) = algebraMa
p R A (f r)
参数：r : R；f : R -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_singleton`：continuousOn_singleton (f : α -> β) (a : α) : Co
ntinuousOn f {a}
· 使用引理 `CFC.spectrum_algebraMap_subset`：CFC.spectrum_algebraMap_subset (r : R) :
 spectrum R (algebraMap R A r) subseteq {r}
· 使用引理 `cfc_predicate_algebraMap`：cfc_predicate_algebraMap (r : R) : p (algebraM
ap R A r)
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_algebraMap (r : R) (f : R → R) : cfc f (algebraMap R A r) = algebraMap R A (f r) := by
  have h₁ : ContinuousOn f (spectrum R (algebraMap R A r)) :=
  continuousOn_singleton _ _ |>.mono <| CFC.spectrum_algebraMap_subset r
  rw [cfc_apply f (algebraMap R A r) (cfc_predicate_algebraMap r),
    ← AlgHomClass.commutes (cfcHom (p := p) (cfc_predicate_algebraMap r)) (f r)]
  congr
  ext ⟨x, hx⟩
  apply CFC.spectrum_algebraMap_subset r at hx
  simp_all
/-
**cfc_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologicalSemiring R]
 [inst_4 : ContinuousStar R] [inst_5 : TopologicalSpace A] [inst_6 : Ring A]   [
inst_7 : StarRing A] [inst_8 : Algebra R A] [instCFC : ContinuousFunctionalCalcu
lus R A p] {f : R → R},   cfc f 0 = (algebraMap R A) (f 0)
参数：algebraMap R A；f 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
-/
@[simp] lemma cfc_apply_zero {f : R → R} : cfc f (0 : A) = algebraMap R A (f 0) := by
  simpa using cfc_algebraMap (A := A) 0 f
/-
**cfc_apply_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologicalSemiring R]
 [inst_4 : ContinuousStar R] [inst_5 : TopologicalSpace A] [inst_6 : Ring A]   [
inst_7 : StarRing A] [inst_8 : Algebra R A] [instCFC : ContinuousFunctionalCalcu
lus R A p] {f : R → R},   cfc f 1 = (algebraMap R A) (f 1)
参数：algebraMap R A；f 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
-/
@[simp] lemma cfc_apply_one {f : R → R} : cfc f (1 : A) = algebraMap R A (f 1) := by
  simpa using cfc_algebraMap (A := A) 1 f

@[simp]
/-
**IsStarNormal.cfc_map** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsStarNormal.cfc_map (f : R -> R) (a : A) : IsStarNormal (cfc f a) where s
tar_comm_self
参数：f : R -> R；a : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_star`：cfc_star (f : R -> R) (a : A) : cfc (fun x => star (f x)) a = 
star (cfc f a)
· 使用引理 `cfc_mul`：cfc_mul (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R
 a)
· 使用定理 `ContinuousOn.star`：ContinuousOn.star (hf : ContinuousOn f s) : Continuou
sOn (fun x => star (f x)) s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsStarNormal.cfc_map (f : R → R) (a : A) : IsStarNormal (cfc f a) where
  star_comm_self := by
    rw [Commute, SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

-- The following two lemmas are just `cfc_predicate`, but specific enough for the `@[simp]` tag.
@[simp]
/-
**IsSelfAdjoint.cfc** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologicalSemiring R] [inst_4 : Cont
inuousStar R] [inst_5 : TopologicalSpace A] [inst_6 : Ring A]   [inst_7 : StarRi
ng A] [inst_8 : Algebra R A] [inst_9 : ContinuousFunctionalCalculus R A IsSelfAd
joint] {f : R → R}   {a : A}, IsSelfAdjoint (cfc f a)
参数：cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_predicate`：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
-/
protected lemma IsSelfAdjoint.cfc [ContinuousFunctionalCalculus R A IsSelfAdjoint]
    {f : R → R} {a : A} : IsSelfAdjoint (cfc f a) :=
  cfc_predicate _ _

@[simp]
/-
**cfc_nonneg_of_predicate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nonneg_of_predicate [LE A] [ContinuousFunctionalCalculus R A (0 <= ·)]
 {f : R -> R} {a : A} : 0 <= cfc f a
参数：0 <= ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_predicate`：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
-/
lemma cfc_nonneg_of_predicate [LE A]
    [ContinuousFunctionalCalculus R A (0 ≤ ·)] {f : R → R} {a : A} : 0 ≤ cfc f a :=
  cfc_predicate _ _

variable (R) in
/-- In an `R`-algebra with a continuous functional calculus, every element satisfying the predicate
has nonempty `R`-spectrum. -/
@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead."
  (since := "2026-03-08")]
/-
**CFC.spectrum_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.spectrum_nonempty [Nontrivial A] (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
-/
lemma CFC.spectrum_nonempty [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    (spectrum R a).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty a ha

end CFC

end Basic

section Inv

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-
**isUnit_cfc_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_cfc_iff (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectrum.zero_notMem_iff`：zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUn
it a
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isUnit_cfc_iff (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : IsUnit (cfc f a) ↔ ∀ x ∈ spectrum R a, f x ≠ 0 := by
  rw [← spectrum.zero_notMem_iff R, cfc_map_spectrum ..]
  simp

alias ⟨_, isUnit_cfc⟩ := isUnit_cfc_iff

variable [ContinuousInv₀ R] (f : R → R) (a : A)

/-- Bundle `cfc f a` into a unit given a proof that `f` is nonzero on the spectrum of `a`. -/
@[simps]
/-
**cfcUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cfcUnits (hf' : forall x in spectrum R a, f x != 0) (hf : ContinuousOn f (
spectrum R a)
参数：hf' : forall x in spectrum R a, f x != 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `cfc f a` into a unit given a proof that `f` is nonzero on the spectrum o
f `a`.
-/
noncomputable def cfcUnits (hf' : ∀ x ∈ spectrum R a, f x ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) : Aˣ where
  val := cfc f a
  inv := cfc (fun x ↦ (f x)⁻¹) a
  val_inv := by
    rw [← cfc_mul .., ← cfc_one R a]
    exact cfc_congr fun _ _ ↦ by aesop
  inv_val := by
    rw [← cfc_mul .., ← cfc_one R a]
    exact cfc_congr fun _ _ ↦ by aesop
/-
**cfcUnits_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcUnits_pow (hf' : forall x in spectrum R a, f x != 0) (n : Nat) (hf : Co
ntinuousOn f (spectrum R a)
参数：hf' : forall x in spectrum R a, f x != 0；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `cfcUnits.congr_simp`：∀ {R : Type u_1} {A : Type u_2} {p p_1 : A → Prop} 
(e_p : p = p_1) [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpa
ce R] [in…
· 使用定理 `val_cfcUnits`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Sem
ifield R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologic
al…
· 使用引理 `cfc_const_one`：cfc_const_one : cfc (fun _ : R => 1) a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `cfc_pow`：cfc_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f (sp
ectrum R a)
-/
lemma cfcUnits_pow (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℕ)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (cfcUnits f a hf') ^ n =
      cfcUnits _ _ (forall₂_imp (fun _ _ ↦ pow_ne_zero n) hf') (hf := hf.fun_pow n) := by
  ext
  cases n with
  | zero => simp [cfc_const_one R a]
  | succ n => simp [cfc_pow f _ a]
/-
**cfc_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_inv (hf' : forall x in spectrum R a, f x != 0) (hf : ContinuousOn f (s
pectrum R a)
参数：hf' : forall x in spectrum R a, f x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `val_inv_cfcUnits`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst :
 Semifield R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopol
ogical…
· 使用定理 `val_cfcUnits`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Sem
ifield R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologic
al…
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
-/
lemma cfc_inv (hf' : ∀ x ∈ spectrum R a, f x ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ (f x)⁻¹) a = (cfc f a)⁻¹ʳ := by
  rw [← val_inv_cfcUnits f a hf', ← val_cfcUnits f a hf', Ring.inverse_unit]
/-
**cfc_inv_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_inv_id (a : Aˣ) (ha : p a
参数：a : Aˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_inv`：cfc_inv (hf' : forall x in spectrum R a, f x != 0) (hf : Contin
uousOn f (spectrum R a)
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma cfc_inv_id (a : Aˣ) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ x⁻¹ : R → R) (a : A) = a⁻¹ := by
  rw [← Ring.inverse_unit]
  convert! cfc_inv (id : R → R) (a : A) ?_
  · exact (cfc_id R (a : A)).symm
  · rintro x hx rfl
    exact spectrum.zero_notMem R a.isUnit hx
/-
**cfc_ringInverse_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_ringInverse_id (ha_unit : IsUnit a) (ha : p a
参数：ha_unit : IsUnit a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_of_isUnit`：inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ
 = ((h.unit⁻¹ : M₀ˣ) : M₀)
· 使用引理 `cfc_inv_id`：cfc_inv_id (a : Aˣ) (ha : p a
-/
lemma cfc_ringInverse_id (ha_unit : IsUnit a) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ x⁻¹ : R → R) a = a⁻¹ʳ := by
  rw [Ring.inverse_of_isUnit ha_unit]
  change cfc (fun x ↦ x⁻¹ : R → R) (ha_unit.unit : A) = ha_unit.unit⁻¹
  exact cfc_inv_id _ ha
/-
**cfc_map_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_map_div (f g : R -> R) (a : A) (hg' : forall x in spectrum R a, g x !=
 0) (hf : ContinuousOn f (spectrum R a)
参数：f g : R -> R；a : A；hg' : forall x in spectrum R a, g x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `cfc_mul`：cfc_mul (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R
 a)
· 使用定理 `ContinuousOn.fun_inv₀`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : Zero G₀]
 [inst_1 : Inv G₀] [inst_2 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   {f : α →
 G₀} {s : S…
· 使用引理 `cfc_inv`：cfc_inv (hf' : forall x in spectrum R a, f x != 0) (hf : Contin
uousOn f (spectrum R a)
-/
lemma cfc_map_div (f g : R → R) (a : A) (hg' : ∀ x ∈ spectrum R a, g x ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ f x / g x) a = cfc f a * (cfc g a)⁻¹ʳ := by
  simp only [div_eq_mul_inv]
  rw [cfc_mul .., cfc_inv g a hg']

section ContinuousOnInvSpectrum
-- TODO: this section should probably be moved to another file altogether

variable {R A : Type*} [Semifield R] [Ring A] [TopologicalSpace R] [ContinuousInv₀ R]
variable [Algebra R A]

@[fun_prop]
/-
**Units.continuousOn_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Units.continuousOn_inv₀_spectrum (a : Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A)) :=
  continuousOn_inv₀.mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

@[fun_prop]
/-
**Units.continuousOn_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Units.continuousOn_zpow₀_spectrum [ContinuousMul R] (a : Aˣ) (n : ℤ) :
    ContinuousOn (· ^ n) (spectrum R (a : A)) :=
  (continuousOn_zpow₀ n).mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

end ContinuousOnInvSpectrum

/-
**cfcUnits_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcUnits_zpow (hf' : forall x in spectrum R a, f x != 0) (n : Int) (hf : C
ontinuousOn f (spectrum R a)
参数：hf' : forall x in spectrum R a, f x != 0；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `ContinuousOn.zpow₀`：ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : Int)
 (h : forall a in s, f a != 0 ∨ 0 <= m) : ContinuousOn (fun x => f x ^ m) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcUnits.congr_simp`：∀ {R : Type u_1} {A : Type u_2} {p p_1 : A → Prop} 
(e_p : p = p_1) [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpa
ce R] [in…
· 使用引理 `cfcUnits_pow`：cfcUnits_pow (hf' : forall x in spectrum R a, f x != 0) (n
 : Nat) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用引理 `cfc_pow`：cfc_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f (sp
ectrum R a)
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
-/
lemma cfcUnits_zpow (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℤ)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (cfcUnits f a hf') ^ n =
      cfcUnits (f ^ n) a (forall₂_imp (fun _ _ ↦ zpow_ne_zero n) hf')
        (hf.zpow₀ n (forall₂_imp (fun _ _ ↦ Or.inl) hf')) := by
  cases n with
  | ofNat _ => simpa using! cfcUnits_pow f a hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
    exact cfc_pow (hf := hf.inv₀ hf') .. |>.symm
/-
**cfc_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_zpow (a : Aˣ) (n : Int) (ha : p a
参数：a : Aˣ；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用引理 `cfc_pow`：cfc_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f (sp
ectrum R a)
· 使用引理 `Units.continuousOn_inv₀_spectrum`：Units.continuousOn_inv₀_spectrum (a : 
Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A))
· 使用引理 `cfc_inv_id`：cfc_inv_id (a : Aˣ) (ha : p a
-/
lemma cfc_zpow (a : Aˣ) (n : ℤ) (ha : p a := by cfc_tac) :
    cfc (fun x : R ↦ x ^ n) (a : A) = ↑(a ^ n) := by
  cases n with
  | ofNat n => simpa using cfc_pow_id (a : A) n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfc_pow (fun x ↦ x⁻¹ : R → R) (n + 1) (a : A)
    exact this.trans <| congr($(cfc_inv_id a) ^ (n + 1))

variable [UniqueHom R A]
/-
**cfc_comp_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_inv (f : R -> R) (a : Aˣ) (hf : ContinuousOn f ((·⁻¹) '' (spectru
m R (a : A)))
参数：f : R -> R；a : Aˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用引理 `Units.continuousOn_inv₀_spectrum`：Units.continuousOn_inv₀_spectrum (a : 
Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A))
· 使用引理 `cfc_inv_id`：cfc_inv_id (a : Aˣ) (ha : p a
-/
lemma cfc_comp_inv (f : R → R) (a : Aˣ)
    (hf : ContinuousOn f ((·⁻¹) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc (fun x ↦ f x⁻¹) (a : A) = cfc f (↑a⁻¹ : A) := by
  rw [cfc_comp' .., cfc_inv_id _]
/-
**cfc_comp_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_zpow (f : R -> R) (n : Int) (a : Aˣ) (hf : ContinuousOn f ((· ^ n
) '' (spectrum R (a : A)))
参数：f : R -> R；n : Int；a : Aˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用引理 `Units.continuousOn_zpow₀_spectrum`：Units.continuousOn_zpow₀_spectrum [Co
ntinuousMul R] (a : Aˣ) (n : Int) : ContinuousOn (· ^ n) (spectrum R (a : A))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用引理 `cfc_zpow`：cfc_zpow (a : Aˣ) (n : Int) (ha : p a
-/
lemma cfc_comp_zpow (f : R → R) (n : ℤ) (a : Aˣ)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc (fun x ↦ f (x ^ n)) (a : A) = cfc f (↑(a ^ n) : A) := by
  rw [cfc_comp' .., cfc_zpow a]

end Inv

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
variable (f g : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
variable (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)

set_option backward.privateInPublic true in
include hf hg in
/-
**cfc_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_sub : cfc (fun x => f x - g x) a = cfc f a - cfc g a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_sub : cfc (fun x ↦ f x - g x) a = cfc f a - cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_sub, cfc_apply ..]
    congr
  · simp [cfc_apply_of_not_predicate a ha]
/-
**cfc_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_neg : cfc (fun x => -(f x)) a = -(cfc f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma cfc_neg : cfc (fun x ↦ -(f x)) a = -(cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a, ← map_neg, cfc_apply ..]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_continuousOn, neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.fun_neg
/-
**cfc_neg'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_neg' : cfc (-f) = (-cfc f : A -> A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `cfc_neg`：cfc_neg : cfc (fun x => -(f x)) a = -(cfc f a)
-/
lemma cfc_neg' : cfc (-f) = (-cfc f : A → A) := by ext1 a; exact cfc_neg f a
/-
**cfc_neg_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_neg_id (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_neg`：cfc_neg : cfc (fun x => -(f x)) a = -(cfc f a)
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
-/
lemma cfc_neg_id (ha : p a := by cfc_tac) : cfc (- · : R → R) a = -a := by
  rw [cfc_neg _ a, cfc_id' R a]

variable [UniqueHom R A]
/-
**cfc_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_neg (hf : ContinuousOn f ((-·) '' (spectrum R (a : A)))
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_neg_id`：cfc_neg_id (ha : p a
-/
lemma cfc_comp_neg (hf : ContinuousOn f ((-·) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (f <| - ·) a = cfc f (-a) := by
  rw [cfc_comp' .., cfc_neg_id _]

end Neg

section Order

section Semiring

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [PartialOrder R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

/-
**cfcHom_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (hfg : f <= g) :
 cfcHom ha f <= cfcHom ha g
参数：ha : p a；spectrum R a, R；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `StarRingHomClass.instOrderHomClass`：∀ {F : Type u_3} {R : Type u_4} {S :
 Type u_5} [inst : NonUnitalSemiring R] [inst_1 : PartialOrder R]   [inst_2 : St
arRing R] [StarOrderedRi…
· 使用定理 `ContinuousMap.instStarOrderedRingOfContinuousSqrt`：∀ {α : Type u_1} [ins
t : TopologicalSpace α] {R : Type u_2} [inst_1 : PartialOrder R] [inst_2 : NonUn
italSemiring R]   [inst_3 : StarRing R]…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `NonUnitalStarAlgHomClass.instNonUnitalStarRingHomClassOfStarHomClass`：∀ 
{F : Type u_1} {R : Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [i
nst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
-/
lemma cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (hfg : f ≤ g) :
    cfcHom ha f ≤ cfcHom ha g :=
  OrderHomClass.mono (cfcHom ha) hfg
/-
**cfcHom_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(spec
trum R a, R)} : 0 <= cfcHom ha f ↔ 0 <= f
参数：ha : p a；spectrum R a, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
· 使用引理 `cfcHom_map_spectrum`：cfcHom_map_spectrum (f : C(spectrum R a, R)) : spec
trum R (cfcHom ha f) = Set.range f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用引理 `cfcHom_mono`：cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (
hfg : f <= g) : cfcHom ha f <= cfcHom ha g
-/
lemma cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(spectrum R a, R)} :
    0 ≤ cfcHom ha f ↔ 0 ≤ f := by
  constructor
  · exact fun hf x ↦ (cfcHom_map_spectrum ha (R := R) _ ▸ spectrum_nonneg_of_nonneg hf) ⟨x, rfl⟩
  · simpa using (cfcHom_mono ha (f := 0) (g := f) ·)
/-
**cfcHom_isStrictlyPositive_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_isStrictlyPositive_iff [NonnegSpectrumClass R A] {a : A} (ha : p a)
 {f : C(spectrum R a, R)} : IsStrictlyPositive (cfcHom ha f) ↔ forall x, 0 < f x
参数：ha : p a；spectrum R a, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStrictlyPositive.spectrum_pos`：spectrum_pos [CommSemiring 𝕜] [PartialO
rder 𝕜] [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : IsStrictlyPositive
 a) {x : 𝕜} (hx : x i…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcHom_map_spectrum`：cfcHom_map_spectrum (f : C(spectrum R a, R)) : spec
trum R (cfcHom ha f) = Set.range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `cfcHom_nonneg_iff`：cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (
ha : p a) {f : C(spectrum R a, R)} : 0 <= cfcHom ha f ↔ 0 <= f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `spectrum.isUnit_of_zero_notMem`：∀ (R : Type u) {A : Type v} [inst : Comm
Semiring R] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   0 ∉ spectrum R a
 → IsUnit a
-/
lemma cfcHom_isStrictlyPositive_iff [NonnegSpectrumClass R A] {a : A} (ha : p a)
    {f : C(spectrum R a, R)} : IsStrictlyPositive (cfcHom ha f) ↔ ∀ x, 0 < f x := by
  refine ⟨fun hf x => hf.spectrum_pos <| cfcHom_map_spectrum (R := R) ha _ ▸ Set.mem_range_self x,
    fun h => ⟨cfcHom_nonneg_iff _ |>.mpr fun x => le_of_lt (h x), ?_⟩⟩
  apply spectrum.isUnit_of_zero_notMem (R := R)
  grind [cfcHom_map_spectrum, ne_of_lt]
/-
**cfc_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_mono {f g : R -> R} {a : A} (h : forall x in spectrum R a, f x <= g x)
 (hf : ContinuousOn f (spectrum R a)
参数：h : forall x in spectrum R a, f x <= g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_mono`：cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (
hfg : f <= g) : cfcHom ha f <= cfcHom ha g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
-/
lemma cfc_mono {f g : R → R} {a : A} (h : ∀ x ∈ spectrum R a, f x ≤ g x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc f a ≤ cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a]
    exact cfcHom_mono ha fun x ↦ h x.1 x.2
  · simp only [cfc_apply_of_not_predicate _ ha, le_rfl]
/-
**cfc_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nonneg_iff [NonnegSpectrumClass R A] (f : R -> R) (a : A) (hf : Contin
uousOn f (spectrum R a)
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_nonneg_iff`：cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (
ha : p a) {f : C(spectrum R a, R)} : 0 <= cfcHom ha f ↔ 0 <= f
· 使用定理 `ContinuousMap.le_def`：le_def [PartialOrder β] {f g : C(α, β)} : f <= g ↔
 forall a, f a <= g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cfc_nonneg_iff [NonnegSpectrumClass R A] (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : 0 ≤ cfc f a ↔ ∀ x ∈ spectrum R a, 0 ≤ f x := by
  rw [cfc_apply .., cfcHom_nonneg_iff, ContinuousMap.le_def]
  simp
/-
**StarOrderedRing.nonneg_iff_spectrum_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StarOrderedRing.nonneg_iff_spectrum_nonneg [NonnegSpectrumClass R A] (a : 
A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_nonneg_iff`：cfc_nonneg_iff [NonnegSpectrumClass R A] (f : R -> R) (a
 : A) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
-/
lemma StarOrderedRing.nonneg_iff_spectrum_nonneg [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : 0 ≤ a ↔ ∀ x ∈ spectrum R a, 0 ≤ x := by
  have := cfc_nonneg_iff (id : R → R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this
/-
**cfc_isStrictlyPositive_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_isStrictlyPositive_iff [NonnegSpectrumClass R A] (f : R -> R) (a : A) 
(hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_isStrictlyPositive_iff`：cfcHom_isStrictlyPositive_iff [NonnegSpec
trumClass R A] {a : A} (ha : p a) {f : C(spectrum R a, R)} : IsStrictlyPositive 
(cfcHom ha f) ↔ for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cfc_isStrictlyPositive_iff [NonnegSpectrumClass R A] (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : IsStrictlyPositive (cfc f a) ↔ ∀ x ∈ spectrum R a, 0 < f x := by
  rw [cfc_apply .., cfcHom_isStrictlyPositive_iff]
  simp
/-
**StarOrderedRing.isStrictlyPositive_iff_spectrum_pos** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：StarOrderedRing.isStrictlyPositive_iff_spectrum_pos [NonnegSpectrumClass R
 A] (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_isStrictlyPositive_iff`：cfc_isStrictlyPositive_iff [NonnegSpectrumCl
ass R A] (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
-/
lemma StarOrderedRing.isStrictlyPositive_iff_spectrum_pos [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : IsStrictlyPositive a ↔ ∀ x ∈ spectrum R a, 0 < x := by
  have := cfc_isStrictlyPositive_iff (id : R → R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this
/-
**cfc_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nonneg {f : R -> R} {a : A} (h : forall x in spectrum R a, 0 <= f x) :
 0 <= cfc f a
参数：h : forall x in spectrum R a, 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_const_zero`：cfc_const_zero : cfc (fun _ : R => 0) a = 0
· 使用引理 `cfc_mono`：cfc_mono {f g : R -> R} {a : A} (h : forall x in spectrum R a,
 f x <= g x) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
-/
lemma cfc_nonneg {f : R → R} {a : A} (h : ∀ x ∈ spectrum R a, 0 ≤ f x) :
    0 ≤ cfc f a := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]
/-
**cfc_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nonpos (f : R -> R) (a : A) (h : forall x in spectrum R a, f x <= 0) :
 cfc f a <= 0
参数：f : R -> R；a : A；h : forall x in spectrum R a, f x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_const_zero`：cfc_const_zero : cfc (fun _ : R => 0) a = 0
· 使用引理 `cfc_mono`：cfc_mono {f g : R -> R} {a : A} (h : forall x in spectrum R a,
 f x <= g x) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
-/
lemma cfc_nonpos (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ 0) :
    cfc f a ≤ 0 := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]
/-
**cfc_le_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_le_algebraMap (f : R -> R) (r : R) (a : A) (h : forall x in spectrum R
 a, f x <= r) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；r : R；a : A；h : forall x in spectrum R a, f x <= r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_mono`：cfc_mono {f g : R -> R} {a : A} (h : forall x in spectrum R a,
 f x <= g x) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
-/
lemma cfc_le_algebraMap (f : R → R) (r : R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ r)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ algebraMap R A r :=
  cfc_const r a ▸ cfc_mono h
/-
**algebraMap_le_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_le_cfc (f : R -> R) (r : R) (a : A) (h : forall x in spectrum R
 a, r <= f x) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；r : R；a : A；h : forall x in spectrum R a, r <= f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_mono`：cfc_mono {f g : R -> R} {a : A} (h : forall x in spectrum R a,
 f x <= g x) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
-/
lemma algebraMap_le_cfc (f : R → R) (r : R) (a : A) (h : ∀ x ∈ spectrum R a, r ≤ f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    algebraMap R A r ≤ cfc f a :=
  cfc_const r a ▸ cfc_mono h
/-
**le_algebraMap_of_spectrum_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_algebraMap_of_spectrum_le {r : R} {a : A} (h : forall x in spectrum R a
, x <= r) (ha : p a
参数：h : forall x in spectrum R a, x <= r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_le_algebraMap`：cfc_le_algebraMap (f : R -> R) (r : R) (a : A) (h : f
orall x in spectrum R a, f x <= r) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma le_algebraMap_of_spectrum_le {r : R} {a : A} (h : ∀ x ∈ spectrum R a, x ≤ r)
    (ha : p a := by cfc_tac) : a ≤ algebraMap R A r := by
  rw [← cfc_id R a]
  exact cfc_le_algebraMap id r a h
/-
**algebraMap_le_of_le_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_le_of_le_spectrum {r : R} {a : A} (h : forall x in spectrum R a
, r <= x) (ha : p a
参数：h : forall x in spectrum R a, r <= x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `algebraMap_le_cfc`：algebraMap_le_cfc (f : R -> R) (r : R) (a : A) (h : f
orall x in spectrum R a, r <= f x) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma algebraMap_le_of_le_spectrum {r : R} {a : A} (h : ∀ x ∈ spectrum R a, r ≤ x)
    (ha : p a := by cfc_tac) : algebraMap R A r ≤ a := by
  rw [← cfc_id R a]
  exact algebraMap_le_cfc id r a h
/-
**cfc_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_le_one (f : R -> R) (a : A) (h : forall x in spectrum R a, f x <= 1) :
 cfc f a <= 1
参数：f : R -> R；a : A；h : forall x in spectrum R a, f x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用引理 `cfcHom_mono`：cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (
hfg : f <= g) : cfcHom ha f <= cfcHom ha g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma cfc_le_one (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ 1) : cfc f a ≤ 1 := by
  apply cfc_cases (· ≤ 1) _ _ (by simp) fun hf ha ↦ ?_
  rw [← map_one (cfcHom ha (R := R))]
  apply cfcHom_mono ha
  simpa [ContinuousMap.le_def] using h
/-
**one_le_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_cfc (f : R -> R) (a : A) (h : forall x in spectrum R a, 1 <= f x) (
hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；a : A；h : forall x in spectrum R a, 1 <= f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `algebraMap_le_cfc`：algebraMap_le_cfc (f : R -> R) (r : R) (a : A) (h : f
orall x in spectrum R a, r <= f x) (hf : ContinuousOn f (spectrum R a)
-/
lemma one_le_cfc (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, 1 ≤ f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    1 ≤ cfc f a := by
  simpa using algebraMap_le_cfc f 1 a h
/-
**CFC.le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.le_one {a : A} (h : forall x in spectrum R a, x <= 1) (ha : p a
参数：h : forall x in spectrum R a, x <= 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `le_algebraMap_of_spectrum_le`：le_algebraMap_of_spectrum_le {r : R} {a : 
A} (h : forall x in spectrum R a, x <= r) (ha : p a
-/
lemma CFC.le_one {a : A} (h : ∀ x ∈ spectrum R a, x ≤ 1) (ha : p a := by cfc_tac) :
    a ≤ 1 := by
  simpa using le_algebraMap_of_spectrum_le h
/-
**CFC.one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.one_le {a : A} (h : forall x in spectrum R a, 1 <= x) (ha : p a
参数：h : forall x in spectrum R a, 1 <= x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `algebraMap_le_of_le_spectrum`：algebraMap_le_of_le_spectrum {r : R} {a : 
A} (h : forall x in spectrum R a, r <= x) (ha : p a
-/
lemma CFC.one_le {a : A} (h : ∀ x ∈ spectrum R a, 1 ≤ x) (ha : p a := by cfc_tac) :
    1 ≤ a := by
  simpa using algebraMap_le_of_le_spectrum h

end Semiring

section NNReal

open scoped NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)]

/-
**CFC.inv_nonneg_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A) <= a
参数：a : Aˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用引理 `cfc_predicate`：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
· 使用引理 `cfc_inv_id`：cfc_inv_id (a : Aˣ) (ha : p a
· 使用定理 `NNReal.instContinuousInv₀`：ContinuousInv₀ NNReal
-/
lemma CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A) ≤ a := by cfc_tac) : (0 : A) ≤ a⁻¹ :=
  cfc_inv_id (R := ℝ≥0) a ▸ cfc_predicate _ (a : A)
/-
**CFC.inv_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.inv_nonneg (a : Aˣ) : (0 : A) <= a⁻¹ ↔ (0 : A) <= a
参数：a : Aˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用引理 `CFC.inv_nonneg_of_nonneg`：CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A
) <= a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma CFC.inv_nonneg (a : Aˣ) : (0 : A) ≤ a⁻¹ ↔ (0 : A) ≤ a :=
  ⟨fun _ ↦ inv_inv a ▸ inv_nonneg_of_nonneg a⁻¹, fun _ ↦ inv_nonneg_of_nonneg a⟩

end NNReal

section Ring

variable {R A : Type*} {p : A → Prop} [CommRing R] [PartialOrder R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]
variable [NonnegSpectrumClass R A]

/-
**cfcHom_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_le_iff {a : A} (ha : p a) {f g : C(spectrum R a, R)} : cfcHom ha f 
<= cfcHom ha g ↔ f <= g
参数：ha : p a；spectrum R a, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用引理 `cfcHom_nonneg_iff`：cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (
ha : p a) {f : C(spectrum R a, R)} : 0 <= cfcHom ha f ↔ 0 <= f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `ContinuousMap.instStarOrderedRingOfContinuousSqrt`：∀ {α : Type u_1} [ins
t : TopologicalSpace α] {R : Type u_2} [inst_1 : PartialOrder R] [inst_2 : NonUn
italSemiring R]   [inst_3 : StarRing R]…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cfcHom_le_iff {a : A} (ha : p a) {f g : C(spectrum R a, R)} :
    cfcHom ha f ≤ cfcHom ha g ↔ f ≤ g := by
  rw [← sub_nonneg, ← map_sub, cfcHom_nonneg_iff, sub_nonneg]
/-
**cfc_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f g : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_le_iff`：cfcHom_le_iff {a : A} (ha : p a) {f g : C(spectrum R a, R
)} : cfcHom ha f <= cfcHom ha g ↔ f <= g
· 使用定理 `ContinuousMap.le_def`：le_def [PartialOrder β] {f g : C(α, β)} : f <= g ↔
 forall a, f a <= g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cfc_le_iff (f g : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum R a, f x ≤ g x := by
  rw [cfc_apply f a, cfc_apply g a, cfcHom_le_iff (show p a from ha), ContinuousMap.le_def]
  simp
/-
**cfc_nonpos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nonpos_iff (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `cfc_nonneg_iff`：cfc_nonneg_iff [NonnegSpectrumClass R A] (f : R -> R) (a
 : A) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
lemma cfc_nonpos_iff (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc f a ≤ 0 ↔ ∀ x ∈ spectrum R a, f x ≤ 0 := by
  simp_rw [← neg_nonneg, ← cfc_neg]
  exact cfc_nonneg_iff (fun x ↦ -f x) a
/-
**cfc_le_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_le_algebraMap_iff (f : R -> R) (r : R) (a : A) (hf : ContinuousOn f (s
pectrum R a)
参数：f : R -> R；r : R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用引理 `cfc_le_iff`：cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spec
trum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cfc_le_algebraMap_iff (f : R → R) (r : R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ algebraMap R A r ↔ ∀ x ∈ spectrum R a, f x ≤ r := by
  rw [← cfc_const r a, cfc_le_iff ..]
/-
**algebraMap_le_cfc_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_le_cfc_iff (f : R -> R) (r : R) (a : A) (hf : ContinuousOn f (s
pectrum R a)
参数：f : R -> R；r : R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_const`：cfc_const (r : R) (a : A) (ha : p a
· 使用引理 `cfc_le_iff`：cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spec
trum R a)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma algebraMap_le_cfc_iff (f : R → R) (r : R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    algebraMap R A r ≤ cfc f a ↔ ∀ x ∈ spectrum R a, r ≤ f x := by
  rw [← cfc_const r a, cfc_le_iff ..]
/-
**le_algebraMap_iff_spectrum_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_algebraMap_iff_spectrum_le {r : R} {a : A} (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_le_algebraMap_iff`：cfc_le_algebraMap_iff (f : R -> R) (r : R) (a : A
) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma le_algebraMap_iff_spectrum_le {r : R} {a : A} (ha : p a := by cfc_tac) :
    a ≤ algebraMap R A r ↔ ∀ x ∈ spectrum R a, x ≤ r := by
  nth_rw 1 [← cfc_id R a]
  exact cfc_le_algebraMap_iff id r a
/-
**algebraMap_le_iff_le_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap_le_iff_le_spectrum {r : R} {a : A} (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `algebraMap_le_cfc_iff`：algebraMap_le_cfc_iff (f : R -> R) (r : R) (a : A
) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma algebraMap_le_iff_le_spectrum {r : R} {a : A} (ha : p a := by cfc_tac) :
    algebraMap R A r ≤ a ↔ ∀ x ∈ spectrum R a, r ≤ x := by
  nth_rw 1 [← cfc_id R a]
  exact algebraMap_le_cfc_iff id r a
/-
**cfc_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_le_one_iff (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `cfc_le_algebraMap_iff`：cfc_le_algebraMap_iff (f : R -> R) (r : R) (a : A
) (hf : ContinuousOn f (spectrum R a)
-/
lemma cfc_le_one_iff (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ 1 ↔ ∀ x ∈ spectrum R a, f x ≤ 1 := by
  simpa using cfc_le_algebraMap_iff f 1 a
/-
**one_le_cfc_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_cfc_iff (f : R -> R) (a : A) (hf : ContinuousOn f (spectrum R a)
参数：f : R -> R；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `algebraMap_le_cfc_iff`：algebraMap_le_cfc_iff (f : R -> R) (r : R) (a : A
) (hf : ContinuousOn f (spectrum R a)
-/
lemma one_le_cfc_iff (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    1 ≤ cfc f a ↔ ∀ x ∈ spectrum R a, 1 ≤ f x := by
  simpa using algebraMap_le_cfc_iff f 1 a
/-
**CFC.le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.le_one_iff (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `le_algebraMap_iff_spectrum_le`：le_algebraMap_iff_spectrum_le {r : R} {a 
: A} (ha : p a
-/
lemma CFC.le_one_iff (a : A) (ha : p a := by cfc_tac) :
    a ≤ 1 ↔ ∀ x ∈ spectrum R a, x ≤ 1 := by
  simpa using le_algebraMap_iff_spectrum_le (r := (1 : R)) (a := a)
/-
**CFC.one_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.one_le_iff (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `algebraMap_le_iff_le_spectrum`：algebraMap_le_iff_le_spectrum {r : R} {a 
: A} (ha : p a
-/
lemma CFC.one_le_iff (a : A) (ha : p a := by cfc_tac) :
    1 ≤ a ↔ ∀ x ∈ spectrum R a, 1 ≤ x := by
  simpa using algebraMap_le_iff_le_spectrum (r := (1 : R)) (a := a)

end Ring

end Order

/-! ### `cfcHom` on a superset of the spectrum -/

section Superset

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

/-- The composition of `cfcHom` with the natural embedding `C(s, R) → C(spectrum R a, R)`
whenever `spectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions applied to multiple
distinct elements, with the added constraint that `cfc` does not suffice. This can occur, for
example, if it is necessary to use uniqueness of this continuous functional calculus. -/
@[simps!]
/-
**cfcHomSuperset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cfcHomSuperset {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subseteq 
s) : C(s, R) ->⋆ₐ[R] A
参数：ha : p a；hs : spectrum R a subseteq s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `cfcHom` with the natural embedding `C(s, R) → C(spectrum R a
, R)`
whenever `spectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions a
pplied to multiple
distinct elements, with the added constraint that `cfc` does not suffice. This c
an occur, for
example, if it is necessary to use uniqueness of this continuous functional calc
ulus.
-/
noncomputable def cfcHomSuperset {a : A} (ha : p a) {s : Set R} (hs : spectrum R a ⊆ s) :
    C(s, R) →⋆ₐ[R] A :=
  cfcHom ha |>.comp <| ContinuousMap.compStarAlgHom' R R <| ⟨_, continuous_id.subtype_map hs⟩
/-
**cfcHomSuperset_continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : spectrum R 
a subseteq s) : Continuous (cfcHomSuperset ha hs)
参数：ha : p a；hs : spectrum R a subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
-/
lemma cfcHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : spectrum R a ⊆ s) :
    Continuous (cfcHomSuperset ha hs) :=
  (cfcHom_continuous ha).comp <| ContinuousMap.continuous_precomp _
/-
**cfcHomSuperset_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : spectrum R a subset
eq s) : cfcHomSuperset ha hs (.restrict s <| .id R) = a
参数：ha : p a；hs : spectrum R a subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
-/
lemma cfcHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : spectrum R a ⊆ s) :
    cfcHomSuperset ha hs (.restrict s <| .id R) = a :=
  cfcHom_id ha

end Superset

section IsClosedEmbedding

/-- A class for the continuous functional calculus which requires the homomorphisms
`C(spectrum R a, R) → A` to be closed embeddings, as opposed to only continuous and injective.

The primary advantage of this is that one can conclude the range of this map is the closed
star subalgebra generated by `a`. However, unless the topology on `A` is induced by a C⋆-norm,
this is unlikely to occur. -/
/-
**ClosedEmbeddingContinuousFunctionalCalculus** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：ClosedEmbeddingContinuousFunctionalCalculus (R A : Type*) (p : outParam (A
 -> Prop)) [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring 
R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] e
xtends ContinuousFunctionalCalculus R A p where isClosedEmbedding (a : A) (ha : 
p a) : Topology.IsClosedEmbedding (cfcHom (R
参数：R A : Type*；p : outParam (A -> Prop)；a : A；ha : p a。
继承自：ContinuousFunctionalCalculus R A p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class for the continuous functional calculus which requires the homomorphisms
`C(spectrum R a, R) → A` to be closed embeddings, as opposed to only continuous 
and injective.

The primary advantage of this is that one can conclude the range of this map is 
the closed
star subalgebra generated by `a`. However, unless the topology on `A` is induced
 by a C⋆-norm,
this is unlikely to occur.
-/
class ClosedEmbeddingContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] extends
    ContinuousFunctionalCalculus R A p where
  isClosedEmbedding (a : A) (ha : p a) : Topology.IsClosedEmbedding (cfcHom (R := R) ha)
/-
**cfcHom_isClosedEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_isClosedEmbedding {R A : Type*} {p : A -> Prop} [CommSemiring R] [S
tarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Topolog
icalSpace A] [Ring A] [StarRing A] [Algebra R A] [instCFC : ClosedEmbeddingConti
nuousFunctionalCalculus R A p] {a : A} (ha : p a) : IsClosedEmbedding (cfcHom ha
 : C(spectrum R a, R) ->⋆ₐ[R] A)
参数：ha : p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding`：∀ {R : Ty
pe u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1
 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
-/
lemma cfcHom_isClosedEmbedding {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [instCFC : ClosedEmbeddingContinuousFunctionalCalculus R A p]
    {a : A} (ha : p a) : IsClosedEmbedding <| (cfcHom ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  ClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

end IsClosedEmbedding

