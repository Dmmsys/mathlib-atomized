/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`ImplicitFunctionData` that holds arguments for the most general version of the implicit function
theorem, see `ImplicitFunctionData.implicitFunction` and
`ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`. This version allows a user to choose a
specific implicit function but provides only a little convenience over the inverse function theorem.

Then we define `HasStrictFDerivAt.implicitFunctionDataOfComplemented`: implicit function defined by
`f (g z y) = z`, where `f : E → F` is a function strictly differentiable at `a` such that its
derivative `f'` is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite-dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `HasStrictFDerivAt`
and `f'.range = ⊤`. This version is named `HasStrictFDerivAt.implicitFunction`.

For the version where the implicit equation is defined by a $C^n$ function `f : E × F → G` with an
invertible derivative `∂f/∂y`, see `ContDiffAt.implicitFunction`.

## TODO

* Add a version for `f : 𝕜 × 𝕜 → 𝕜` proving `HasStrictDerivAt` and `deriv φ = ...`.
* Prove that in a real vector space the implicit function has the same smoothness as the original
  one.
* If the original function is differentiable in a neighborhood, then the implicit function is
  differentiable in a neighborhood as well. Current setup only proves differentiability at one
  point for the implicit function constructed in this file (as opposed to an unspecified implicit
  function). One of the ways to overcome this difficulty is to use uniqueness of the implicit
  function in the general version of the theorem. Another way is to prove that *any* implicit
  function satisfying some predicate is strictly differentiable.

## Tags

implicit function, inverse function
-/

public section

noncomputable section

open scoped Topology

open Filter

open ContinuousLinearMap (fst snd smulRight ker_prod)

open ContinuousLinearEquiv (ofBijective)

open LinearMap (ker range)

/-!
### General version

Consider two functions `f : E → F` and `g : E → G` and a point `a` such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is an open partial
homeomorphism between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `ImplicitFunctionData.implicitFunction`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`. We also prove a formula for `∂φ / ∂z`.

Though this statement is almost symmetric with respect to `F`, `G`, we interpret it in the following
way. Consider a family of surfaces `{x | f x = y}`, `y ∈ 𝓝 (f a)`. Each of these surfaces is
parametrized by `φ y`.

There are many ways to choose a (differentiable) function `φ` such that `f (φ y z) = y` but the
extra condition `g (φ y z) = z` allows a user to select one of these functions. If we imagine
that the level surfaces `f = const` form a local horizontal foliation, then the choice of
`g` fixes a transverse foliation `g = const`, and `φ` is the inverse function of the projection
of `{x | f x = y}` along this transverse foliation.

This version of the theorem is used to prove the other versions and can be used if a user
needs to have a complete control over the choice of the implicit function.
-/


/--
Definition of `ImplicitFunctionData` / `ImplicitFunctionData` 的定义

English:
structure ImplicitFunctionData
  parameters: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
  axioms and operations (10):
    - leftFun : E -> F
    - leftDeriv : E ->L[𝕜] F
    - rightFun : E -> G
    - rightDeriv : E ->L[𝕜] G
    - pt : E
    - hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
    - hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
    - range_leftDeriv : leftDeriv.range = ⊤
    - range_rightDeriv : rightDeriv.range = ⊤
    - isCompl_ker : IsCompl leftDeriv.ker rightDeriv.ker

中文:
结构 ImplicitFunctionData
  参数: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型)
  公理与运算 (10 个):
    - leftFun : E -> F
    - leftDeriv : E ->L[𝕜] F
    - rightFun : E -> G
    - rightDeriv : E ->L[𝕜] G
    - pt : E
    - hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
    - hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
    - range_leftDeriv : leftDeriv.range = ⊤
    - range_rightDeriv : rightDeriv.range = ⊤
    - isCompl_ker : IsCompl leftDeriv.ker rightDeriv.ker
-/
structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace G] where
  /-- Left function -/
  leftFun : E -> F
  /-- Derivative of the left function -/
  leftDeriv : E ->L[𝕜] F
  /-- Right function -/
  rightFun : E -> G
  /-- Derivative of the right function -/
  rightDeriv : E ->L[𝕜] G
  /-- The point at which `leftFun` and `rightFun` are strictly differentiable -/
  pt : E
  hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
  hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
  range_leftDeriv : leftDeriv.range = ⊤
  range_rightDeriv : rightDeriv.range = ⊤
  isCompl_ker : IsCompl leftDeriv.ker rightDeriv.ker

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

/--
Definition of `prodFun` / `prodFun` 的定义

English:
definition prodFun
  signature: (x : E)
  body: (φ.leftFun x, φ.rightFun x)

@[simp]

中文:
定义 prodFun
  签名: (x : E)
  定义体: (φ.leftFun x, φ.rightFun x)

@[simp]

Depends on / 依赖: leftFun, rightFun
-/
def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)

@[simp]
/--
theorem `prodFun_apply` / 定理 `prodFun_apply`

English:
theorem prodFun_apply
  given: (x : E)
  statement: φ.prodFun x = (φ.leftFun x, φ.rightFun x)
  proof: by
  rfl

中文:
定理 prodFun_apply
  条件: (x : E)
  结论: φ.prodFun x = (φ.leftFun x, φ.rightFun x)
  证明: by
  rfl
-/
theorem prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x) := by
  rfl

/--
theorem `hasStrictFDerivAt` / 定理 `hasStrictFDerivAt`

English:
theorem hasStrictFDerivAt
  proof: φ.hasStrictFDerivAt_leftFun.prodMk φ.hasStrictFDerivAt_rightFun

中文:
定理 hasStrictFDerivAt
  证明: φ.hasStrictFDerivAt_leftFun.prodMk φ.hasStrictFDerivAt_rightFun
-/
protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt φ.prodFun
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv
          φ.isCompl_ker :
        E ->L[𝕜] F × G)
      φ.pt :=
  φ.hasStrictFDerivAt_leftFun.prodMk φ.hasStrictFDerivAt_rightFun

/--
theorem `isInvertible_fderiv_prodFun` / 定理 `isInvertible_fderiv_prodFun`

English:
theorem isInvertible_fderiv_prodFun
  statement: (fderiv 𝕜 φ.prodFun φ.pt).IsInvertible
  proof: by
  rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

中文:
定理 isInvertible_fderiv_prodFun
  结论: (fderiv 𝕜 φ.prodFun φ.pt).IsInvertible
  证明: by
  rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isInvertible_equiv, fderiv, hasFDerivAt, hasStrictFDerivAt, hasStrictFDerivAt.hasFDerivAt.fderiv, isInvertible_equiv
-/
theorem isInvertible_fderiv_prodFun : (fderiv 𝕜 φ.prodFun φ.pt).IsInvertible := by
  rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

/--
Definition of `toOpenPartialHomeomorph` / `toOpenPartialHomeomorph` 的定义

English:
definition toOpenPartialHomeomorph
  signature: : OpenPartialHomeomorph E (F × G)
  body: φ.hasStrictFDerivAt.toOpenPartialHomeomorph _

中文:
定义 toOpenPartialHomeomorph
  签名: : OpenPartialHomeomorph E (F × G)
  定义体: φ.hasStrictFDerivAt.toOpenPartialHomeomorph _

Depends on / 依赖: hasStrictFDerivAt, hasStrictFDerivAt.toOpenPartialHomeomorph, toOpenPartialHomeomorph
-/
def toOpenPartialHomeomorph : OpenPartialHomeomorph E (F × G) :=
  φ.hasStrictFDerivAt.toOpenPartialHomeomorph _

/--
Definition of `implicitFunction` / `implicitFunction` 的定义

English:
definition implicitFunction
  signature: : F -> G -> E
  body: Function.curry φ.toOpenPartialHomeomorph.symm

中文:
定义 implicitFunction
  签名: : F -> G -> E
  定义体: Function.curry φ.toOpenPartialHomeomorph.symm

Depends on / 依赖: Function, Function.curry, toOpenPartialHomeomorph, toOpenPartialHomeomorph.symm
-/
def implicitFunction : F -> G -> E :=
Function.curry φ.toOpenPartialHomeomorph.symm

/--
theorem `implicitFunction_def` / 定理 `implicitFunction_def`

English:
theorem implicitFunction_def
  proof: by
  rfl

中文:
定理 implicitFunction_def
  证明: by
  rfl
-/
theorem implicitFunction_def :
    implicitFunction φ = Function.curry (φ.hasStrictFDerivAt.toOpenPartialHomeomorph _).symm := by
  rfl

/--
lemma `implicitFunction_apply` / 引理 `implicitFunction_apply`

English:
lemma implicitFunction_apply
  given: {x : F} {y : G}
  proof: by
  rfl

@[simp]

中文:
引理 implicitFunction_apply
  条件: {x : F} {y : G}
  证明: by
  rfl

@[simp]
-/
lemma implicitFunction_apply {x : F} {y : G} :
    φ.implicitFunction x y = φ.toOpenPartialHomeomorph.symm (x, y) := by
  rfl

@[simp]
/--
theorem `toOpenPartialHomeomorph_coe` / 定理 `toOpenPartialHomeomorph_coe`

English:
theorem toOpenPartialHomeomorph_coe
  statement: ⇑φ.toOpenPartialHomeomorph = φ.prodFun
  proof: by
  rfl

中文:
定理 toOpenPartialHomeomorph_coe
  结论: ⇑φ.toOpenPartialHomeomorph = φ.prodFun
  证明: by
  rfl
-/
theorem toOpenPartialHomeomorph_coe : ⇑φ.toOpenPartialHomeomorph = φ.prodFun := by
  rfl

/--
theorem `toOpenPartialHomeomorph_apply` / 定理 `toOpenPartialHomeomorph_apply`

English:
theorem toOpenPartialHomeomorph_apply
  given: (x : E)
  proof: by
  rfl

中文:
定理 toOpenPartialHomeomorph_apply
  条件: (x : E)
  证明: by
  rfl
-/
theorem toOpenPartialHomeomorph_apply (x : E) :
    φ.toOpenPartialHomeomorph x = (φ.leftFun x, φ.rightFun x) := by
  rfl

/--
theorem `pt_mem_toOpenPartialHomeomorph_source` / 定理 `pt_mem_toOpenPartialHomeomorph_source`

English:
theorem pt_mem_toOpenPartialHomeomorph_source
  statement: φ.pt in φ.toOpenPartialHomeomorph.source
  proof: φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

中文:
定理 pt_mem_toOpenPartialHomeomorph_source
  结论: φ.pt in φ.toOpenPartialHomeomorph.source
  证明: φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

Depends on / 依赖: hasStrictFDerivAt, hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source, mem_toOpenPartialHomeomorph_source
-/
theorem pt_mem_toOpenPartialHomeomorph_source : φ.pt in φ.toOpenPartialHomeomorph.source :=
  φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

/--
theorem `map_pt_mem_toOpenPartialHomeomorph_target` / 定理 `map_pt_mem_toOpenPartialHomeomorph_target`

English:
theorem map_pt_mem_toOpenPartialHomeomorph_target
  proof: φ.toOpenPartialHomeomorph.map_source φ.pt_mem_toOpenPartialHomeomorph_source

中文:
定理 map_pt_mem_toOpenPartialHomeomorph_target
  证明: φ.toOpenPartialHomeomorph.map_source φ.pt_mem_toOpenPartialHomeomorph_source

Depends on / 依赖: map_source, pt_mem_toOpenPartialHomeomorph_source, toOpenPartialHomeomorph, toOpenPartialHomeomorph.map_source
-/
theorem map_pt_mem_toOpenPartialHomeomorph_target :
    (φ.leftFun φ.pt, φ.rightFun φ.pt) in φ.toOpenPartialHomeomorph.target :=
φ.toOpenPartialHomeomorph.map_source φ.pt_mem_toOpenPartialHomeomorph_source

/--
theorem `prodFun_implicitFunction` / 定理 `prodFun_implicitFunction`

English:
theorem prodFun_implicitFunction
  proof: φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h

@[deprecated (since := "2026-01-27")]
alias prod_map_implicitFunction := prodFun_implicitFunction

中文:
定理 prodFun_implicitFunction
  证明: φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h

@[deprecated (since := "2026-01-27")]
alias prod_map_implicitFunction := prodFun_implicitFunction

Depends on / 依赖: eventually_right_inverse, hasStrictFDerivAt, hasStrictFDerivAt.eventually_right_inverse.mono
-/
theorem prodFun_implicitFunction :
    forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2) = p :=
  φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h

@[deprecated (since := "2026-01-27")]
alias prod_map_implicitFunction := prodFun_implicitFunction

/--
theorem `leftFun_implicitFunction` / 定理 `leftFun_implicitFunction`

English:
theorem leftFun_implicitFunction
  proof: φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.fst

@[deprecated (since := "2026-01-27")]
alias left_map_implicitFunction := leftFun_implicitFunction

中文:
定理 leftFun_implicitFunction
  证明: φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.fst

@[deprecated (since := "2026-01-27")]
alias left_map_implicitFunction := leftFun_implicitFunction

Depends on / 依赖: Prod.fst, congr_arg, prodFun_implicitFunction, prodFun_implicitFunction.mono
-/
theorem leftFun_implicitFunction :
    forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2) = p.1 :=
  φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.fst

@[deprecated (since := "2026-01-27")]
alias left_map_implicitFunction := leftFun_implicitFunction

/--
theorem `rightFun_implicitFunction` / 定理 `rightFun_implicitFunction`

English:
theorem rightFun_implicitFunction
  proof: φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.snd

@[deprecated (since := "2026-01-27")]
alias right_map_implicitFunction := rightFun_implicitFunction

中文:
定理 rightFun_implicitFunction
  证明: φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.snd

@[deprecated (since := "2026-01-27")]
alias right_map_implicitFunction := rightFun_implicitFunction

Depends on / 依赖: Prod.snd, congr_arg, prodFun_implicitFunction, prodFun_implicitFunction.mono
-/
theorem rightFun_implicitFunction :
    forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 p.2) = p.2 :=
  φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.snd

@[deprecated (since := "2026-01-27")]
alias right_map_implicitFunction := rightFun_implicitFunction

/--
theorem `implicitFunction_apply_image` / 定理 `implicitFunction_apply_image`

English:
theorem implicitFunction_apply_image
  proof: φ.hasStrictFDerivAt.eventually_left_inverse

中文:
定理 implicitFunction_apply_image
  证明: φ.hasStrictFDerivAt.eventually_left_inverse

Depends on / 依赖: eventually_left_inverse, hasStrictFDerivAt, hasStrictFDerivAt.eventually_left_inverse
-/
theorem implicitFunction_apply_image :
    forallᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) = x :=
  φ.hasStrictFDerivAt.eventually_left_inverse

/--
theorem `leftFun_implicitFunction_eq_leftFun` / 定理 `leftFun_implicitFunction_eq_leftFun`

English:
theorem leftFun_implicitFunction_eq_leftFun
  statement: forallᶠ x in 𝓝 φ.pt,
  proof: by
  have := φ.leftFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

中文:
定理 leftFun_implicitFunction_eq_leftFun
  结论: 对任意ᶠ x in 𝓝 φ.pt,
  证明: by
  have := φ.leftFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

Depends on / 依赖: curry_nhds, eventually_map, hasStrictFDerivAt, hasStrictFDerivAt.map_nhds_eq_of_equiv, leftFun, leftFun_implicitFunction, leftFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds, map_nhds_eq_of_equiv, prodFun_apply, prod_inr_nhds, self_of_nhds
-/
theorem leftFun_implicitFunction_eq_leftFun : forallᶠ x in 𝓝 φ.pt,
    φ.leftFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.leftFun φ.pt := by
  have := φ.leftFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

/--
theorem `rightFun_implicitFunction_eq_rightFun` / 定理 `rightFun_implicitFunction_eq_rightFun`

English:
theorem rightFun_implicitFunction_eq_rightFun
  statement: forallᶠ x in 𝓝 φ.pt,
  proof: by
  have := φ.rightFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

中文:
定理 rightFun_implicitFunction_eq_rightFun
  结论: 对任意ᶠ x in 𝓝 φ.pt,
  证明: by
  have := φ.rightFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

Depends on / 依赖: curry_nhds, eventually_map, hasStrictFDerivAt, hasStrictFDerivAt.map_nhds_eq_of_equiv, leftFun, map_nhds_eq_of_equiv, prodFun_apply, prod_inr_nhds, rightFun_implicitFunction, rightFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds, self_of_nhds
-/
theorem rightFun_implicitFunction_eq_rightFun : forallᶠ x in 𝓝 φ.pt,
    φ.rightFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.rightFun x := by
  have := φ.rightFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

/--
theorem `leftFun_eq_iff_implicitFunction` / 定理 `leftFun_eq_iff_implicitFunction`

English:
theorem leftFun_eq_iff_implicitFunction
  statement: forallᶠ x in 𝓝 φ.pt,
  proof: by
  filter_upwards [φ.implicitFunction_apply_image, φ.leftFun_implicitFunction_eq_leftFun] with x _ _
  constructor <;> exact fun h => by rwa [← h]

中文:
定理 leftFun_eq_iff_implicitFunction
  结论: 对任意ᶠ x in 𝓝 φ.pt,
  证明: by
  filter_upwards [φ.implicitFunction_apply_image, φ.leftFun_implicitFunction_eq_leftFun] with x _ _
  constructor <;> exact fun h => by rwa [← h]

Depends on / 依赖: filter_upwards, implicitFunction_apply_image, leftFun_implicitFunction_eq_leftFun
-/
theorem leftFun_eq_iff_implicitFunction : forallᶠ x in 𝓝 φ.pt,
    φ.leftFun x = φ.leftFun φ.pt ↔ φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x) = x := by
  filter_upwards [φ.implicitFunction_apply_image, φ.leftFun_implicitFunction_eq_leftFun] with x _ _
  constructor <;> exact fun h => by rwa [← h]

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  statement: map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt)
  proof: show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map]; rw [φ.hasStrictFDerivAt.map_nhds_eq_of_equiv]; rw [map_fst_nhds]

中文:
定理 map_nhds_eq
  结论: map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt)
  证明: show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map]; rw [φ.hasStrictFDerivAt.map_nhds_eq_of_equiv]; rw [map_fst_nhds]

Depends on / 依赖: Prod.fst, hasStrictFDerivAt, hasStrictFDerivAt.map_nhds_eq_of_equiv, map_fst_nhds, map_map, map_nhds_eq_of_equiv, prodFun
-/
theorem map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt) :=
  show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map]; rw [φ.hasStrictFDerivAt.map_nhds_eq_of_equiv]; rw [map_fst_nhds]

/--
theorem `hasStrictFDerivAt_implicitFunction_fderiv` / 定理 `hasStrictFDerivAt_implicitFunction_fderiv`

English:
theorem hasStrictFDerivAt_implicitFunction_fderiv
  proof: by
  have := φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  convert! this
  exact this.hasFDerivAt.fderiv

中文:
定理 hasStrictFDerivAt_implicitFunction_fderiv
  证明: by
  have := φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  convert! this
  exact this.hasFDerivAt.fderiv

Depends on / 依赖: convert, fderiv, hasFDerivAt, hasStrictFDerivAt, hasStrictFDerivAt.to_localInverse.comp, hasStrictFDerivAt_const, hasStrictFDerivAt_id, prodMk, rightFun, this.hasFDerivAt.fderiv, to_localInverse
-/
theorem hasStrictFDerivAt_implicitFunction_fderiv :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt))
      (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)) (φ.rightFun φ.pt) := by
  have := φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  convert! this
  exact this.hasFDerivAt.fderiv

/--
theorem `differentiableAt_implicitFunction` / 定理 `differentiableAt_implicitFunction`

English:
theorem differentiableAt_implicitFunction
  given: (φ : ImplicitFunctionData 𝕜 E F G)
  proof: φ.hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt.differentiableAt

中文:
定理 differentiableAt_implicitFunction
  条件: (φ : ImplicitFunctionData 𝕜 E F G)
  证明: φ.hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hasStrictFDerivAt_implicitFunction_fderiv, hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt.differentiableAt
-/
theorem differentiableAt_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) :
    DifferentiableAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) :=
  φ.hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt.differentiableAt

/--
theorem `fderiv_implicitFunction_apply_eq_iff` / 定理 `fderiv_implicitFunction_apply_eq_iff`

English:
theorem fderiv_implicitFunction_apply_eq_iff
  given: (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E}
  proof: by
  unfold implicitFunction Function.curry toOpenPartialHomeomorph
  simp only [← HasStrictFDerivAt.localInverse_def]
  rw [φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
.fderiv] .hasFDerivAt ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  simp [ContinuousLinearEquiv.

中文:
定理 fderiv_implicitFunction_apply_eq_iff
  条件: (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E}
  证明: by
  unfold implicitFunction Function.curry toOpenPartialHomeomorph
  simp only [← HasStrictFDerivAt.localInverse_def]
  rw [φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
.fderiv] .hasFDerivAt ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  simp [ContinuousLinearEquiv.

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.symm_apply_eq, Function, Function.curry, HasStrictFDerivAt, HasStrictFDerivAt.localInverse_def, eq_comm, fderiv, hasFDerivAt, hasStrictFDerivAt, hasStrictFDerivAt.to_localInverse.comp, hasStrictFDerivAt_const, hasStrictFDerivAt_id, implicitFunction, leftDeriv, localInverse_def, prodMk, rightDeriv, rightFun, symm_apply_eq
-/
theorem fderiv_implicitFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} :
    fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x = y ↔
      φ.leftDeriv y = 0 ∧ φ.rightDeriv y = x := by
  unfold implicitFunction Function.curry toOpenPartialHomeomorph
  simp only [← HasStrictFDerivAt.localInverse_def]
  rw [φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
.fderiv] .hasFDerivAt ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  simp [ContinuousLinearEquiv.symm_apply_eq, @eq_comm _ (φ.leftDeriv _),
    @eq_comm _ (φ.rightDeriv _)]

@[simp]
/--
theorem `leftDeriv_fderiv_implicitFunction` / 定理 `leftDeriv_fderiv_implicitFunction`

English:
theorem leftDeriv_fderiv_implicitFunction
  given: (φ : ImplicitFunctionData 𝕜 E F G) (x : G)
  proof: by
.left exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl

@[simp]

中文:
定理 leftDeriv_fderiv_implicitFunction
  条件: (φ : ImplicitFunctionData 𝕜 E F G) (x : G)
  证明: by
.left exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl

@[simp]

Depends on / 依赖: fderiv_implicitFunction_apply_eq_iff, fderiv_implicitFunction_apply_eq_iff.mp
-/
theorem leftDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.leftDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = 0 := by
.left exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl

@[simp]
/--
theorem `rightDeriv_fderiv_implicitFunction` / 定理 `rightDeriv_fderiv_implicitFunction`

English:
theorem rightDeriv_fderiv_implicitFunction
  given: (φ : ImplicitFunctionData 𝕜 E F G) (x : G)
  proof: by
.right exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl

中文:
定理 rightDeriv_fderiv_implicitFunction
  条件: (φ : ImplicitFunctionData 𝕜 E F G) (x : G)
  证明: by
.right exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl

Depends on / 依赖: fderiv_implicitFunction_apply_eq_iff, fderiv_implicitFunction_apply_eq_iff.mp
-/
theorem rightDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.rightDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = x := by
.right exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl

/--
theorem `hasStrictFDerivAt_implicitFunction` / 定理 `hasStrictFDerivAt_implicitFunction`

English:
theorem hasStrictFDerivAt_implicitFunction
  statement: (g'inv : G ->L[𝕜] E)
  proof: by
  convert! φ.hasStrictFDerivAt_implicitFunction_fderiv
  ext1 x
  rw [eq_comm]; rw [fderiv_implicitFunction_apply_eq_iff]
  simp_all [DFunLike.ext_iff]

@[deprecated (since := "2026-01-27")]
alias implicitFunction_hasStrictFDerivAt := hasStrictFDerivAt_implicitFunction

中文:
定理 hasStrictFDerivAt_implicitFunction
  结论: (g'inv : G ->L[𝕜] E)
  证明: by
  convert! φ.hasStrictFDerivAt_implicitFunction_fderiv
  ext1 x
  rw [eq_comm]; rw [fderiv_implicitFunction_apply_eq_iff]
  simp_all [DFunLike.ext_iff]

@[deprecated (since := "2026-01-27")]
alias implicitFunction_hasStrictFDerivAt := hasStrictFDerivAt_implicitFunction

Depends on / 依赖: DFunLike, DFunLike.ext_iff, convert, eq_comm, ext_iff, fderiv_implicitFunction_apply_eq_iff, hasStrictFDerivAt_implicitFunction_fderiv
-/
theorem hasStrictFDerivAt_implicitFunction (g'inv : G ->L[𝕜] E)
    (hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 𝕜 G)
    (hg'invf : φ.leftDeriv.comp g'inv = 0) :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun φ.pt) := by
  convert! φ.hasStrictFDerivAt_implicitFunction_fderiv
  ext1 x
  rw [eq_comm]; rw [fderiv_implicitFunction_apply_eq_iff]
  simp_all [DFunLike.ext_iff]

@[deprecated (since := "2026-01-27")]
alias implicitFunction_hasStrictFDerivAt := hasStrictFDerivAt_implicitFunction

/--
theorem `map_implicitFunction_nhdsWithin_preimage` / 定理 `map_implicitFunction_nhdsWithin_preimage`

English:
theorem map_implicitFunction_nhdsWithin_preimage
  statement: (φ : ImplicitFunctionData 𝕜 E F G)
  proof: by
  have H : φ.implicitFunction (φ.leftFun φ.pt) =
      φ.toOpenPartialHomeomorph.symm ∘ (φ.leftFun φ.pt, ·) := rfl
  rw [H]; rw [← Filter.map_map]; rw [(isInducing_prodMkRight _).map_nhdsWithin_eq]; rw [← Set.singleton_prod]; rw [OpenPartialHomeomorph.map_nhdsWithin_eq]; rw [← prodFun_apply]; rw 

中文:
定理 map_implicitFunction_nhdsWithin_preimage
  结论: (φ : ImplicitFunctionData 𝕜 E F G)
  证明: by
  have H : φ.implicitFunction (φ.leftFun φ.pt) =
      φ.toOpenPartialHomeomorph.symm ∘ (φ.leftFun φ.pt, ·) := rfl
  rw [H]; rw [← Filter.map_map]; rw [(isInducing_prodMkRight _).map_nhdsWithin_eq]; rw [← Set.singleton_prod]; rw [OpenPartialHomeomorph.map_nhdsWithin_eq]; rw [← prodFun_apply]; rw 

Depends on / 依赖: Filter, Filter.map_map, OpenPartialHomeomorph, OpenPartialHomeomorph.image_source_inter_eq, OpenPartialHomeomorph.map_nhdsWithin_eq, Set.singleton_prod, conv_rhs, image_source_inter_eq, implicitFunction, isInducing_prodMkRight, leftFun, leftInvOn, map_map, map_nhdsWithin_eq, prodFun_apply, pt_mem_toOpenPartialHomeomorph_source, singleton_prod, toOpenPartialHomeomorph, toOpenPartialHomeomorph.leftInvOn, toOpenPartialHomeomorph.symm
-/
theorem map_implicitFunction_nhdsWithin_preimage (φ : ImplicitFunctionData 𝕜 E F G)
    (s : Set E) :
    (𝓝[φ.implicitFunction (φ.leftFun φ.pt) ⁻¹' s] (φ.rightFun φ.pt)).map
      (φ.implicitFunction (φ.leftFun φ.pt)) = 𝓝[s inter φ.leftFun ⁻¹' {φ.leftFun φ.pt}] φ.pt := by
  have H : φ.implicitFunction (φ.leftFun φ.pt) =
      φ.toOpenPartialHomeomorph.symm ∘ (φ.leftFun φ.pt, ·) := rfl
  rw [H]; rw [← Filter.map_map]; rw [(isInducing_prodMkRight _).map_nhdsWithin_eq]; rw [← Set.singleton_prod]; rw [OpenPartialHomeomorph.map_nhdsWithin_eq]; rw [← prodFun_apply]; rw [← toOpenPartialHomeomorph_coe]; rw [φ.toOpenPartialHomeomorph.leftInvOn φ.pt_mem_toOpenPartialHomeomorph_source]; rw [OpenPartialHomeomorph.image_source_inter_eq']
  · conv_rhs =>
      rw [← φ.toOpenPartialHomeomorph.nhdsWithin_source_inter
        φ.pt_mem_toOpenPartialHomeomorph_source]
    congr 1
    ext x
    suffices x in φ.toOpenPartialHomeomorph.source -> φ.leftFun x = φ.leftFun φ.pt ->
        (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, φ.rightFun x) in s ↔ x in s) by
      simpa [@and_comm (_ = _)]
    intro hxs hx_eq
    rw [← hx_eq]; rw [← prodFun_apply]; rw [← toOpenPartialHomeomorph_coe]; rw [φ.toOpenPartialHomeomorph.leftInvOn hxs]
  · exact φ.toOpenPartialHomeomorph.mapsTo φ.pt_mem_toOpenPartialHomeomorph_source

/--
theorem `eventuallyEq_implicitFunction` / 定理 `eventuallyEq_implicitFunction`

English:
theorem eventuallyEq_implicitFunction
  statement: {ψ : F -> G -> E}
  proof: HasStrictFDerivAt.localInverse_unique _ h

中文:
定理 eventuallyEq_implicitFunction
  结论: {ψ : F -> G -> E}
  证明: HasStrictFDerivAt.localInverse_unique _ h

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.localInverse_unique, localInverse_unique
-/
theorem eventuallyEq_implicitFunction {ψ : F -> G -> E}
    (h : forallᶠ x in 𝓝 φ.pt, ψ (φ.leftFun x) (φ.rightFun x) = x) :
    Function.uncurry ψ =ᶠ[𝓝 (φ.prodFun φ.pt)] Function.uncurry φ.implicitFunction :=
  HasStrictFDerivAt.localInverse_unique _ h

end ImplicitFunctionData

namespace HasStrictFDerivAt

section Complemented

/-!
### Case of a complemented kernel

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` and a point `a : E` such that `f` is strictly differentiable at `a`, its derivative `f'`
is surjective and the kernel of `f'` is a complemented subspace of `E` (i.e., it has a closed
complementary subspace). Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {f : E -> F} {f' : E ->L[𝕜] F} {a : E}

section Defs

variable (f f')

/-- Data used to apply the generic implicit function theorem to the case of a strictly
differentiable map such that its derivative is surjective and has a complemented kernel. -/
@[simp]
/--
Definition of `implicitFunctionDataOfComplemented` / `implicitFunctionDataOfComplemented` 的定义

English:
definition implicitFunctionDataOfComplemented
  signature: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  body: f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  range_leftDeriv := hf'
  r

中文:
定义 implicitFunctionDataOfComplemented
  签名: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  定义体: f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  range_leftDeriv := hf'
  r
-/
def implicitFunctionDataOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : ImplicitFunctionData 𝕜 E F f'.ker where
  leftFun := f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  range_leftDeriv := hf'
  range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
  isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker)

/--
Definition of `implicitToOpenPartialHomeomorphOfComplemented` / `implicitToOpenPartialHomeomorphOfComplemented` 的定义

English:
definition implicitToOpenPartialHomeomorphOfComplemented
  signature: (hf : HasStrictFDerivAt f f' a)
  body: (implicitFunctionDataOfComplemented f f' hf hf' hker).toOpenPartialHomeomorph

中文:
定义 implicitToOpenPartialHomeomorphOfComplemented
  签名: (hf : HasStrictFDerivAt f f' a)
  定义体: (implicitFunctionDataOfComplemented f f' hf hf' hker).toOpenPartialHomeomorph

Depends on / 依赖: implicitFunctionDataOfComplemented, toOpenPartialHomeomorph
-/
def implicitToOpenPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).toOpenPartialHomeomorph

/--
Definition of `implicitFunctionOfComplemented` / `implicitFunctionOfComplemented` 的定义

English:
definition implicitFunctionOfComplemented
  signature: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  body: (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction

中文:
定义 implicitFunctionOfComplemented
  签名: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  定义体: (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction

Depends on / 依赖: implicitFunction, implicitFunctionDataOfComplemented
-/
def implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : F -> f'.ker -> E :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction

end Defs

@[simp]
/--
theorem `implicitToOpenPartialHomeomorphOfComplemented_fst` / 定理 `implicitToOpenPartialHomeomorphOfComplemented_fst`

English:
theorem implicitToOpenPartialHomeomorphOfComplemented_fst
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: by
  rfl

中文:
定理 implicitToOpenPartialHomeomorphOfComplemented_fst
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: by
  rfl
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (x : E) :
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x := by
  rfl

/--
theorem `implicitToOpenPartialHomeomorphOfComplemented_apply` / 定理 `implicitToOpenPartialHomeomorphOfComplemented_apply`

English:
theorem implicitToOpenPartialHomeomorphOfComplemented_apply
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: by
  rfl

@[simp]

中文:
定理 implicitToOpenPartialHomeomorphOfComplemented_apply
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: by
  rfl

@[simp]
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : E) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker y =
      (f y, Classical.choose hker (y - a)) := by
  rfl

@[simp]
/--
theorem `implicitToOpenPartialHomeomorphOfComplemented_apply_ker` / 定理 `implicitToOpenPartialHomeomorphOfComplemented_apply_ker`

English:
theorem implicitToOpenPartialHomeomorphOfComplemented_apply_ker
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: by
  simp only [implicitToOpenPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]

@[simp]

中文:
定理 implicitToOpenPartialHomeomorphOfComplemented_apply_ker
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: by
  simp only [implicitToOpenPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, add_sub_cancel_right, choose_spec, implicitToOpenPartialHomeomorphOfComplemented_apply
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : f'.ker) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicitToOpenPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]

@[simp]
/--
theorem `implicitToOpenPartialHomeomorphOfComplemented_self` / 定理 `implicitToOpenPartialHomeomorphOfComplemented_self`

English:
theorem implicitToOpenPartialHomeomorphOfComplemented_self
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: by
  simp [hf.implicitToOpenPartialHomeomorphOfComplemented_apply]

中文:
定理 implicitToOpenPartialHomeomorphOfComplemented_self
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: by
  simp [hf.implicitToOpenPartialHomeomorphOfComplemented_apply]

Depends on / 依赖: hf.implicitToOpenPartialHomeomorphOfComplemented_apply, implicitToOpenPartialHomeomorphOfComplemented_apply
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0) := by
  simp [hf.implicitToOpenPartialHomeomorphOfComplemented_apply]

/--
theorem `mem_implicitToOpenPartialHomeomorphOfComplemented_source` / 定理 `mem_implicitToOpenPartialHomeomorphOfComplemented_source`

English:
theorem mem_implicitToOpenPartialHomeomorphOfComplemented_source
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

中文:
定理 mem_implicitToOpenPartialHomeomorphOfComplemented_source
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

Depends on / 依赖: ImplicitFunctionData, ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source, pt_mem_toOpenPartialHomeomorph_source
-/
theorem mem_implicitToOpenPartialHomeomorphOfComplemented_source (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    a in (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).source :=
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

/--
theorem `mem_implicitToOpenPartialHomeomorphOfComplemented_target` / 定理 `mem_implicitToOpenPartialHomeomorphOfComplemented_target`

English:
theorem mem_implicitToOpenPartialHomeomorphOfComplemented_target
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using
(hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).map_source
      hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

中文:
定理 mem_implicitToOpenPartialHomeomorphOfComplemented_target
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using
(hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).map_source
      hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

Depends on / 依赖: hf.implicitToOpenPartialHomeomorphOfComplemented, hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source, implicitToOpenPartialHomeomorphOfComplemented, implicitToOpenPartialHomeomorphOfComplemented_self, map_source, mem_implicitToOpenPartialHomeomorphOfComplemented_source
-/
theorem mem_implicitToOpenPartialHomeomorphOfComplemented_target (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    (f a, (0 : f'.ker)) in
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target := by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using
(hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).map_source
      hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

/--
theorem `map_implicitFunctionOfComplemented_eq` / 定理 `map_implicitFunctionOfComplemented_eq`

English:
theorem map_implicitFunctionOfComplemented_eq
  statement: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h

中文:
定理 map_implicitFunctionOfComplemented_eq
  结论: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h

Depends on / 依赖: Prod.fst, congr_arg, eventually_right_inverse, hf.implicitToOpenPartialHomeomorphOfComplemented, hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target, implicitToOpenPartialHomeomorphOfComplemented, mem_implicitToOpenPartialHomeomorphOfComplemented_target
-/
theorem map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    forallᶠ p : F × f'.ker in 𝓝 (f a, 0),
      f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h

/--
theorem `eq_implicitFunctionOfComplemented` / 定理 `eq_implicitFunctionOfComplemented`

English:
theorem eq_implicitFunctionOfComplemented
  statement: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image

@[simp]

中文:
定理 eq_implicitFunctionOfComplemented
  结论: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image

@[simp]

Depends on / 依赖: implicitFunctionDataOfComplemented, implicitFunction_apply_image
-/
theorem eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    forallᶠ x in 𝓝 a, hf.implicitFunctionOfComplemented f f' hf' hker (f x)
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).snd = x :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image

@[simp]
/--
theorem `implicitFunctionOfComplemented_apply_image` / 定理 `implicitFunctionOfComplemented_apply_image`

English:
theorem implicitFunctionOfComplemented_apply_image
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using!
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)

中文:
定理 implicitFunctionOfComplemented_apply_image
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using!
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)

Depends on / 依赖: hf.implicitToOpenPartialHomeomorphOfComplemented, hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source, implicitToOpenPartialHomeomorphOfComplemented, implicitToOpenPartialHomeomorphOfComplemented_self, left_inv, mem_implicitToOpenPartialHomeomorphOfComplemented_source
-/
theorem implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    hf.implicitFunctionOfComplemented f f' hf' hker (f a) 0 = a := by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using!
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `to_implicitFunctionOfComplemented` / 定理 `to_implicitFunctionOfComplemented`

English:
theorem to_implicitFunctionOfComplemented
  statement: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: by
  convert!
    (implicitFunctionDataOfComplemented f f' hf hf' hker).hasStrictFDerivAt_implicitFunction
      f'.ker.subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.c

中文:
定理 to_implicitFunctionOfComplemented
  结论: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: by
  convert!
    (implicitFunctionDataOfComplemented f f' hf hf' hker).hasStrictFDerivAt_implicitFunction
      f'.ker.subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.c

Depends on / 依赖: Classical, Classical.choose_spec, ContinuousLinearMap, ContinuousLinearMap.apply_val_ker, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, Submodule, Submodule.coe_subtype, Submodule.coe_subtypeL, apply_val_ker, choose_spec, coe_subtype, coe_subtypeL, comp_apply, convert, hasStrictFDerivAt_implicitFunction, id_apply, implicitFunctionDataOfCom, implicitFunctionDataOfComplemented, ker.subtypeL
-/
theorem to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitFunctionOfComplemented f f' hf' hker (f a))
      f'.ker.subtypeL 0 := by
  convert!
    (implicitFunctionDataOfComplemented f f' hf hf' hker).hasStrictFDerivAt_implicitFunction
      f'.ker.subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
      ContinuousLinearMap.id_apply]
  swap
  · ext
    simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
      ContinuousLinearMap.apply_val_ker, zero_apply]
  simp only [implicitFunctionDataOfComplemented, map_sub, sub_self]

end Complemented

/-!
### Finite-dimensional case

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` from a Banach normed space to a finite-dimensional space.
Take a point `a : E` such that `f` is strictly differentiable at `a` and its derivative `f'`
is surjective. Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

This version deduces that `ker f'` is a complemented subspace from the fact that `F` is a finite
dimensional space, then applies the previous version.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

section FiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E -> F) (f' : E ->L[𝕜] F) {a : E}

/--
Definition of `implicitToOpenPartialHomeomorph` / `implicitToOpenPartialHomeomorph` 的定义

English:
definition implicitToOpenPartialHomeomorph
  signature: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  body: have := FiniteDimensional.complete 𝕜 F
  hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range

中文:
定义 implicitToOpenPartialHomeomorph
  签名: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  定义体: have := FiniteDimensional.complete 𝕜 F
  hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, hf.implicitToOpenPartialHomeomorphOfComplemented, implicitToOpenPartialHomeomorphOfComplemented, ker_closedComplemented_of_finiteDimensional_range
-/
def implicitToOpenPartialHomeomorph (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  have := FiniteDimensional.complete 𝕜 F
  hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range

/--
Definition of `implicitFunction` / `implicitFunction` 的定义

English:
definition implicitFunction
  signature: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  body: Function.curry (hf.implicitToOpenPartialHomeomorph f f' hf').symm

中文:
定义 implicitFunction
  签名: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  定义体: Function.curry (hf.implicitToOpenPartialHomeomorph f f' hf').symm

Depends on / 依赖: Function, Function.curry, hf.implicitToOpenPartialHomeomorph, implicitToOpenPartialHomeomorph
-/
def implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) : F -> f'.ker -> E :=
Function.curry (hf.implicitToOpenPartialHomeomorph f f' hf').symm

variable {f f'}

@[simp]
/--
theorem `implicitToOpenPartialHomeomorph_fst` / 定理 `implicitToOpenPartialHomeomorph_fst`

English:
theorem implicitToOpenPartialHomeomorph_fst
  statement: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: by
  rfl

@[simp]

中文:
定理 implicitToOpenPartialHomeomorph_fst
  结论: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: by
  rfl

@[simp]
-/
theorem implicitToOpenPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (x : E) : (hf.implicitToOpenPartialHomeomorph f f' hf' x).fst = f x := by
  rfl

@[simp]
/--
theorem `implicitToOpenPartialHomeomorph_apply_ker` / 定理 `implicitToOpenPartialHomeomorph_apply_ker`

English:
theorem implicitToOpenPartialHomeomorph_apply_ker
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_apply_ker ..

@[simp]

中文:
定理 implicitToOpenPartialHomeomorph_apply_ker
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_apply_ker ..

@[simp]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, implicitToOpenPartialHomeomorphOfComplemented_apply_ker
-/
theorem implicitToOpenPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (y : f'.ker) :
    hf.implicitToOpenPartialHomeomorph f f' hf' (y + a) = (f (y + a), y) :=
  have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_apply_ker ..

@[simp]
/--
theorem `implicitToOpenPartialHomeomorph_self` / 定理 `implicitToOpenPartialHomeomorph_self`

English:
theorem implicitToOpenPartialHomeomorph_self
  given: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_self ..

中文:
定理 implicitToOpenPartialHomeomorph_self
  条件: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_self ..

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, implicitToOpenPartialHomeomorphOfComplemented_self
-/
theorem implicitToOpenPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicitToOpenPartialHomeomorph f f' hf' a = (f a, 0) :=
  have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_self ..

/--
theorem `mem_implicitToOpenPartialHomeomorph_source` / 定理 `mem_implicitToOpenPartialHomeomorph_source`

English:
theorem mem_implicitToOpenPartialHomeomorph_source
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: have := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

中文:
定理 mem_implicitToOpenPartialHomeomorph_source
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: have := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, ImplicitFunctionData, ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source, complete, pt_mem_toOpenPartialHomeomorph_source
-/
theorem mem_implicitToOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) : a in (hf.implicitToOpenPartialHomeomorph f f' hf').source :=
  have := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

/--
theorem `mem_implicitToOpenPartialHomeomorph_target` / 定理 `mem_implicitToOpenPartialHomeomorph_target`

English:
theorem mem_implicitToOpenPartialHomeomorph_target
  statement: (hf : HasStrictFDerivAt f f' a)
  proof: have := FiniteDimensional.complete 𝕜 F
  mem_implicitToOpenPartialHomeomorphOfComplemented_target ..

中文:
定理 mem_implicitToOpenPartialHomeomorph_target
  结论: (hf : HasStrictFDerivAt f f' a)
  证明: have := FiniteDimensional.complete 𝕜 F
  mem_implicitToOpenPartialHomeomorphOfComplemented_target ..

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, mem_implicitToOpenPartialHomeomorphOfComplemented_target
-/
theorem mem_implicitToOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) :
    (f a, (0 : f'.ker)) in (hf.implicitToOpenPartialHomeomorph f f' hf').target :=
  have := FiniteDimensional.complete 𝕜 F
  mem_implicitToOpenPartialHomeomorphOfComplemented_target ..

/--
theorem `tendsto_implicitFunction` / 定理 `tendsto_implicitFunction`

English:
theorem tendsto_implicitFunction
  statement: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {α : Type*}
  proof: by
  refine ((hf.implicitToOpenPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToOpenPartialHomeomorph_source hf')).comp ?_
  rw [implicitToOpenPartialHomeomorph_self]
  exact h₁.prodMk_nhds h₂

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction

中文:
定理 tendsto_implicitFunction
  结论: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {α : 类型}
  证明: by
  refine ((hf.implicitToOpenPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToOpenPartialHomeomorph_source hf')).comp ?_
  rw [implicitToOpenPartialHomeomorph_self]
  exact h₁.prodMk_nhds h₂

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction

Depends on / 依赖: hf.implicitToOpenPartialHomeomorph, hf.mem_implicitToOpenPartialHomeomorph_source, implicitToOpenPartialHomeomorph, implicitToOpenPartialHomeomorph_self, mem_implicitToOpenPartialHomeomorph_source, prodMk_nhds, tendsto_symm
-/
theorem tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {α : Type*}
    {l : Filter α} {g₁ : α -> F} {g₂ : α -> f'.ker} (h₁ : Tendsto g₁ l (𝓝 <| f a))
    (h₂ : Tendsto g₂ l (𝓝 0)) :
    Tendsto (fun t => hf.implicitFunction f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine ((hf.implicitToOpenPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToOpenPartialHomeomorph_source hf')).comp ?_
  rw [implicitToOpenPartialHomeomorph_self]
  exact h₁.prodMk_nhds h₂

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction

/--
theorem `map_implicitFunction_eq` / 定理 `map_implicitFunction_eq`

English:
theorem map_implicitFunction_eq
  given: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: have := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..

@[simp]

中文:
定理 map_implicitFunction_eq
  条件: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: have := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..

@[simp]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, map_implicitFunctionOfComplemented_eq
-/
theorem map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    forallᶠ p : F × f'.ker in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p.2) = p.1 :=
  have := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..

@[simp]
/--
theorem `implicitFunction_apply_image` / 定理 `implicitFunction_apply_image`

English:
theorem implicitFunction_apply_image
  given: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: by
  have := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image

中文:
定理 implicitFunction_apply_image
  条件: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: by
  have := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, implicitFunctionOfComplemented_apply_image
-/
theorem implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a := by
  have := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image

/--
theorem `eq_implicitFunction` / 定理 `eq_implicitFunction`

English:
theorem eq_implicitFunction
  given: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: have := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..

中文:
定理 eq_implicitFunction
  条件: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: have := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, eq_implicitFunctionOfComplemented
-/
theorem eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    forallᶠ x in 𝓝 a,
      hf.implicitFunction f f' hf' (f x) (hf.implicitToOpenPartialHomeomorph f f' hf' x).snd = x :=
  have := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..

/--
theorem `to_implicitFunction` / 定理 `to_implicitFunction`

English:
theorem to_implicitFunction
  given: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  proof: have := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..

中文:
定理 to_implicitFunction
  条件: (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
  证明: have := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete, to_implicitFunctionOfComplemented
-/
theorem to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) f'.ker.subtypeL 0 :=
  have := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..

end FiniteDimensional

end HasStrictFDerivAt

end
