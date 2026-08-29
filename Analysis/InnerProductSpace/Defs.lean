/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic

/-!
# Inner product spaces

This file defines inner product spaces.
Hilbert spaces can be obtained using the set of assumptions
`[RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]`.
For convenience, a variable alias `HilbertSpace` is provided so that one can write
`variable? [HilbertSpace 𝕜 E]` and get this as a suggestion.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `RCLike` typeclass.

Rather than defining the norm on an inner product space to be `√(re ⟪x, x⟫)`, we assume that a norm
is given, and add a hypothesis stating that `‖x‖ ^ 2 = re ⟪x, x⟫`. This makes it possible to
handle spaces where the norm is equal, but not defeq, to the square root of the
inner product. Defining a norm starting from an inner product is handled via the
`InnerProductSpace.Core` structure.

This file is intended to contain the minimal amount of machinery needed to define inner product
spaces, and to construct a normed space from an inner product space. Many more general lemmas can
be found in `Analysis.InnerProductSpace.Basic`. For the specific construction of an inner product
structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `EuclideanSpace` in
`Analysis.InnerProductSpace.PiL2`.

## Main results

- We define the class `InnerProductSpace 𝕜 E` extending `NormedSpace 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `RCLike` typeclass.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

@[expose] public section


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp Bornology

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

/--
Definition of `Inner` / `Inner` 的定义

English:
class Inner
  parameters: (𝕜 E : Type*)
  axioms and operations (1):
    - inner((𝕜)) : E -> E -> 𝕜

中文:
类 Inner
  参数: (𝕜 E : 类型)
  公理与运算 (1 个):
    - inner((𝕜)) : E -> E -> 𝕜
-/
class Inner (𝕜 E : Type*) where
  /-- The inner product function. -/
  inner (𝕜) : E -> E -> 𝕜

export Inner (inner)

/-- The inner product with values in `𝕜`. -/
scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y

section Notations

/-- The inner product with values in `ℝ`. -/
scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => inner Real x y

/-- The inner product with values in `ℂ`. -/
scoped[ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => inner Complex x y

end Notations

/-- A (pre) inner product space is a vector space with an additional operation called inner product.
The (semi)norm could be derived from the inner product, instead we require the existence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`.
-/
@[wikidata Q214159]
/--
Definition of `InnerProductSpace` / `InnerProductSpace` 的定义

English:
class InnerProductSpace
  parameters: (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E]
  axioms and operations (4):
    - norm_sq_eq_re_inner : forall x : E, ‖x‖ ^ 2 = re (inner x x)
    - conj_inner_symm : forall x y, conj (inner y x) = inner x y
    - add_left : forall x y z, inner (x + y) z = inner x z + inner y z
    - smul_left : forall x y r, inner (r • x) y = conj r * inner x y

中文:
类 InnerProductSpace
  参数: (𝕜 : 类型) (E : 类型) [RCLike 𝕜] [SeminormedAddCommGroup E]
  公理与运算 (4 个):
    - norm_sq_eq_re_inner : 对任意 x : E, ‖x‖ ^ 2 = re (inner x x)
    - conj_inner_symm : 对任意 x y, conj (inner y x) = inner x y
    - add_left : 对任意 x y z, inner (x + y) z = inner x z + inner y z
    - smul_left : 对任意 x y r, inner (r • x) y = conj r * inner x y
-/
class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
    NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_re_inner : forall x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm : forall x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : forall x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : forall x y r, inner (r • x) y = conj r * inner x y

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`InnerProductSpace.Core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `InnerProductSpace`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/--
Definition of `PreInnerProductSpace.Core` / `PreInnerProductSpace.Core` 的定义

English:
structure PreInnerProductSpace.Core
  parameters: (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  extends: Inner 𝕜 F
  axioms and operations (4):
    - conj_inner_symm(x y) : conj (inner y x) = inner x y
    - re_inner_nonneg(x) : 0 <= re (inner x x)
    - add_left(x y z) : inner (x + y) z = inner x z + inner y z
    - smul_left(x y r) : inner (r • x) y = conj r * inner x y

中文:
结构 PreInnerProductSpace.Core
  参数: (𝕜 : 类型) (F : 类型) [RCLike 𝕜] [AddCommGroup F]
  继承: Inner 𝕜 F
  公理与运算 (4 个):
    - conj_inner_symm(x y) : conj (inner y x) = inner x y
    - re_inner_nonneg(x) : 0 <= re (inner x x)
    - add_left(x y z) : inner (x + y) z = inner x z + inner y z
    - smul_left(x y r) : inner (r • x) y = conj r * inner x y
-/
structure PreInnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
    [Module 𝕜 F] extends Inner 𝕜 F where
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm x y : conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  re_inner_nonneg x : 0 <= re (inner x x)
  /-- The inner product is additive in the first coordinate. -/
  add_left x y z : inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left x y r : inner (r • x) y = conj r * inner x y

attribute [class] PreInnerProductSpace.Core

/--
Definition of `InnerProductSpace.Core` / `InnerProductSpace.Core` 的定义

English:
structure InnerProductSpace.Core
  parameters: (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  extends: PreInnerProductSpace.Core 𝕜 F
  axioms and operations (1):
    - definite : forall x, inner x x = 0 -> x = 0

中文:
结构 InnerProductSpace.Core
  参数: (𝕜 : 类型) (F : 类型) [RCLike 𝕜] [AddCommGroup F]
  继承: PreInnerProductSpace.Core 𝕜 F
  公理与运算 (1 个):
    - definite : 对任意 x, inner x x = 0 -> x = 0
-/
structure InnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends PreInnerProductSpace.Core 𝕜 F where
  /-- The inner product is positive definite. -/
  definite : forall x, inner x x = 0 -> x = 0

/- We set `InnerProductSpace.Core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

instance (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
    [Module 𝕜 F] [cd : InnerProductSpace.Core 𝕜 F] : PreInnerProductSpace.Core 𝕜 F where
  inner := cd.inner
  conj_inner_symm := cd.conj_inner_symm
  re_inner_nonneg := cd.re_inner_nonneg
  add_left := cd.add_left
  smul_left := cd.smul_left

/-- Define `PreInnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemmas about
`PreInnerProductSpace.Core` for `PreInnerProductSpace`s. Note that the `Seminorm` instance provided
by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
@[instance_reducible]
/--
Definition of `PreInnerProductSpace.toCore` / `PreInnerProductSpace.toCore` 的定义

English:
definition PreInnerProductSpace.toCore
  signature: [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E]
  body: c
  re_inner_nonneg x := by rw [← InnerProductSpace.norm_sq_eq_re_inner]; apply sq_nonneg

中文:
定义 PreInnerProductSpace.toCore
  签名: [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E]
  定义体: c
  re_inner_nonneg x := by rw [← InnerProductSpace.norm_sq_eq_re_inner]; apply sq_nonneg
-/
def PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    PreInnerProductSpace.Core 𝕜 E where
  __ := c
  re_inner_nonneg x := by rw [← InnerProductSpace.norm_sq_eq_re_inner]; apply sq_nonneg

/-- Define `InnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemmas about
`InnerProductSpace.Core` for `InnerProductSpace`s. Note that the `Norm` instance provided by
`InnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
@[instance_reducible]
/--
Definition of `InnerProductSpace.toCore` / `InnerProductSpace.toCore` 的定义

English:
definition InnerProductSpace.toCore
  signature: [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E]
  body: { c with
    re_inner_nonneg := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_re_inner]
      apply sq_nonneg
    definite := fun x hx =>
norm_eq_zero.1 eq_zero_of_pow_eq_zero (n := 2) by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x]; rw [hx]; rw [map_zero] }

中文:
定义 InnerProductSpace.toCore
  签名: [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E]
  定义体: { c with
    re_inner_nonneg := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_re_inner]
      apply sq_nonneg
    definite := fun x hx =>
norm_eq_zero.1 eq_zero_of_pow_eq_zero (n := 2) by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x]; rw [hx]; rw [map_zero] }

Depends on / 依赖: InnerProductSpace, InnerProductSpace.norm_sq_eq_re_inner, definite, eq_zero_of_pow_eq_zero, map_zero, norm_eq_zero, norm_sq_eq_re_inner, re_inner_nonneg, sq_nonneg
-/
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    re_inner_nonneg := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_re_inner]
      apply sq_nonneg
    definite := fun x hx =>
norm_eq_zero.1 eq_zero_of_pow_eq_zero (n := 2) by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x]; rw [hx]; rw [map_zero] }

namespace InnerProductSpace.Core

section PreInnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Local notation for `RCLike.ext_iff 𝕜` -/
local notation "ext_iff" => @RCLike.ext_iff 𝕜 _

/-- Local notation for `starRingEnd _` -/
local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `PreInnerProductSpace.Core` structure. We can't reuse
`PreInnerProductSpace.Core.toInner` because it takes `PreInnerProductSpace.Core` as an explicit
argument. -/
@[instance_reducible]
/--
Definition of `toPreInner'` / `toPreInner'` 的定义

English:
definition toPreInner'
  signature: : Inner 𝕜 F
  body: c.toInner

中文:
定义 toPreInner'
  签名: : Inner 𝕜 F
  定义体: c.toInner

Depends on / 依赖: c.toInner, toInner
-/
def toPreInner' : Inner 𝕜 F :=
  c.toInner

attribute [local instance] toPreInner'

/--
Definition of `normSq` / `normSq` 的定义

English:
definition normSq
  signature: (x : F)
  body: re ⟪x, x⟫

中文:
定义 normSq
  签名: (x : F)
  定义体: re ⟪x, x⟫
-/
def normSq (x : F) :=
  re ⟪x, x⟫

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
local notation "normSqF" => @normSq 𝕜 F _ _ _ _

/--
theorem `inner_conj_symm` / 定理 `inner_conj_symm`

English:
theorem inner_conj_symm
  given: (x y : F)
  statement: ⟪y, x⟫† = ⟪x, y⟫
  proof: c.conj_inner_symm x y

中文:
定理 inner_conj_symm
  条件: (x y : F)
  结论: ⟪y, x⟫† = ⟪x, y⟫
  证明: c.conj_inner_symm x y

Depends on / 依赖: c.conj_inner_symm, conj_inner_symm
-/
theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_inner_symm x y

/--
theorem `inner_self_nonneg` / 定理 `inner_self_nonneg`

English:
theorem inner_self_nonneg
  given: {x : F}
  statement: 0 <= re ⟪x, x⟫
  proof: c.re_inner_nonneg _

中文:
定理 inner_self_nonneg
  条件: {x : F}
  结论: 0 <= re ⟪x, x⟫
  证明: c.re_inner_nonneg _

Depends on / 依赖: c.re_inner_nonneg, re_inner_nonneg
-/
theorem inner_self_nonneg {x : F} : 0 <= re ⟪x, x⟫ :=
  c.re_inner_nonneg _

/--
theorem `inner_self_im` / 定理 `inner_self_im`

English:
theorem inner_self_im
  given: (x : F)
  statement: im ⟪x, x⟫ = 0
  proof: by
  rw [← @ofReal_inj 𝕜]; rw [im_eq_conj_sub]
  simp [inner_conj_symm]

中文:
定理 inner_self_im
  条件: (x : F)
  结论: im ⟪x, x⟫ = 0
  证明: by
  rw [← @ofReal_inj 𝕜]; rw [im_eq_conj_sub]
  simp [inner_conj_symm]

Depends on / 依赖: im_eq_conj_sub, inner_conj_symm, ofReal_inj
-/
theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜]; rw [im_eq_conj_sub]
  simp [inner_conj_symm]

/--
theorem `inner_add_left` / 定理 `inner_add_left`

English:
theorem inner_add_left
  given: (x y z : F)
  statement: ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  proof: c.add_left _ _ _

中文:
定理 inner_add_left
  条件: (x y z : F)
  结论: ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  证明: c.add_left _ _ _

Depends on / 依赖: add_left, c.add_left
-/
theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _

/--
theorem `inner_add_right` / 定理 `inner_add_right`

English:
theorem inner_add_right
  given: (x y z : F)
  statement: ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
  proof: by
  rw [← inner_conj_symm]; rw [inner_add_left]; rw [map_add]; simp only [inner_conj_symm]

中文:
定理 inner_add_right
  条件: (x y z : F)
  结论: ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
  证明: by
  rw [← inner_conj_symm]; rw [inner_add_left]; rw [map_add]; simp only [inner_conj_symm]

Depends on / 依赖: inner_add_left, inner_conj_symm, map_add
-/
theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm]; rw [inner_add_left]; rw [map_add]; simp only [inner_conj_symm]

/--
theorem `ofReal_normSq_eq_inner_self` / 定理 `ofReal_normSq_eq_inner_self`

English:
theorem ofReal_normSq_eq_inner_self
  given: (x : F)
  statement: (normSqF x : 𝕜) = ⟪x, x⟫
  proof: by
  rw [ext_iff]
  exact ⟨by simp only [ofReal_re, normSq], by simp only [inner_self_im, ofReal_im]⟩

中文:
定理 ofReal_normSq_eq_inner_self
  条件: (x : F)
  结论: (normSqF x : 𝕜) = ⟪x, x⟫
  证明: by
  rw [ext_iff]
  exact ⟨by simp only [ofReal_re, normSq], by simp only [inner_self_im, ofReal_im]⟩

Depends on / 依赖: ext_iff, inner_self_im, normSq, ofReal_im, ofReal_re
-/
theorem ofReal_normSq_eq_inner_self (x : F) : (normSqF x : 𝕜) = ⟪x, x⟫ := by
  rw [ext_iff]
  exact ⟨by simp only [ofReal_re, normSq], by simp only [inner_self_im, ofReal_im]⟩

/--
theorem `inner_re_symm` / 定理 `inner_re_symm`

English:
theorem inner_re_symm
  given: (x y : F)
  statement: re ⟪x, y⟫ = re ⟪y, x⟫
  proof: by rw [← inner_conj_symm, conj_re]

中文:
定理 inner_re_symm
  条件: (x y : F)
  结论: re ⟪x, y⟫ = re ⟪y, x⟫
  证明: by rw [← inner_conj_symm, conj_re]

Depends on / 依赖: conj_re, inner_conj_symm
-/
theorem inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

/--
theorem `inner_im_symm` / 定理 `inner_im_symm`

English:
theorem inner_im_symm
  given: (x y : F)
  statement: im ⟪x, y⟫ = -im ⟪y, x⟫
  proof: by rw [← inner_conj_symm, conj_im]

中文:
定理 inner_im_symm
  条件: (x y : F)
  结论: im ⟪x, y⟫ = -im ⟪y, x⟫
  证明: by rw [← inner_conj_symm, conj_im]

Depends on / 依赖: conj_im, inner_conj_symm
-/
theorem inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

/--
theorem `inner_smul_left` / 定理 `inner_smul_left`

English:
theorem inner_smul_left
  given: (x y : F) {r : 𝕜}
  statement: ⟪r • x, y⟫ = r† * ⟪x, y⟫
  proof: c.smul_left _ _ _

中文:
定理 inner_smul_left
  条件: (x y : F) {r : 𝕜}
  结论: ⟪r • x, y⟫ = r† * ⟪x, y⟫
  证明: c.smul_left _ _ _

Depends on / 依赖: c.smul_left, smul_left
-/
theorem inner_smul_left (x y : F) {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _

/--
theorem `inner_smul_right` / 定理 `inner_smul_right`

English:
theorem inner_smul_right
  given: (x y : F) {r : 𝕜}
  statement: ⟪x, r • y⟫ = r * ⟪x, y⟫
  proof: by
  rw [← inner_conj_symm]; rw [inner_smul_left]
  simp only [conj_conj, inner_conj_symm, map_mul]

中文:
定理 inner_smul_right
  条件: (x y : F) {r : 𝕜}
  结论: ⟪x, r • y⟫ = r * ⟪x, y⟫
  证明: by
  rw [← inner_conj_symm]; rw [inner_smul_left]
  simp only [conj_conj, inner_conj_symm, map_mul]

Depends on / 依赖: conj_conj, inner_conj_symm, inner_smul_left, map_mul
-/
theorem inner_smul_right (x y : F) {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm]; rw [inner_smul_left]
  simp only [conj_conj, inner_conj_symm, map_mul]

/--
theorem `inner_zero_left` / 定理 `inner_zero_left`

English:
theorem inner_zero_left
  given: (x : F)
  statement: ⟪0, x⟫ = 0
  proof: by
  rw [← zero_smul 𝕜 (0 : F)]; rw [inner_smul_left]
  simp only [zero_mul, map_zero]

中文:
定理 inner_zero_left
  条件: (x : F)
  结论: ⟪0, x⟫ = 0
  证明: by
  rw [← zero_smul 𝕜 (0 : F)]; rw [inner_smul_left]
  simp only [zero_mul, map_zero]

Depends on / 依赖: inner_smul_left, map_zero, zero_mul, zero_smul
-/
theorem inner_zero_left (x : F) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F)]; rw [inner_smul_left]
  simp only [zero_mul, map_zero]

/--
theorem `inner_zero_right` / 定理 `inner_zero_right`

English:
theorem inner_zero_right
  given: (x : F)
  statement: ⟪x, 0⟫ = 0
  proof: by
  rw [← inner_conj_symm]; rw [inner_zero_left]; simp only [map_zero]

中文:
定理 inner_zero_right
  条件: (x : F)
  结论: ⟪x, 0⟫ = 0
  证明: by
  rw [← inner_conj_symm]; rw [inner_zero_left]; simp only [map_zero]

Depends on / 依赖: inner_conj_symm, inner_zero_left, map_zero
-/
theorem inner_zero_right (x : F) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm]; rw [inner_zero_left]; simp only [map_zero]

/--
theorem `inner_self_of_eq_zero` / 定理 `inner_self_of_eq_zero`

English:
theorem inner_self_of_eq_zero
  given: {x : F}
  statement: x = 0 -> ⟪x, x⟫ = 0
  proof: by
  rintro rfl
  exact inner_zero_left _

中文:
定理 inner_self_of_eq_zero
  条件: {x : F}
  结论: x = 0 -> ⟪x, x⟫ = 0
  证明: by
  rintro rfl
  exact inner_zero_left _

Depends on / 依赖: inner_zero_left
-/
theorem inner_self_of_eq_zero {x : F} : x = 0 -> ⟪x, x⟫ = 0 := by
  rintro rfl
  exact inner_zero_left _

/--
theorem `normSq_eq_zero_of_eq_zero` / 定理 `normSq_eq_zero_of_eq_zero`

English:
theorem normSq_eq_zero_of_eq_zero
  given: {x : F}
  statement: x = 0 -> normSqF x = 0
  proof: by
  rintro rfl
  simp [normSq, inner_self_of_eq_zero]

中文:
定理 normSq_eq_zero_of_eq_zero
  条件: {x : F}
  结论: x = 0 -> normSqF x = 0
  证明: by
  rintro rfl
  simp [normSq, inner_self_of_eq_zero]

Depends on / 依赖: inner_self_of_eq_zero, normSq
-/
theorem normSq_eq_zero_of_eq_zero {x : F} : x = 0 -> normSqF x = 0 := by
  rintro rfl
  simp [normSq, inner_self_of_eq_zero]

/--
theorem `ne_zero_of_inner_self_ne_zero` / 定理 `ne_zero_of_inner_self_ne_zero`

English:
theorem ne_zero_of_inner_self_ne_zero
  given: {x : F}
  statement: ⟪x, x⟫ != 0 -> x != 0
  proof: mt inner_self_of_eq_zero

中文:
定理 ne_zero_of_inner_self_ne_zero
  条件: {x : F}
  结论: ⟪x, x⟫ != 0 -> x != 0
  证明: mt inner_self_of_eq_zero

Depends on / 依赖: inner_self_of_eq_zero
-/
theorem ne_zero_of_inner_self_ne_zero {x : F} : ⟪x, x⟫ != 0 -> x != 0 :=
  mt inner_self_of_eq_zero

/--
theorem `inner_self_ofReal_re` / 定理 `inner_self_ofReal_re`

English:
theorem inner_self_ofReal_re
  given: (x : F)
  statement: (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫
  proof: by
  norm_num [ext_iff, inner_self_im]

中文:
定理 inner_self_ofReal_re
  条件: (x : F)
  结论: (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫
  证明: by
  norm_num [ext_iff, inner_self_im]

Depends on / 依赖: ext_iff, inner_self_im
-/
theorem inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  norm_num [ext_iff, inner_self_im]

/--
theorem `norm_inner_symm` / 定理 `norm_inner_symm`

English:
theorem norm_inner_symm
  given: (x y : F)
  statement: ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖
  proof: by rw [← inner_conj_symm, norm_conj]

中文:
定理 norm_inner_symm
  条件: (x y : F)
  结论: ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖
  证明: by rw [← inner_conj_symm, norm_conj]

Depends on / 依赖: inner_conj_symm, norm_conj
-/
theorem norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

/--
theorem `inner_neg_left` / 定理 `inner_neg_left`

English:
theorem inner_neg_left
  given: (x y : F)
  statement: ⟪-x, y⟫ = -⟪x, y⟫
  proof: by
  rw [← neg_one_smul 𝕜 x]; rw [inner_smul_left]
  simp

中文:
定理 inner_neg_left
  条件: (x y : F)
  结论: ⟪-x, y⟫ = -⟪x, y⟫
  证明: by
  rw [← neg_one_smul 𝕜 x]; rw [inner_smul_left]
  simp

Depends on / 依赖: inner_smul_left, neg_one_smul
-/
theorem inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x]; rw [inner_smul_left]
  simp

/--
theorem `inner_neg_right` / 定理 `inner_neg_right`

English:
theorem inner_neg_right
  given: (x y : F)
  statement: ⟪x, -y⟫ = -⟪x, y⟫
  proof: by
  rw [← inner_conj_symm]; rw [inner_neg_left]; simp only [map_neg, inner_conj_symm]

中文:
定理 inner_neg_right
  条件: (x y : F)
  结论: ⟪x, -y⟫ = -⟪x, y⟫
  证明: by
  rw [← inner_conj_symm]; rw [inner_neg_left]; simp only [map_neg, inner_conj_symm]

Depends on / 依赖: inner_conj_symm, inner_neg_left, map_neg
-/
theorem inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm]; rw [inner_neg_left]; simp only [map_neg, inner_conj_symm]

/--
theorem `inner_sub_left` / 定理 `inner_sub_left`

English:
theorem inner_sub_left
  given: (x y z : F)
  statement: ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
  proof: by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]

中文:
定理 inner_sub_left
  条件: (x y z : F)
  结论: ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
  证明: by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]

Depends on / 依赖: inner_add_left, inner_neg_left, sub_eq_add_neg
-/
theorem inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]

/--
theorem `inner_sub_right` / 定理 `inner_sub_right`

English:
theorem inner_sub_right
  given: (x y z : F)
  statement: ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
  proof: by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]

中文:
定理 inner_sub_right
  条件: (x y z : F)
  结论: ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
  证明: by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]

Depends on / 依赖: inner_add_right, inner_neg_right, sub_eq_add_neg
-/
theorem inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]

/--
theorem `inner_mul_symm_re_eq_norm` / 定理 `inner_mul_symm_re_eq_norm`

English:
theorem inner_mul_symm_re_eq_norm
  given: (x y : F)
  statement: re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖
  proof: by
  rw [← inner_conj_symm]; rw [mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

中文:
定理 inner_mul_symm_re_eq_norm
  条件: (x y : F)
  结论: re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖
  证明: by
  rw [← inner_conj_symm]; rw [mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

Depends on / 依赖: inner_conj_symm, mul_comm, re_eq_norm_of_mul_conj
-/
theorem inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm]; rw [mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

/--
theorem `inner_add_add_self` / 定理 `inner_add_add_self`

English:
theorem inner_add_add_self
  given: (x y : F)
  statement: ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
  proof: by
  simp only [inner_add_left, inner_add_right]; ring

中文:
定理 inner_add_add_self
  条件: (x y : F)
  结论: ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
  证明: by
  simp only [inner_add_left, inner_add_right]; ring

Depends on / 依赖: inner_add_left, inner_add_right
-/
theorem inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

-- Expand `⟪x - y, x - y⟫`
/--
theorem `inner_sub_sub_self` / 定理 `inner_sub_sub_self`

English:
theorem inner_sub_sub_self
  given: (x y : F)
  statement: ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
  proof: by
  simp only [inner_sub_left, inner_sub_right]; ring

中文:
定理 inner_sub_sub_self
  条件: (x y : F)
  结论: ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
  证明: by
  simp only [inner_sub_left, inner_sub_right]; ring

Depends on / 依赖: inner_sub_left, inner_sub_right
-/
theorem inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/--
theorem `inner_smul_ofReal_left` / 定理 `inner_smul_ofReal_left`

English:
theorem inner_smul_ofReal_left
  given: (x y : F) {t : Real}
  statement: ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t
  proof: by
  rw [inner_smul_left]; rw [conj_ofReal]; rw [mul_comm]

中文:
定理 inner_smul_ofReal_left
  条件: (x y : F) {t : 实数}
  结论: ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t
  证明: by
  rw [inner_smul_left]; rw [conj_ofReal]; rw [mul_comm]

Depends on / 依赖: conj_ofReal, inner_smul_left, mul_comm
-/
theorem inner_smul_ofReal_left (x y : F) {t : Real} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_left]; rw [conj_ofReal]; rw [mul_comm]

/--
theorem `inner_smul_ofReal_right` / 定理 `inner_smul_ofReal_right`

English:
theorem inner_smul_ofReal_right
  given: (x y : F) {t : Real}
  statement: ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t
  proof: by
  rw [inner_smul_right]; rw [mul_comm]

中文:
定理 inner_smul_ofReal_right
  条件: (x y : F) {t : 实数}
  结论: ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t
  证明: by
  rw [inner_smul_right]; rw [mul_comm]

Depends on / 依赖: inner_smul_right, mul_comm
-/
theorem inner_smul_ofReal_right (x y : F) {t : Real} : ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_right]; rw [mul_comm]

/--
theorem `re_inner_smul_ofReal_smul_self` / 定理 `re_inner_smul_ofReal_smul_self`

English:
theorem re_inner_smul_ofReal_smul_self
  given: (x : F) {t : Real}
  proof: by
  simp [inner_smul_ofReal_left, inner_smul_ofReal_right, normSq]

中文:
定理 re_inner_smul_ofReal_smul_self
  条件: (x : F) {t : 实数}
  证明: by
  simp [inner_smul_ofReal_left, inner_smul_ofReal_right, normSq]

Depends on / 依赖: inner_smul_ofReal_left, inner_smul_ofReal_right, normSq
-/
theorem re_inner_smul_ofReal_smul_self (x : F) {t : Real} :
    re ⟪(t : 𝕜) • x, (t : 𝕜) • x⟫ = normSqF x * t * t := by
  simp [inner_smul_ofReal_left, inner_smul_ofReal_right, normSq]

/--
lemma `cauchy_schwarz_aux'` / 引理 `cauchy_schwarz_aux'`

English:
lemma cauchy_schwarz_aux'
  given: (x y : F) (t : Real)
  statement: 0 <= normSqF x * t * t + 2 * re ⟪x, y⟫ * t
  proof: by
  calc 0 <= re ⟪(ofReal t : 𝕜) • x + y, (ofReal t : 𝕜) • x + y⟫ := inner_self_nonneg
  _ = re (⟪(ofReal t : 𝕜) • x, (ofReal t : 𝕜) • x⟫ + ⟪(ofReal t : 𝕜) • x, y⟫
      + ⟪y, (ofReal t : 𝕜) • x⟫ + ⟪y, y⟫) := by rw [inner_add_add_self ((ofReal t : 𝕜) • x) y]
  _ = re ⟪(ofReal t : 𝕜) • x, (ofReal t 

中文:
引理 cauchy_schwarz_aux'
  条件: (x y : F) (t : 实数)
  结论: 0 <= normSqF x * t * t + 2 * re ⟪x, y⟫ * t
  证明: by
  calc 0 <= re ⟪(ofReal t : 𝕜) • x + y, (ofReal t : 𝕜) • x + y⟫ := inner_self_nonneg
  _ = re (⟪(ofReal t : 𝕜) • x, (ofReal t : 𝕜) • x⟫ + ⟪(ofReal t : 𝕜) • x, y⟫
      + ⟪y, (ofReal t : 𝕜) • x⟫ + ⟪y, y⟫) := by rw [inner_add_add_self ((ofReal t : 𝕜) • x) y]
  _ = re ⟪(ofReal t : 𝕜) • x, (ofReal t 

Depends on / 依赖: inner_add_add_self, inner_self_nonneg, map_add, normSq, ofReal, re_inner_smul_ofReal_smul_s
-/
lemma cauchy_schwarz_aux' (x y : F) (t : Real) : 0 <= normSqF x * t * t + 2 * re ⟪x, y⟫ * t
    + normSqF y := by
  calc 0 <= re ⟪(ofReal t : 𝕜) • x + y, (ofReal t : 𝕜) • x + y⟫ := inner_self_nonneg
  _ = re (⟪(ofReal t : 𝕜) • x, (ofReal t : 𝕜) • x⟫ + ⟪(ofReal t : 𝕜) • x, y⟫
      + ⟪y, (ofReal t : 𝕜) • x⟫ + ⟪y, y⟫) := by rw [inner_add_add_self ((ofReal t : 𝕜) • x) y]
  _ = re ⟪(ofReal t : 𝕜) • x, (ofReal t : 𝕜) • x⟫
      + re ⟪(ofReal t : 𝕜) • x, y⟫ + re ⟪y, (ofReal t : 𝕜) • x⟫ + re ⟪y, y⟫ := by
      simp only [map_add]
  _ = normSq x * t * t + re (⟪x, y⟫ * t) + re (⟪y, x⟫ * t) + re ⟪y, y⟫ := by rw
    [re_inner_smul_ofReal_smul_self, inner_smul_ofReal_left, inner_smul_ofReal_right]
  _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪y, x⟫ * t + re ⟪y, y⟫ := by rw [mul_comm ⟪x, y⟫ _,
    RCLike.re_ofReal_mul, mul_comm t _, mul_comm ⟪y, x⟫ _, RCLike.re_ofReal_mul, mul_comm t _]
  _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪y, x⟫ * t + normSq y := by rw [← normSq]
  _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪x, y⟫ * t + normSq y := by rw [inner_re_symm]
  _ = normSq x * t * t + 2 * re ⟪x, y⟫ * t + normSq y := by ring

/--
theorem `cauchy_schwarz_aux` / 定理 `cauchy_schwarz_aux`

English:
theorem cauchy_schwarz_aux
  given: (x y : F)
  statement: normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y)
  proof: by
  rw [← @ofReal_inj 𝕜]; rw [ofReal_normSq_eq_inner_self]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_ofReal, mul_sub, ←
    ofReal_normSq_eq_inner_self x, ← ofReal_normSq_eq_inner_self y]
  rw [← mul_assoc]; rw [mul_conj]; rw [RCLike.conj_mul]; rw [mul_left_comm]; rw 

中文:
定理 cauchy_schwarz_aux
  条件: (x y : F)
  结论: normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y)
  证明: by
  rw [← @ofReal_inj 𝕜]; rw [ofReal_normSq_eq_inner_self]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_ofReal, mul_sub, ←
    ofReal_normSq_eq_inner_self x, ← ofReal_normSq_eq_inner_self y]
  rw [← mul_assoc]; rw [mul_conj]; rw [RCLike.conj_mul]; rw [mul_left_comm]; rw 

Depends on / 依赖: RCLike, RCLike.conj_mul, conj_mul, conj_ofReal, inner_conj_symm, inner_smul_left, inner_smul_right, inner_sub_sub_self, mul_assoc, mul_conj, mul_left_comm, mul_sub, ofReal_inj, ofReal_normSq_eq_inner_self
-/
theorem cauchy_schwarz_aux (x y : F) : normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y)
    = normSqF x * (normSqF x * normSqF y - ‖⟪x, y⟫‖ ^ 2) := by
  rw [← @ofReal_inj 𝕜]; rw [ofReal_normSq_eq_inner_self]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_ofReal, mul_sub, ←
    ofReal_normSq_eq_inner_self x, ← ofReal_normSq_eq_inner_self y]
  rw [← mul_assoc]; rw [mul_conj]; rw [RCLike.conj_mul]; rw [mul_left_comm]; rw [← inner_conj_symm y]; rw [mul_conj]
  push_cast
  ring

/--
theorem `inner_mul_inner_self_le` / 定理 `inner_mul_inner_self_le`

English:
theorem inner_mul_inner_self_le
  given: (x y : F)
  statement: ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫
  proof: by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫_𝕜‖) (normSqF y) <= 0 by
    rw [norm_inner_symm y x]
    rw [discrim]; rw [normSq]; rw [normSq]; rw [sq] at this
    linarith
  refine discrim_le_zero fun t => ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [← sq, hzero, norm_zero, mul_zero, zero_mul, a

中文:
定理 inner_mul_inner_self_le
  条件: (x y : F)
  结论: ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫
  证明: by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫_𝕜‖) (normSqF y) <= 0 by
    rw [norm_inner_symm y x]
    rw [discrim]; rw [normSq]; rw [normSq]; rw [sq] at this
    linarith
  refine discrim_le_zero fun t => ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [← sq, hzero, norm_zero, mul_zero, zero_mul, a

Depends on / 依赖: add_zero, cauchy_schwarz_aux, convert, discrim, discrim_le_zero, inner_self_nonneg, mul_zero, normSq, normSqF, norm_inner_symm, norm_ne_zero_iff, norm_zero, zero_mul
-/
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫ := by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫_𝕜‖) (normSqF y) <= 0 by
    rw [norm_inner_symm y x]
    rw [discrim]; rw [normSq]; rw [normSq]; rw [sq] at this
    linarith
  refine discrim_le_zero fun t => ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [← sq, hzero, norm_zero, mul_zero, zero_mul, add_zero]
    obtain ⟨hx, hy⟩ : (0 <= normSqF x ∧ 0 <= normSqF y) := ⟨inner_self_nonneg, inner_self_nonneg⟩
    positivity
  · have hzero' : ‖⟪x, y⟫‖ != 0 := norm_ne_zero_iff.2 hzero
    convert! cauchy_schwarz_aux' (𝕜 := 𝕜) (⟪x, y⟫ • x) y (t / ‖⟪x, y⟫‖) using 3
    · field_simp
      rw [normSq]; rw [normSq]; rw [inner_smul_right]; rw [inner_smul_left]; rw [← mul_assoc _ _ ⟪x]; rw [x⟫]; rw [mul_conj]
      rw [← ofReal_pow]; rw [re_ofReal_mul]
      ring
    · field_simp
      rw [inner_smul_left]; rw [mul_comm _ ⟪x]; rw [y⟫_𝕜]; rw [mul_conj]; rw [← ofReal_pow]; rw [ofReal_re]
      ring

/-- (Semi)norm constructed from a `PreInnerProductSpace.Core` structure, defined to be the square
root of the scalar product. -/
@[instance_reducible]
/--
Definition of `toNorm` / `toNorm` 的定义

English:
definition toNorm
  signature: : Norm F where norm x
  body: √(re ⟪x, x⟫)

中文:
定义 toNorm
  签名: : Norm F where norm x
  定义体: √(re ⟪x, x⟫)
-/
def toNorm : Norm F where norm x := √(re ⟪x, x⟫)

attribute [local instance] toNorm

/--
theorem `norm_eq_sqrt_re_inner` / 定理 `norm_eq_sqrt_re_inner`

English:
theorem norm_eq_sqrt_re_inner
  given: (x : F)
  statement: ‖x‖ = √(re ⟪x, x⟫)
  proof: rfl

中文:
定理 norm_eq_sqrt_re_inner
  条件: (x : F)
  结论: ‖x‖ = √(re ⟪x, x⟫)
  证明: rfl
-/
theorem norm_eq_sqrt_re_inner (x : F) : ‖x‖ = √(re ⟪x, x⟫) := rfl

/--
theorem `inner_self_eq_norm_mul_norm` / 定理 `inner_self_eq_norm_mul_norm`

English:
theorem inner_self_eq_norm_mul_norm
  given: (x : F)
  statement: re ⟪x, x⟫ = ‖x‖ * ‖x‖
  proof: by
  rw [norm_eq_sqrt_re_inner]; rw [← sqrt_mul inner_self_nonneg]; rw [sqrt_mul_self inner_self_nonneg]

中文:
定理 inner_self_eq_norm_mul_norm
  条件: (x : F)
  结论: re ⟪x, x⟫ = ‖x‖ * ‖x‖
  证明: by
  rw [norm_eq_sqrt_re_inner]; rw [← sqrt_mul inner_self_nonneg]; rw [sqrt_mul_self inner_self_nonneg]

Depends on / 依赖: inner_self_nonneg, norm_eq_sqrt_re_inner, sqrt_mul, sqrt_mul_self
-/
theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_re_inner]; rw [← sqrt_mul inner_self_nonneg]; rw [sqrt_mul_self inner_self_nonneg]

/--
theorem `sqrt_normSq_eq_norm` / 定理 `sqrt_normSq_eq_norm`

English:
theorem sqrt_normSq_eq_norm
  given: (x : F)
  statement: √(normSqF x) = ‖x‖
  proof: rfl

中文:
定理 sqrt_normSq_eq_norm
  条件: (x : F)
  结论: √(normSqF x) = ‖x‖
  证明: rfl
-/
theorem sqrt_normSq_eq_norm (x : F) : √(normSqF x) = ‖x‖ := rfl

/--
theorem `norm_inner_le_norm` / 定理 `norm_inner_le_norm`

English:
theorem norm_inner_le_norm
  given: (x y : F)
  statement: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
  proof: nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ <= re ⟪x, x⟫ * re ⟪y, y⟫ := inner_mul_inner_self_le x y
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm

中文:
定理 norm_inner_le_norm
  条件: (x y : F)
  结论: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
  证明: nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ <= re ⟪x, x⟫ * re ⟪y, y⟫ := inner_mul_inner_self_le x y
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm

Depends on / 依赖: inner_mul_inner_self_le, inner_self_eq_norm_mul_norm, mul_nonneg, nonneg_le_nonneg_of_sq_le_sq, norm_inner_symm, sqrt_nonneg
-/
theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ :=
nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ <= re ⟪x, x⟫ * re ⟪y, y⟫ := inner_mul_inner_self_le x y
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm]; ring

/-- Seminormed group structure constructed from a `PreInnerProductSpace.Core` structure -/
@[instance_reducible]
/--
Definition of `toSeminormedAddCommGroup` / `toSeminormedAddCommGroup` 的定义

English:
definition toSeminormedAddCommGroup
  signature: : SeminormedAddCommGroup F
  body: AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖

中文:
定义 toSeminormedAddCommGroup
  签名: : SeminormedAddCommGroup F
  定义体: AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, add_le, conj_re, inner_conj_symm, inner_neg_left, inner_neg_right, inner_zero_right, map_zero, neg_neg, norm_inner_le_norm, re_le_norm, sqrt_zero, toSeminormedAddCommGroup
-/
def toSeminormedAddCommGroup : SeminormedAddCommGroup F :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ <= ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ <= ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ <= ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ <= (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this }

attribute [local instance] toSeminormedAddCommGroup

/-- Normed space (which is actually a seminorm in general) structure constructed from a
`PreInnerProductSpace.Core` structure -/
@[instance_reducible]
/--
Definition of `toNormedSpace` / `toNormedSpace` 的定义

English:
definition toNormedSpace
  signature: : NormedSpace 𝕜 F where
  body: by
    rw [norm_eq_sqrt_re_inner]; rw [inner_smul_left]; rw [inner_smul_right]; rw [← mul_assoc]
    rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [re_ofReal_mul]; rw [sqrt_mul]; rw [← ofReal_normSq_eq_inner_self]; rw [ofReal_re]
    · simp [sqrt_normSq_eq_norm]
    · positivity

omit c in

中文:
定义 toNormedSpace
  签名: : NormedSpace 𝕜 F where
  定义体: by
    rw [norm_eq_sqrt_re_inner]; rw [inner_smul_left]; rw [inner_smul_right]; rw [← mul_assoc]
    rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [re_ofReal_mul]; rw [sqrt_mul]; rw [← ofReal_normSq_eq_inner_self]; rw [ofReal_re]
    · simp [sqrt_normSq_eq_norm]
    · positivity

omit c in

Depends on / 依赖: RCLike, RCLike.conj_mul, conj_mul, inner_smul_left, inner_smul_right, mul_assoc, norm_eq_sqrt_re_inner, ofReal_normSq_eq_inner_self, ofReal_pow, ofReal_re, re_ofReal_mul, sqrt_mul, sqrt_normSq_eq_norm
-/
def toNormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_re_inner]; rw [inner_smul_left]; rw [inner_smul_right]; rw [← mul_assoc]
    rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [re_ofReal_mul]; rw [sqrt_mul]; rw [← ofReal_normSq_eq_inner_self]; rw [ofReal_re]
    · simp [sqrt_normSq_eq_norm]
    · positivity

omit c in
/--
lemma `toSeminormedSpaceCore` / 引理 `toSeminormedSpaceCore`

English:
lemma toSeminormedSpaceCore
  given: (c : PreInnerProductSpace.Core 𝕜 F)
  statement: SeminormedSpace.Core 𝕜 F where
  proof: norm_nonneg x
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

中文:
引理 toSeminormedSpaceCore
  条件: (c : PreInnerProductSpace.Core 𝕜 F)
  结论: SeminormedSpace.Core 𝕜 F where
  证明: norm_nonneg x
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

Depends on / 依赖: norm_nonneg
-/
lemma toSeminormedSpaceCore (c : PreInnerProductSpace.Core 𝕜 F) : SeminormedSpace.Core 𝕜 F where
  norm_nonneg x := norm_nonneg x
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

end PreInnerProductSpace.Core

section InnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [cd : InnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "ext_iff" => @RCLike.ext_iff 𝕜 _

/-- Inner product defined by the `InnerProductSpace.Core` structure. We can't reuse
`InnerProductSpace.Core.toInner` because it takes `InnerProductSpace.Core` as an explicit
argument. -/
@[instance_reducible]
/--
Definition of `toInner'` / `toInner'` 的定义

English:
definition toInner'
  signature: : Inner 𝕜 F
  body: cd.toInner

中文:
定义 toInner'
  签名: : Inner 𝕜 F
  定义体: cd.toInner

Depends on / 依赖: cd.toInner, toInner
-/
def toInner' : Inner 𝕜 F :=
  cd.toInner

attribute [local instance] toInner'

local notation "normSqF" => @normSq 𝕜 F _ _ _ _

/--
theorem `inner_self_eq_zero` / 定理 `inner_self_eq_zero`

English:
theorem inner_self_eq_zero
  given: {x : F}
  statement: ⟪x, x⟫ = 0 ↔ x = 0
  proof: ⟨cd.definite _, inner_self_of_eq_zero⟩

中文:
定理 inner_self_eq_zero
  条件: {x : F}
  结论: ⟪x, x⟫ = 0 ↔ x = 0
  证明: ⟨cd.definite _, inner_self_of_eq_zero⟩

Depends on / 依赖: cd.definite, definite, inner_self_of_eq_zero
-/
theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  ⟨cd.definite _, inner_self_of_eq_zero⟩

/--
theorem `normSq_eq_zero` / 定理 `normSq_eq_zero`

English:
theorem normSq_eq_zero
  given: {x : F}
  statement: normSqF x = 0 ↔ x = 0
  proof: Iff.trans
    (by simp only [normSq, ext_iff, map_zero, inner_self_im, and_true])
    (inner_self_eq_zero (𝕜 := 𝕜))

中文:
定理 normSq_eq_zero
  条件: {x : F}
  结论: normSqF x = 0 ↔ x = 0
  证明: Iff.trans
    (by simp only [normSq, ext_iff, map_zero, inner_self_im, and_true])
    (inner_self_eq_zero (𝕜 := 𝕜))

Depends on / 依赖: Iff.trans, and_true, ext_iff, inner_self_eq_zero, inner_self_im, map_zero, normSq
-/
theorem normSq_eq_zero {x : F} : normSqF x = 0 ↔ x = 0 :=
  Iff.trans
    (by simp only [normSq, ext_iff, map_zero, inner_self_im, and_true])
    (inner_self_eq_zero (𝕜 := 𝕜))

/--
theorem `inner_self_ne_zero` / 定理 `inner_self_ne_zero`

English:
theorem inner_self_ne_zero
  given: {x : F}
  statement: ⟪x, x⟫ != 0 ↔ x != 0
  proof: inner_self_eq_zero.not

中文:
定理 inner_self_ne_zero
  条件: {x : F}
  结论: ⟪x, x⟫ != 0 ↔ x != 0
  证明: inner_self_eq_zero.not

Depends on / 依赖: inner_self_eq_zero, inner_self_eq_zero.not
-/
theorem inner_self_ne_zero {x : F} : ⟪x, x⟫ != 0 ↔ x != 0 :=
  inner_self_eq_zero.not

attribute [local instance] toNorm

/-- Normed group structure constructed from an `InnerProductSpace.Core` structure -/
@[instance_reducible]
/--
Definition of `toNormedAddCommGroup` / `toNormedAddCommGroup` 的定义

English:
definition toNormedAddCommGroup
  signature: : NormedAddCommGroup F
  body: AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ := norm

中文:
定义 toNormedAddCommGroup
  签名: : NormedAddCommGroup F
  定义体: AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ := norm

Depends on / 依赖: AddGroupNorm, AddGroupNorm.toNormedAddCommGroup, add_le, conj_re, inner_conj_symm, inner_neg_left, inner_neg_right, inner_zero_right, map_zero, neg_neg, norm_inner_le_norm, re_le_norm, sqrt_zero, toNormedAddCommGroup
-/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ <= ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ <= ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ <= ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ <= (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun _ hx =>
normSq_eq_zero.1 (sqrt_eq_zero inner_self_nonneg).1 hx }

section

attribute [local instance] toNormedAddCommGroup

omit cd in
/--
lemma `toNormedSpaceCore` / 引理 `toNormedSpaceCore`

English:
lemma toNormedSpaceCore
  given: (cd : InnerProductSpace.Core 𝕜 F)
  statement: NormedSpace.Core 𝕜 F where
  proof: norm_nonneg x
  norm_eq_zero_iff x := norm_eq_zero
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

中文:
引理 toNormedSpaceCore
  条件: (cd : InnerProductSpace.Core 𝕜 F)
  结论: NormedSpace.Core 𝕜 F where
  证明: norm_nonneg x
  norm_eq_zero_iff x := norm_eq_zero
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

Depends on / 依赖: norm_nonneg
-/
lemma toNormedSpaceCore (cd : InnerProductSpace.Core 𝕜 F) : NormedSpace.Core 𝕜 F where
  norm_nonneg x := norm_nonneg x
  norm_eq_zero_iff x := norm_eq_zero
  norm_smul c x := by
    let : NormedSpace 𝕜 F := toNormedSpace
    exact _root_.norm_smul c x
  norm_triangle x y := norm_add_le x y

end

set_option backward.isDefEq.respectTransparency false in
/--
lemma `topology_eq` / 引理 `topology_eq`

English:
lemma topology_eq
  proof: by
  let p : Seminorm 𝕜 F := @normSeminorm 𝕜 F _ cd.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace
  suffices WithSeminorms (fun (i : Fin 1) => p) by
    rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 this]
    simp
  have : p.ball 0 1 = {

中文:
引理 topology_eq
  证明: by
  let p : Seminorm 𝕜 F := @normSeminorm 𝕜 F _ cd.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace
  suffices WithSeminorms (fun (i : Fin 1) => p) by
    rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 this]
    simp
  have : p.ball 0 1 = {

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toNormedSpace, Metric, Metric.mem_ball, Seminorm, SeminormFamily, SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf, Set.mem_ofPred_eq, WithSeminorms, ball_normSeminorm, cd.inner, cd.toNormedAddCommGroup.toSeminormedAddCommGroup, conv_lhs, dist_eq_norm, mem_ball, mem_ofPred_eq, normSeminorm, p.ball, sub_zero, toNormedAddCommGroup
-/
lemma topology_eq
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) => cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    tF = cd.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  let p : Seminorm 𝕜 F := @normSeminorm 𝕜 F _ cd.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace
  suffices WithSeminorms (fun (i : Fin 1) => p) by
    rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 this]
    simp
  have : p.ball 0 1 = {v | re (cd.inner v v) < 1} := by
    ext v
    simp only [ball_normSeminorm, Metric.mem_ball, dist_eq_norm, sub_zero, Set.mem_ofPred_eq, p]
    change √(re (cd.inner v v)) < 1 ↔ re (cd.inner v v) < 1
    conv_lhs => rw [show (1 : Real) = √1 by simp]
    rw [sqrt_lt_sqrt_iff]
    exact InnerProductSpace.Core.inner_self_nonneg
  rw [withSeminorms_iff_mem_nhds_isVonNBounded]; rw [this]
  refine ⟨?_, h'⟩
  have A : ContinuousAt (fun (v : F) => re (cd.inner v v)) 0 := by fun_prop
  have B : Set.Iio 1 in 𝓝 (re (cd.inner 0 0)) := by
    simp only [InnerProductSpace.Core.inner_zero_left, map_zero]
    exact Iio_mem_nhds (by positivity)
  exact A B

/--
Definition of `toNormedAddCommGroupOfTopology` / `toNormedAddCommGroupOfTopology` 的定义

English:
definition toNormedAddCommGroupOfTopology
  body: NormedAddCommGroup.ofCoreReplaceTopology cd.toNormedSpaceCore (cd.topology_eq h h')

中文:
定义 toNormedAddCommGroupOfTopology
  定义体: NormedAddCommGroup.ofCoreReplaceTopology cd.toNormedSpaceCore (cd.topology_eq h h')
-/
@[reducible] def toNormedAddCommGroupOfTopology
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) => cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    NormedAddCommGroup F :=
  NormedAddCommGroup.ofCoreReplaceTopology cd.toNormedSpaceCore (cd.topology_eq h h')

/--
Definition of `toNormedSpaceOfTopology` / `toNormedSpaceOfTopology` 的定义

English:
definition toNormedSpaceOfTopology
  body: cd.toNormedAddCommGroupOfTopology h h';
    NormedSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  { norm_smul_le r x := by
      rw [norm_eq_sqrt_re_inner]; rw [inner_smul_left]; rw [inner_smul_right]; rw [← mul_assoc]
      rw [RCLike.conj_mul]; rw [← ofReal_p

中文:
定义 toNormedSpaceOfTopology
  定义体: cd.toNormedAddCommGroupOfTopology h h';
    NormedSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  { norm_smul_le r x := by
      rw [norm_eq_sqrt_re_inner]; rw [inner_smul_left]; rw [inner_smul_right]; rw [← mul_assoc]
      rw [RCLike.conj_mul]; rw [← ofReal_p
-/
@[reducible] def toNormedSpaceOfTopology
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) => cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h';
    NormedSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  { norm_smul_le r x := by
      rw [norm_eq_sqrt_re_inner]; rw [inner_smul_left]; rw [inner_smul_right]; rw [← mul_assoc]
      rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [re_ofReal_mul]; rw [sqrt_mul]; rw [← ofReal_normSq_eq_inner_self]; rw [ofReal_re]
      · simp [sqrt_normSq_eq_norm]
      · positivity }

end InnerProductSpace.Core

end InnerProductSpace.Core

section

attribute [local instance] InnerProductSpace.Core.toSeminormedAddCommGroup

/-- Given a `PreInnerProductSpace.Core` structure on a space, one can use it to turn
the space into a pre-inner product space (i.e., `SeminormedAddCommGroup` and `InnerProductSpace`).
The `SeminormedAddCommGroup` structure is expected to already be defined with
`InnerProductSpace.ofCore.toSeminormedAddCommGroup`. -/
@[instance_reducible]
/--
Definition of `InnerProductSpace.ofCore` / `InnerProductSpace.ofCore` 的定义

English:
definition InnerProductSpace.ofCore
  signature: [AddCommGroup F] [Module 𝕜 F] (cd : PreInnerProductSpace.Core 𝕜 F)
  body: letI : NormedSpace 𝕜 F := InnerProductSpace.Core.toNormedSpace
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 <= re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

中文:
定义 InnerProductSpace.ofCore
  签名: [AddCommGroup F] [Module 𝕜 F] (cd : PreInnerProductSpace.Core 𝕜 F)
  定义体: letI : NormedSpace 𝕜 F := InnerProductSpace.Core.toNormedSpace
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 <= re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.inner_self_nonneg, InnerProductSpace.Core.toNormedSpace, NormedSpace, cd.inner, inner_self_nonneg, norm_sq_eq_re_inner, sq_sqrt, toNormedSpace
-/
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (cd : PreInnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := InnerProductSpace.Core.toNormedSpace
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 <= re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

end

/-- Given an `InnerProductSpace.Core` structure on a space with a topology, one can use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is expected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroupOfTopology`. -/
@[instance_reducible]
/--
Definition of `InnerProductSpace.ofCoreOfTopology` / `InnerProductSpace.ofCoreOfTopology` 的定义

English:
definition InnerProductSpace.ofCoreOfTopology
  signature: [AddCommGroup F] [hF : Module 𝕜 F] [TopologicalSpace F]
  body: cd.toNormedAddCommGroupOfTopology h h';
    InnerProductSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  letI : NormedSpace 𝕜 F := cd.toNormedSpaceOfTopology h h'
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^

中文:
定义 InnerProductSpace.ofCoreOfTopology
  签名: [AddCommGroup F] [hF : Module 𝕜 F] [TopologicalSpace F]
  定义体: cd.toNormedAddCommGroupOfTopology h h';
    InnerProductSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  letI : NormedSpace 𝕜 F := cd.toNormedSpaceOfTopology h h'
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^

Depends on / 依赖: cd.toNormedAddCommGroupOfTopology, toNormedAddCommGroupOfTopology
-/
def InnerProductSpace.ofCoreOfTopology [AddCommGroup F] [hF : Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (cd : InnerProductSpace.Core 𝕜 F)
    (h : ContinuousAt (fun (v : F) => cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h';
    InnerProductSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  letI : NormedSpace 𝕜 F := cd.toNormedSpaceOfTopology h h'
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 <= re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

/-- A Hilbert space is a complete normed inner product space. -/
@[variable_alias]
/--
Definition of `HilbertSpace` / `HilbertSpace` 的定义

English:
structure HilbertSpace
  parameters: (𝕜 E : Type*) [RCLike 𝕜]
  (no additional axioms)

中文:
结构 HilbertSpace
  参数: (𝕜 E : 类型) [RCLike 𝕜]
  (无附加公理)
-/
structure HilbertSpace (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace PUnit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InnerProductSpace 𝕜 PUnit
  body: 0
  norm_sq_eq_re_inner := by simp
  conj_inner_symm := by simp
  add_left := by simp
  smul_left := by simp

中文:
实例 :
  签名: InnerProductSpace 𝕜 PUnit
  定义体: 0
  norm_sq_eq_re_inner := by simp
  conj_inner_symm := by simp
  add_left := by simp
  smul_left := by simp
-/
instance : InnerProductSpace 𝕜 PUnit where
  inner _ _ := 0
  norm_sq_eq_re_inner := by simp
  conj_inner_symm := by simp
  add_left := by simp
  smul_left := by simp

/--
lemma `inner_eq_zero` / 引理 `inner_eq_zero`

English:
lemma inner_eq_zero
  given: (x y : PUnit)
  statement: inner 𝕜 x y = 0
  proof: rfl

中文:
引理 inner_eq_zero
  条件: (x y : PUnit)
  结论: inner 𝕜 x y = 0
  证明: rfl
-/
@[simp] lemma inner_eq_zero (x y : PUnit) : inner 𝕜 x y = 0 := rfl

end PUnit

end
