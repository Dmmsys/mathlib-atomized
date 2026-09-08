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

/-- Syntactic typeclass for types endowed with an inner product -/
/-
**Inner** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_5 → Type (max u_4 u_5)
参数：max u_4 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Syntactic typeclass for types endowed with an inner product
-/
class Inner (𝕜 E : Type*) where
  /-- The inner product function. -/
  inner (𝕜) : E → E → 𝕜

export Inner (inner)

/-- The inner product with values in `𝕜`. -/
scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y

section Notations

/-- The inner product with values in `ℝ`. -/
scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The inner product with values in `ℂ`. -/
scoped[ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℂ x y

end Notations

/-- A (pre) inner product space is a vector space with an additional operation called inner product.
The (semi)norm could be derived from the inner product, instead we require the existence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`.
-/
@[wikidata Q214159]
/-
**InnerProductSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_4) → (E : Type u_5) → [RCLike 𝕜] → [SeminormedAddCommGroup E] 
→ Type (max u_4 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (pre) inner product space is a vector space with an additional operation calle
d inner product.
The (semi)norm could be derived from the inner product, instead we require the e
xistence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂
` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather
 a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`
.
-/
class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
    NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_re_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

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

/-- A structure requiring that a scalar product is positive semidefinite and symmetric. -/
/-
**PreInnerProductSpace.Core** 是 Mathlib 中的一个归纳类型，位于命名空间 `PreInnerProductSpace`。
形式化陈述：(𝕜 : Type u_4) →   (F : Type u_5) → [inst : RCLike 𝕜] → [inst_1 : AddCommG
roup F] → [_root_.Module 𝕜 F] → Type (max u_4 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure requiring that a scalar product is positive semidefinite and symmetr
ic.
-/
structure PreInnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
    [Module 𝕜 F] extends Inner 𝕜 F where
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm x y : conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  re_inner_nonneg x : 0 ≤ re (inner x x)
  /-- The inner product is additive in the first coordinate. -/
  add_left x y z : inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left x y r : inner (r • x) y = conj r * inner x y

attribute [class] PreInnerProductSpace.Core

/-- A structure requiring that a scalar product is positive definite. Some theorems that
require these assumptions are put under section `InnerProductSpace.Core`. -/
/-
**InnerProductSpace.Core** 是 Mathlib 中的一个归纳类型，位于命名空间 `InnerProductSpace`。
形式化陈述：(𝕜 : Type u_4) →   (F : Type u_5) → [inst : RCLike 𝕜] → [inst_1 : AddCommG
roup F] → [_root_.Module 𝕜 F] → Type (max u_4 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure requiring that a scalar product is positive definite. Some theorems 
that
require these assumptions are put under section `InnerProductSpace.Core`.
-/
structure InnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends PreInnerProductSpace.Core 𝕜 F where
  /-- The inner product is positive definite. -/
  definite : ∀ x, inner x x = 0 → x = 0

/- We set `InnerProductSpace.Core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We set `InnerProductSpace.Core` to be a class as we will use it as such in the c
onstruction
of the normed space structure that it produces. However, all the instances we wi
ll use will be
local to this proof.
-/
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
/-
**PreInnerProductSpace.toCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSp
ace 𝕜 E] : PreInnerProductSpace.Core 𝕜 E where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.conj_inner_symm`：∀ {𝕜 : Type u_4} {E : Type u_5} {inst
 : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜 E] 
  (x y : E), (starRingE…
· 使用定理 `InnerProductSpace.add_left`：∀ {𝕜 : Type u_4} {E : Type u_5} {inst : RCLi
ke 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜 E]   (x y 
z : E), inner 𝕜 …
· 使用定理 `InnerProductSpace.smul_left`：∀ {𝕜 : Type u_4} {E : Type u_5} {inst : RCL
ike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜 E]   (x y
 : E) (r : 𝕜), in…

--- 原说明 ---
Define `PreInnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse le
mmas about
`PreInnerProductSpace.Core` for `PreInnerProductSpace`s. Note that the `Seminorm
` instance provided
by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally eq
ual to the original
norm.
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
/-
**InnerProductSpace.toCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E
] : InnerProductSpace.Core 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `InnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemma
s about
`InnerProductSpace.Core` for `InnerProductSpace`s. Note that the `Norm` instance
 provided by
`InnerProductSpace.Core.norm` is propositionally but not definitionally equal to
 the original
norm.
-/
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    re_inner_nonneg := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_re_inner]
      apply sq_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| eq_zero_of_pow_eq_zero (n := 2) <| by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x, hx, map_zero] }

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
/-
**InnerProductSpace.Core.toPreInner'** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpac
e.Core`。
形式化陈述：toPreInner' : Inner 𝕜 F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inner product defined by the `PreInnerProductSpace.Core` structure. We can't reu
se
`PreInnerProductSpace.Core.toInner` because it takes `PreInnerProductSpace.Core`
 as an explicit
argument.
-/
def toPreInner' : Inner 𝕜 F :=
  c.toInner

attribute [local instance] toPreInner'

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
/-
**InnerProductSpace.Core.normSq** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace.Cor
e`。
形式化陈述：normSq (x : F)
参数：x : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm squared function for `PreInnerProductSpace.Core` structure.
-/
def normSq (x : F) :=
  re ⟪x, x⟫

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
local notation "normSqF" => @normSq 𝕜 F _ _ _ _

/-
**InnerProductSpace.Core.inner_conj_symm** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreInnerProductSpace.Core.conj_inner_symm`：∀ {𝕜 : Type u_4} {F : Type u_
5} [inst : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (s
elf : PreInnerProductSpace.Core…
-/
theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_inner_symm x y
/-
**InnerProductSpace.Core.inner_self_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `InnerProdu
ctSpace.Core`。
形式化陈述：inner_self_nonneg {x : F} : 0 <= re ⟪x, x⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreInnerProductSpace.Core.re_inner_nonneg`：∀ {𝕜 : Type u_4} {F : Type u_
5} [inst : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (s
elf : PreInnerProductSpace.Core…
-/
theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.re_inner_nonneg _
/-
**InnerProductSpace.Core.inner_self_im** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
ace.Core`。
形式化陈述：inner_self_im (x : F) : im ⟪x, x⟫ = 0
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RCLike.im_eq_conj_sub`：im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - 
z) / 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]
  simp [inner_conj_symm]
/-
**InnerProductSpace.Core.inner_add_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace.Core`。
形式化陈述：inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
参数：x y z : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreInnerProductSpace.Core.add_left`：∀ {𝕜 : Type u_4} {F : Type u_5} [ins
t : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (self : P
reInnerProductSpace.Core…
-/
theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _
/-
**InnerProductSpace.Core.inner_add_right** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
参数：x y z : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `InnerProductSpace.Core.inner_add_left`：inner_add_left (x y z : F) : ⟪x +
 y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, map_add]; simp only [inner_conj_symm]
/-
**InnerProductSpace.Core.ofReal_normSq_eq_inner_self** 是 Mathlib 中的一个定理，位于命名空间 `
InnerProductSpace.Core`。
形式化陈述：ofReal_normSq_eq_inner_self (x : F) : (normSqF x : 𝕜) = ⟪x, x⟫
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `InnerProductSpace.Core.inner_self_im`：inner_self_im (x : F) : im ⟪x, x⟫ 
= 0
-/
theorem ofReal_normSq_eq_inner_self (x : F) : (normSqF x : 𝕜) = ⟪x, x⟫ := by
  rw [ext_iff]
  exact ⟨by simp only [ofReal_re, normSq], by simp only [inner_self_im, ofReal_im]⟩
/-
**InnerProductSpace.Core.inner_re_symm** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
ace.Core`。
形式化陈述：inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_re`：conj_re (z : K) : re (conj z) = re z
-/
theorem inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]
/-
**InnerProductSpace.Core.inner_im_symm** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
ace.Core`。
形式化陈述：inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_im`：conj_im (z : K) : im (conj z) = -im z
-/
theorem inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]
/-
**InnerProductSpace.Core.inner_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：inner_smul_left (x y : F) {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreInnerProductSpace.Core.smul_left`：∀ {𝕜 : Type u_4} {F : Type u_5} [in
st : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (self : 
PreInnerProductSpace.Core…
-/
theorem inner_smul_left (x y : F) {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _
/-
**InnerProductSpace.Core.inner_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduc
tSpace.Core`。
形式化陈述：inner_smul_right (x y : F) {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `InnerProductSpace.Core.inner_smul_left`：inner_smul_left (x y : F) {r : 𝕜
} : ⟪r • x, y⟫ = r† * ⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarR
ing R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_smul_right (x y : F) {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left]
  simp only [conj_conj, inner_conj_symm, map_mul]
/-
**InnerProductSpace.Core.inner_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：inner_zero_left (x : F) : ⟪0, x⟫ = 0
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `InnerProductSpace.Core.inner_smul_left`：inner_smul_left (x y : F) {r : 𝕜
} : ⟪r • x, y⟫ = r† * ⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_zero_left (x : F) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F), inner_smul_left]
  simp only [zero_mul, map_zero]
/-
**InnerProductSpace.Core.inner_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduc
tSpace.Core`。
形式化陈述：inner_zero_right (x : F) : ⟪x, 0⟫ = 0
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `InnerProductSpace.Core.inner_zero_left`：inner_zero_left (x : F) : ⟪0, x⟫
 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_zero_right (x : F) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left]; simp only [map_zero]
/-
**InnerProductSpace.Core.inner_self_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.Core`。
形式化陈述：inner_self_of_eq_zero {x : F} : x = 0 -> ⟪x, x⟫ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.Core.inner_zero_left`：inner_zero_left (x : F) : ⟪0, x⟫
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inner_self_of_eq_zero {x : F} : x = 0 → ⟪x, x⟫ = 0 := by
  rintro rfl
  exact inner_zero_left _
/-
**InnerProductSpace.Core.normSq_eq_zero_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductSpace.Core`。
形式化陈述：normSq_eq_zero_of_eq_zero {x : F} : x = 0 -> normSqF x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.inner_self_of_eq_zero`：inner_self_of_eq_zero {x :
 F} : x = 0 -> ⟪x, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem normSq_eq_zero_of_eq_zero {x : F} : x = 0 → normSqF x = 0 := by
  rintro rfl
  simp [normSq, inner_self_of_eq_zero]
/-
**InnerProductSpace.Core.ne_zero_of_inner_self_ne_zero** 是 Mathlib 中的一个定理，位于命名空间
 `InnerProductSpace.Core`。
形式化陈述：ne_zero_of_inner_self_ne_zero {x : F} : ⟪x, x⟫ != 0 -> x != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `InnerProductSpace.Core.inner_self_of_eq_zero`：inner_self_of_eq_zero {x :
 F} : x = 0 -> ⟪x, x⟫ = 0
-/
theorem ne_zero_of_inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 → x ≠ 0 :=
  mt inner_self_of_eq_zero
/-
**InnerProductSpace.Core.inner_self_ofReal_re** 是 Mathlib 中的一个定理，位于命名空间 `InnerPr
oductSpace.Core`。
形式化陈述：inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `InnerProductSpace.Core.inner_self_im`：inner_self_im (x : F) : im ⟪x, x⟫ 
= 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  norm_num [ext_iff, inner_self_im]
/-
**InnerProductSpace.Core.norm_inner_symm** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
-/
theorem norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]
/-
**InnerProductSpace.Core.inner_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace.Core`。
形式化陈述：inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `InnerProductSpace.Core.inner_smul_left`：inner_smul_left (x y : F) {r : 𝕜
} : ⟪r • x, y⟫ = r† * ⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
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
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp
/-
**InnerProductSpace.Core.inner_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `InnerProductSpace.Core.inner_neg_left`：inner_neg_left (x y : F) : ⟪-x, y
⟫ = -⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [map_neg, inner_conj_symm]
/-
**InnerProductSpace.Core.inner_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace.Core`。
形式化陈述：inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
参数：x y z : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductSpace.Core.inner_add_left`：inner_add_left (x y z : F) : ⟪x +
 y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
· 使用定理 `InnerProductSpace.Core.inner_neg_left`：inner_neg_left (x y : F) : ⟪-x, y
⟫ = -⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
/-
**InnerProductSpace.Core.inner_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space.Core`。
形式化陈述：inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
参数：x y z : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductSpace.Core.inner_add_right`：inner_add_right (x y z : F) : ⟪x
, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
· 使用定理 `InnerProductSpace.Core.inner_neg_right`：inner_neg_right (x y : F) : ⟪x, 
-y⟫ = -⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]
/-
**InnerProductSpace.Core.inner_mul_symm_re_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductSpace.Core`。
形式化陈述：inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y,
 x⟫‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.re_eq_norm_of_mul_conj`：re_eq_norm_of_mul_conj (x : K) : re (x * 
conj x) = ‖x * conj x‖
-/
theorem inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

/-- Expand `⟪x + y, x + y⟫` -/
/-
**InnerProductSpace.Core.inner_add_add_self** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace.Core`。
形式化陈述：inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ +
 ⟪y, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InnerProductSpace.Core.inner_add_right`：inner_add_right (x y z : F) : ⟪x
, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductSpace.Core.inner_add_left`：inner_add_left (x y z : F) : ⟪x +
 y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a

--- 原说明 ---
Expand `⟪x + y, x + y⟫`
-/
theorem inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

-- Expand `⟪x - y, x - y⟫`
/-
**InnerProductSpace.Core.inner_sub_sub_self** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace.Core`。
形式化陈述：inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ +
 ⟪y, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InnerProductSpace.Core.inner_sub_right`：inner_sub_right (x y z : F) : ⟪x
, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductSpace.Core.inner_sub_left`：inner_sub_left (x y z : F) : ⟪x -
 y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
-/
theorem inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring
/-
**InnerProductSpace.Core.inner_smul_ofReal_left** 是 Mathlib 中的一个定理，位于命名空间 `Inner
ProductSpace.Core`。
形式化陈述：inner_smul_ofReal_left (x y : F) {t : Real} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * 
t
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.inner_smul_left`：inner_smul_left (x y : F) {r : 𝕜
} : ⟪r • x, y⟫ = r† * ⟪x, y⟫
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem inner_smul_ofReal_left (x y : F) {t : ℝ} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_left, conj_ofReal, mul_comm]
/-
**InnerProductSpace.Core.inner_smul_ofReal_right** 是 Mathlib 中的一个定理，位于命名空间 `Inne
rProductSpace.Core`。
形式化陈述：inner_smul_ofReal_right (x y : F) {t : Real} : ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ *
 t
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.inner_smul_right`：inner_smul_right (x y : F) {r :
 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem inner_smul_ofReal_right (x y : F) {t : ℝ} : ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_right, mul_comm]
/-
**InnerProductSpace.Core.re_inner_smul_ofReal_smul_self** 是 Mathlib 中的一个定理，位于命名空
间 `InnerProductSpace.Core`。
形式化陈述：re_inner_smul_ofReal_smul_self (x : F) {t : Real} : re ⟪(t : 𝕜) • x, (t : 
𝕜) • x⟫ = normSqF x * t * t
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.inner_smul_ofReal_right`：inner_smul_ofReal_right 
(x y : F) {t : Real} : ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t
· 使用定理 `InnerProductSpace.Core.inner_smul_ofReal_left`：inner_smul_ofReal_left (x
 y : F) {t : Real} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_inner_smul_ofReal_smul_self (x : F) {t : ℝ} :
    re ⟪(t : 𝕜) • x, (t : 𝕜) • x⟫ = normSqF x * t * t := by
  simp [inner_smul_ofReal_left, inner_smul_ofReal_right, normSq]

/-- An auxiliary equality useful to prove the **Cauchy–Schwarz inequality**. Here we use the
standard argument involving the discriminant of quadratic form. -/
/-
**InnerProductSpace.Core.cauchy_schwarz_aux'** 是 Mathlib 中的一个引理，位于命名空间 `InnerPro
ductSpace.Core`。
形式化陈述：cauchy_schwarz_aux' (x y : F) (t : Real) : 0 <= normSqF x * t * t + 2 * re
 ⟪x, y⟫ * t + normSqF y
参数：x y : F；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductSpace.Core.inner_self_nonneg`：inner_self_nonneg {x : F} : 0 
<= re ⟪x, x⟫
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.inner_add_add_self`：inner_add_add_self (x y : F) 
: ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `InnerProductSpace.Core.re_inner_smul_ofReal_smul_self`：re_inner_smul_ofR
eal_smul_self (x : F) {t : Real} : re ⟪(t : 𝕜) • x, (t : 𝕜) • x⟫ = normSqF x * t
 * t
· 使用定理 `InnerProductSpace.Core.inner_smul_ofReal_left`：inner_smul_ofReal_left (x
 y : F) {t : Real} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t
· 使用定理 `InnerProductSpace.Core.inner_smul_ofReal_right`：inner_smul_ofReal_right 
(x y : F) {t : Real} : ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.Core.normSq.eq_1`：∀ {𝕜 : Type u_1} {F : Type u_3} [ins
t : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [c : PreI
nnerProductSpace.Core 𝕜 …
· 使用定理 `InnerProductSpace.Core.inner_re_symm`：inner_re_symm (x y : F) : re ⟪x, y
⟫ = re ⟪y, x⟫
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
An auxiliary equality useful to prove the **Cauchy–Schwarz inequality**. Here we
 use the
standard argument involving the discriminant of quadratic form.
-/
lemma cauchy_schwarz_aux' (x y : F) (t : ℝ) : 0 ≤ normSqF x * t * t + 2 * re ⟪x, y⟫ * t
    + normSqF y := by
  calc 0 ≤ re ⟪(ofReal t : 𝕜) • x + y, (ofReal t : 𝕜) • x + y⟫ := inner_self_nonneg
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

/-- Another auxiliary equality related with the **Cauchy–Schwarz inequality**: the square of the
seminorm of `⟪x, y⟫ • x - ⟪x, x⟫ • y` is equal to `‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫‖ ^ 2)`.
We use `InnerProductSpace.ofCore.normSq x` etc. (defeq to `is_R_or_C.re ⟪x, x⟫`) instead of
`‖x‖ ^ 2` etc. to avoid extra rewrites when applying it to an `InnerProductSpace`. -/
/-
**InnerProductSpace.Core.cauchy_schwarz_aux** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace.Core`。
形式化陈述：cauchy_schwarz_aux (x y : F) : normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y) = normSqF
 x * (normSqF x * normSqF y - ‖⟪x, y⟫‖ ^ 2)
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `InnerProductSpace.Core.ofReal_normSq_eq_inner_self`：ofReal_normSq_eq_inn
er_self (x : F) : (normSqF x : 𝕜) = ⟪x, x⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductSpace.Core.inner_sub_sub_self`：inner_sub_sub_self (x y : F) 
: ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
· 使用定理 `InnerProductSpace.Core.inner_smul_right`：inner_smul_right (x y : F) {r :
 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫
· 使用定理 `InnerProductSpace.Core.inner_smul_left`：inner_smul_left (x y : F) {r : 𝕜
} : ⟪r • x, y⟫ = r† * ⟪x, y⟫
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `InnerProductSpace.Core.inner_conj_symm`：inner_conj_symm (x y : F) : ⟪y, 
x⟫† = ⟪x, y⟫
· 使用定理 `algebraMap.coe_sub`：coe_sub (a b : R) : (↑(a - b : R) : A) = ↑a - ↑b
· 使用定理 `algebraMap.coe_mul`：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
· 使用定理 `algebraMap.coe_pow`：coe_pow (a : R) (n : Nat) : (↑(a ^ n : R) : A) = (a 
: A) ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
Another auxiliary equality related with the **Cauchy–Schwarz inequality**: the s
quare of the
seminorm of `⟪x, y⟫ • x - ⟪x, x⟫ • y` is equal to `‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 
- ‖⟪x, y⟫‖ ^ 2)`.
We use `InnerProductSpace.ofCore.normSq x` etc. (defeq to `is_R_or_C.re ⟪x, x⟫`)
 instead of
`‖x‖ ^ 2` etc. to avoid extra rewrites when applying it to an `InnerProductSpace
`.
-/
theorem cauchy_schwarz_aux (x y : F) : normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y)
    = normSqF x * (normSqF x * normSqF y - ‖⟪x, y⟫‖ ^ 2) := by
  rw [← @ofReal_inj 𝕜, ofReal_normSq_eq_inner_self]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_ofReal, mul_sub, ←
    ofReal_normSq_eq_inner_self x, ← ofReal_normSq_eq_inner_self y]
  rw [← mul_assoc, mul_conj, RCLike.conj_mul, mul_left_comm, ← inner_conj_symm y, mul_conj]
  push_cast
  ring

/-- **Cauchy–Schwarz inequality**.
We need this for the `PreInnerProductSpace.Core` structure to prove the triangle inequality below
when showing the core is a normed group and to take the quotient.

(This is not intended for general use; see `Analysis.InnerProductSpace.Basic` for a variety of
versions of Cauchy-Schwarz for an inner product space, rather than a `PreInnerProductSpace.Core`).
-/
/-
**InnerProductSpace.Core.inner_mul_inner_self_le** 是 Mathlib 中的一个定理，位于命名空间 `Inne
rProductSpace.Core`。
形式化陈述：inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re 
⟪y, y⟫
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `discrim_le_zero`：discrim_le_zero (h : forall x : K, 0 <= a * (x * x) + b
 * x + c) : discrim a b c <= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `InnerProductSpace.Core.inner_self_nonneg`：inner_self_nonneg {x : F} : 0 
<= re ⟪x, x⟫
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 120 条，此处仅展示前 30 条）

--- 原说明 ---
**Cauchy–Schwarz inequality**.
We need this for the `PreInnerProductSpace.Core` structure to prove the triangle
 inequality below
when showing the core is a normed group and to take the quotient.

(This is not intended for general use; see `Analysis.InnerProductSpace.Basic` fo
r a variety of
versions of Cauchy-Schwarz for an inner product space, rather than a `PreInnerPr
oductSpace.Core`).
-/
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫_𝕜‖) (normSqF y) ≤ 0 by
    rw [norm_inner_symm y x]
    rw [discrim, normSq, normSq, sq] at this
    linarith
  refine discrim_le_zero fun t ↦ ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [← sq, hzero, norm_zero, mul_zero, zero_mul, add_zero]
    obtain ⟨hx, hy⟩ : (0 ≤ normSqF x ∧ 0 ≤ normSqF y) := ⟨inner_self_nonneg, inner_self_nonneg⟩
    positivity
  · have hzero' : ‖⟪x, y⟫‖ ≠ 0 := norm_ne_zero_iff.2 hzero
    convert! cauchy_schwarz_aux' (𝕜 := 𝕜) (⟪x, y⟫ • x) y (t / ‖⟪x, y⟫‖) using 3
    · field_simp
      rw [normSq, normSq, inner_smul_right, inner_smul_left, ← mul_assoc _ _ ⟪x, x⟫,
        mul_conj]
      rw [← ofReal_pow, re_ofReal_mul]
      ring
    · field_simp
      rw [inner_smul_left, mul_comm _ ⟪x, y⟫_𝕜, mul_conj, ← ofReal_pow, ofReal_re]
      ring

/-- (Semi)norm constructed from a `PreInnerProductSpace.Core` structure, defined to be the square
root of the scalar product. -/
@[instance_reducible]
/-
**InnerProductSpace.Core.toNorm** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace.Cor
e`。
形式化陈述：toNorm : Norm F where norm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Semi)norm constructed from a `PreInnerProductSpace.Core` structure, defined to 
be the square
root of the scalar product.
-/
def toNorm : Norm F where norm x := √(re ⟪x, x⟫)

attribute [local instance] toNorm
/-
**InnerProductSpace.Core.norm_eq_sqrt_re_inner** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace.Core`。
形式化陈述：norm_eq_sqrt_re_inner (x : F) : ‖x‖ = √(re ⟪x, x⟫)
参数：x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_sqrt_re_inner (x : F) : ‖x‖ = √(re ⟪x, x⟫) := rfl
/-
**InnerProductSpace.Core.inner_self_eq_norm_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 `
InnerProductSpace.Core`。
形式化陈述：inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖
参数：x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.norm_eq_sqrt_re_inner`：norm_eq_sqrt_re_inner (x :
 F) : ‖x‖ = √(re ⟪x, x⟫)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `InnerProductSpace.Core.inner_self_nonneg`：inner_self_nonneg {x : F} : 0 
<= re ⟪x, x⟫
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
-/
theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_re_inner, ← sqrt_mul inner_self_nonneg, sqrt_mul_self inner_self_nonneg]
/-
**InnerProductSpace.Core.sqrt_normSq_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `InnerPro
ductSpace.Core`。
形式化陈述：sqrt_normSq_eq_norm (x : F) : √(normSqF x) = ‖x‖
参数：x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqrt_normSq_eq_norm (x : F) : √(normSqF x) = ‖x‖ := rfl

/-- Cauchy–Schwarz inequality with norm -/
/-
**InnerProductSpace.Core.norm_inner_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace.Core`。
形式化陈述：norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
参数：x y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonneg_le_nonneg_of_sq_le_sq`：nonneg_le_nonneg_of_sq_le_sq [PosMulStrict
Mono R] [MulPosMono R] {a b : R} (hb : 0 <= b) (h : a * a <= b * b) : a <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.Core.norm_inner_symm`：norm_inner_symm (x y : F) : ‖⟪x,
 y⟫‖ = ‖⟪y, x⟫‖
· 使用定理 `InnerProductSpace.Core.inner_mul_inner_self_le`：inner_mul_inner_self_le 
(x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductSpace.Core.inner_self_eq_norm_mul_norm`：inner_self_eq_norm_m
ul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c

--- 原说明 ---
Cauchy–Schwarz inequality with norm
-/
theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) <|
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := inner_mul_inner_self_le x y
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm]; ring

/-- Seminormed group structure constructed from a `PreInnerProductSpace.Core` structure -/
@[instance_reducible]
/-
**InnerProductSpace.Core.toSeminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Inn
erProductSpace.Core`。
形式化陈述：toSeminormedAddCommGroup : SeminormedAddCommGroup F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed group structure constructed from a `PreInnerProductSpace.Core` struct
ure
-/
def toSeminormedAddCommGroup : SeminormedAddCommGroup F :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this }

attribute [local instance] toSeminormedAddCommGroup

/-- Normed space (which is actually a seminorm in general) structure constructed from a
`PreInnerProductSpace.Core` structure -/
@[instance_reducible]
/-
**InnerProductSpace.Core.toNormedSpace** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSp
ace.Core`。
形式化陈述：toNormedSpace : NormedSpace 𝕜 F where norm_smul_le r x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space (which is actually a seminorm in general) structure constructed fro
m a
`PreInnerProductSpace.Core` structure
-/
def toNormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_re_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
      ofReal_re]
    · simp [sqrt_normSq_eq_norm]
    · positivity

omit c in
/-- Seminormed space core structure constructed from a `PreInnerProductSpace.Core` structure -/
/-
**InnerProductSpace.Core.toSeminormedSpaceCore** 是 Mathlib 中的一个引理，位于命名空间 `InnerP
roductSpace.Core`。
形式化陈述：toSeminormedSpaceCore (c : PreInnerProductSpace.Core 𝕜 F) : SeminormedSpac
e.Core 𝕜 F where norm_nonneg x
参数：c : PreInnerProductSpace.Core 𝕜 F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖

--- 原说明 ---
Seminormed space core structure constructed from a `PreInnerProductSpace.Core` s
tructure
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
/-
**InnerProductSpace.toInner'** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inner product defined by the `InnerProductSpace.Core` structure. We can't reuse
`InnerProductSpace.Core.toInner` because it takes `InnerProductSpace.Core` as an
 explicit
argument.
-/
def toInner' : Inner 𝕜 F :=
  cd.toInner

attribute [local instance] toInner'

local notation "normSqF" => @normSq 𝕜 F _ _ _ _
/-
**InnerProductSpace.inner_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
ace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  ⟨cd.definite _, inner_self_of_eq_zero⟩
/-
**InnerProductSpace.normSq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normSq_eq_zero {x : F} : normSqF x = 0 ↔ x = 0 :=
  Iff.trans
    (by simp only [normSq, ext_iff, map_zero, inner_self_im, and_true])
    (inner_self_eq_zero (𝕜 := 𝕜))
/-
**InnerProductSpace.inner_self_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
ace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

attribute [local instance] toNorm

/-- Normed group structure constructed from an `InnerProductSpace.Core` structure -/
@[instance_reducible]
/-
**InnerProductSpace.toNormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `InnerProduct
Space`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed group structure constructed from an `InnerProductSpace.Core` structure
-/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun _ hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }

section

attribute [local instance] toNormedAddCommGroup

omit cd in
/-- Normed space core structure constructed from an `InnerProductSpace.Core` structure -/
/-
**InnerProductSpace.toNormedSpaceCore** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductSpa
ce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space core structure constructed from an `InnerProductSpace.Core` structu
re
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
/-- In a topological vector space, if the unit ball of a continuous inner product is von Neumann
bounded, then the inner product defines the same topology as the original one. -/
/-
**InnerProductSpace.topology_eq** 是 Mathlib 中的一个引理，位于命名空间 `InnerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a topological vector space, if the unit ball of a continuous inner product is
 von Neumann
bounded, then the inner product defines the same topology as the original one.
-/
lemma topology_eq
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    tF = cd.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  let p : Seminorm 𝕜 F := @normSeminorm 𝕜 F _ cd.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace
  suffices WithSeminorms (fun (i : Fin 1) ↦ p) by
    rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).1 this]
    simp
  have : p.ball 0 1 = {v | re (cd.inner v v) < 1} := by
    ext v
    simp only [ball_normSeminorm, Metric.mem_ball, dist_eq_norm, sub_zero, Set.mem_ofPred_eq, p]
    change √(re (cd.inner v v)) < 1 ↔ re (cd.inner v v) < 1
    conv_lhs => rw [show (1 : ℝ) = √1 by simp]
    rw [sqrt_lt_sqrt_iff]
    exact InnerProductSpace.Core.inner_self_nonneg
  rw [withSeminorms_iff_mem_nhds_isVonNBounded, this]
  refine ⟨?_, h'⟩
  have A : ContinuousAt (fun (v : F) ↦ re (cd.inner v v)) 0 := by fun_prop
  have B : Set.Iio 1 ∈ 𝓝 (re (cd.inner 0 0)) := by
    simp only [InnerProductSpace.Core.inner_zero_left, map_zero]
    exact Iio_mem_nhds (by positivity)
  exact A B

/-- Normed space structure constructed from an `InnerProductSpace.Core` structure, adjusting the
topology to make sure it is defeq to an already existing topology. -/
/-
**InnerProductSpace.toNormedAddCommGroupOfTopology** 是 Mathlib 中的一个定义，位于命名空间 `In
nerProductSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space structure constructed from an `InnerProductSpace.Core` structure, a
djusting the
topology to make sure it is defeq to an already existing topology.
-/
@[reducible] def toNormedAddCommGroupOfTopology
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    NormedAddCommGroup F :=
  NormedAddCommGroup.ofCoreReplaceTopology cd.toNormedSpaceCore (cd.topology_eq h h')

/-- Normed space structure constructed from an `InnerProductSpace.Core` structure, adjusting the
topology to make sure it is defeq to an already existing topology. -/
/-
**InnerProductSpace.toNormedSpaceOfTopology** 是 Mathlib 中的一个定义，位于命名空间 `InnerProd
uctSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space structure constructed from an `InnerProductSpace.Core` structure, a
djusting the
topology to make sure it is defeq to an already existing topology.
-/
@[reducible] def toNormedSpaceOfTopology
    [tF : TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h';
    NormedSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  { norm_smul_le r x := by
      rw [norm_eq_sqrt_re_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
      rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
        ofReal_re]
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
/-
**InnerProductSpace.ofCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (cd : PreInnerProdu
ctSpace.Core 𝕜 F) : InnerProductSpace 𝕜 F
参数：cd : PreInnerProductSpace.Core 𝕜 F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PreInnerProductSpace.Core.conj_inner_symm`：∀ {𝕜 : Type u_4} {F : Type u_
5} [inst : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (s
elf : PreInnerProductSpace.Core…
· 使用定理 `PreInnerProductSpace.Core.add_left`：∀ {𝕜 : Type u_4} {F : Type u_5} [ins
t : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (self : P
reInnerProductSpace.Core…
· 使用定理 `PreInnerProductSpace.Core.smul_left`：∀ {𝕜 : Type u_4} {F : Type u_5} [in
st : RCLike 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   (self : 
PreInnerProductSpace.Core…

--- 原说明 ---
Given a `PreInnerProductSpace.Core` structure on a space, one can use it to turn
the space into a pre-inner product space (i.e., `SeminormedAddCommGroup` and `In
nerProductSpace`).
The `SeminormedAddCommGroup` structure is expected to already be defined with
`InnerProductSpace.ofCore.toSeminormedAddCommGroup`.
-/
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (cd : PreInnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := InnerProductSpace.Core.toNormedSpace
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

end

/-- Given an `InnerProductSpace.Core` structure on a space with a topology, one can use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is expected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroupOfTopology`. -/
@[instance_reducible]
/-
**InnerProductSpace.ofCoreOfTopology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.ofCoreOfTopology [AddCommGroup F] [hF : Module 𝕜 F] [Top
ologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] (cd : Inner
ProductSpace.Core 𝕜 F) (h : ContinuousAt (fun (v : F) => cd.inner v v) 0) (h' : 
IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) : letI : NormedAddCommGroup F
参数：cd : InnerProductSpace.Core 𝕜 F；h : ContinuousAt (fun (v : F) => cd.inner v v
) 0；h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `InnerProductSpace.Core` structure on a space with a topology, one can 
use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is exp
ected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroupOfTopol
ogy`.
-/
def InnerProductSpace.ofCoreOfTopology [AddCommGroup F] [hF : Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (cd : InnerProductSpace.Core 𝕜 F)
    (h : ContinuousAt (fun (v : F) ↦ cd.inner v v) 0)
    (h' : IsVonNBounded 𝕜 {v : F | re (cd.inner v v) < 1}) :
    letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h';
    InnerProductSpace 𝕜 F :=
  letI : NormedAddCommGroup F := cd.toNormedAddCommGroupOfTopology h h'
  letI : NormedSpace 𝕜 F := cd.toNormedSpaceOfTopology h h'
  { cd with
    norm_sq_eq_re_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

/-- A Hilbert space is a complete normed inner product space. -/
@[variable_alias]
/-
**HilbertSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_4) →   (E : Type u_5) →     [inst : RCLike 𝕜] → [inst_1 : Norm
edAddCommGroup E] → [InnerProductSpace 𝕜 E] → [CompleteSpace E] → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hilbert space is a complete normed inner product space.
-/
structure HilbertSpace (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace PUnit

/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InnerProductSpace 𝕜 PUnit where
  inner _ _ := 0
  norm_sq_eq_re_inner := by simp
  conj_inner_symm := by simp
  add_left := by simp
  smul_left := by simp
/-
**PUnit.inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (x y : PUnit.{u_4 + 1}), inner 𝕜 x y = 
0
参数：x y : PUnit.{u_4 + 1}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inner_eq_zero (x y : PUnit) : inner 𝕜 x y = 0 := rfl

end PUnit

end

