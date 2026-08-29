/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum.GCD

/-!
# Hilbert C⋆-modules

A Hilbert C⋆-module is a complex module `E` together with a right `A`-module structure, where `A`
is a C⋆-algebra, and with an `A`-valued inner product. This inner product satisfies the
Cauchy-Schwarz inequality, and induces a norm that makes `E` a normed vector space over `ℂ`.

## Main declarations

+ `CStarModule`: The class containing the Hilbert C⋆-module structure
+ `CStarModule.normedSpaceCore`: The proof that a Hilbert C⋆-module is a normed vector
  space. This can be used with `NormedAddCommGroup.ofCore` and `NormedSpace.ofCore` to create
  the relevant instances on a type of interest.
+ `CStarModule.inner_mul_inner_swap_le`: The statement that
  `⟪x, y⟫ * ⟪y, x⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫`, which can be viewed as a version of the Cauchy-Schwarz
  inequality for Hilbert C⋆-modules.
+ `CStarModule.norm_inner_le`, which states that `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`, i.e. the
  Cauchy-Schwarz inequality.

## Implementation notes

The class `CStarModule A E` requires `E` to already have a `Norm E` instance on it, but
no other norm-related instances. We then include the fact that this norm agrees with the norm
induced by the inner product among the axioms of the class. Furthermore, instead of registering
`NormedAddCommGroup E` and `NormedSpace ℂ E` instances (which might already be present on the type,
and which would send the type class search algorithm on a chase for `A`), we provide a
`NormedSpace.Core` structure which enables downstream users of the class to easily register
these instances themselves on a particular type.

Although the `Norm` is passed as a parameter, it almost never coincides with the norm on the
underlying type, unless that it is a purpose built type, as with the *standard Hilbert C⋆-module*.
However, with generic types already equipped with a norm, the norm as a Hilbert C⋆-module almost
never coincides with the norm on the underlying type. The two notable exceptions to this are when
we view `A` as a C⋆-module over itself, or when `A := ℂ`. For this reason we will later use the
type synonym `WithCStarModule`.

As an example of just how different the norm can be, consider `CStarModule`s `E` and `F` over `A`.
One would like to put a `CStarModule` structure on (a type synonym of) `E × F`, where the `A`-valued
inner product is given, for `x y : E × F`, `⟪x, y⟫_A := ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A`. The norm this
induces satisfies `‖x‖ ^ 2 = ‖⟪x.1, y.1⟫ + ⟪x.2, y.2⟫‖`, but this doesn't coincide with *any*
natural norm on `E × F` unless `A := ℂ`, in which case it is `WithLp 2 (E × F)` because `E × F` is
then an `InnerProductSpace` over `ℂ`.

## References

+ Erin Wittlich. *Formalizing Hilbert Modules in C⋆-algebras with the Lean Proof Assistant*,
  December 2022. Master's thesis, Southern Illinois University Edwardsville.
-/

@[expose] public section

open scoped ComplexOrder RightActions

/--
Definition of `CStarModule` / `CStarModule` 的定义

English:
class CStarModule
  parameters: (A E : Type*) [NonUnitalSemiring A] [StarRing A]
  extends: Inner A E
  axioms and operations (7):
    - inner_add_right({x} {y} {z}) : inner x (y + z) = inner x y + inner x z
    - inner_self_nonneg({x}) : 0 <= inner x x
    - inner_self({x}) : inner x x = 0 ↔ x = 0
    - inner_op_smul_right({a : A} {x y : E}) : inner x (a • y) = a * inner x y
    - inner_smul_right_complex({z : Complex} {x} {y}) : inner x (z • y) = z • inner x y
    - star_inner(x y) : star (inner x y) = inner y x
    - norm_eq_sqrt_norm_inner_self(x) : ‖x‖ = √‖inner x x‖

中文:
类 CStarModule
  参数: (A E : 类型) [NonUnitalSemiring A] [StarRing A]
  继承: Inner A E
  公理与运算 (7 个):
    - inner_add_right({x} {y} {z}) : inner x (y + z) = inner x y + inner x z
    - inner_self_nonneg({x}) : 0 <= inner x x
    - inner_self({x}) : inner x x = 0 ↔ x = 0
    - inner_op_smul_right({a : A} {x y : E}) : inner x (a • y) = a * inner x y
    - inner_smul_right_complex({z : Complex} {x} {y}) : inner x (z • y) = z • inner x y
    - star_inner(x y) : star (inner x y) = inner y x
    - norm_eq_sqrt_norm_inner_self(x) : ‖x‖ = √‖inner x x‖

Depends on / 依赖: NormedDivisionRing, NormedDivisionRing.to_continuousInv
-/
class CStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A]
    [Module Complex A] [AddCommGroup E] [Module Complex E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x} {y} {z} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x} : 0 <= inner x x
  inner_self {x} : inner x x = 0 ↔ x = 0
  inner_op_smul_right {a : A} {x y : E} : inner x (a • y) = a * inner x y
  inner_smul_right_complex {z : Complex} {x} {y} : inner x (z • y) = z • inner x y
  star_inner x y : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self x : ‖x‖ = √‖inner x x‖

attribute [simp] CStarModule.inner_add_right CStarModule.star_inner
  CStarModule.inner_op_smul_right CStarModule.inner_smul_right_complex

namespace CStarModule

section general

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [AddCommGroup E] [Module Complex A]
  [Module Complex E] [PartialOrder A] [SMul A E] [Norm A] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner A x y

@[simp]
/--
lemma `inner_add_left` / 引理 `inner_add_left`

English:
lemma inner_add_left
  given: {x y z : E}
  statement: ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  proof: by
  rw [← star_star (r := ⟪x + y]; rw [z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp]

中文:
引理 inner_add_left
  条件: {x y z : E}
  结论: ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  证明: by
  rw [← star_star (r := ⟪x + y]; rw [z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp]

Depends on / 依赖: inner_add_right, star_add, star_inner, star_star
-/
lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  rw [← star_star (r := ⟪x + y]; rw [z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp]
/--
lemma `inner_op_smul_left` / 引理 `inner_op_smul_left`

English:
lemma inner_op_smul_left
  given: {a : A} {x y : E}
  statement: ⟪a • x, y⟫ = ⟪x, y⟫ * star a
  proof: by
  rw [← star_inner]; simp

中文:
引理 inner_op_smul_left
  条件: {a : A} {x y : E}
  结论: ⟪a • x, y⟫ = ⟪x, y⟫ * star a
  证明: by
  rw [← star_inner]; simp

Depends on / 依赖: star_inner
-/
lemma inner_op_smul_left {a : A} {x y : E} : ⟪a • x, y⟫ = ⟪x, y⟫ * star a := by
  rw [← star_inner]; simp

section StarModule

variable [StarModule Complex A]

@[simp]
/--
lemma `inner_smul_left_complex` / 引理 `inner_smul_left_complex`

English:
lemma inner_smul_left_complex
  given: {z : Complex} {x y : E}
  statement: ⟪z • x, y⟫ = star z • ⟪x, y⟫
  proof: by
  rw [← star_inner]
  simp

@[simp]

中文:
引理 inner_smul_left_complex
  条件: {z : Complex} {x y : E}
  结论: ⟪z • x, y⟫ = star z • ⟪x, y⟫
  证明: by
  rw [← star_inner]
  simp

@[simp]

Depends on / 依赖: NormedDivisionRing, NormedDivisionRing.to_isTopologicalDivisionRing, star_inner, to_isTopologicalDivisionRing
-/
lemma inner_smul_left_complex {z : Complex} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x, y⟫ := by
  rw [← star_inner]
  simp

@[simp]
/--
lemma `inner_smul_left_real` / 引理 `inner_smul_left_real`

English:
lemma inner_smul_left_real
  given: {z : Real} {x y : E}
  statement: ⟪z • x, y⟫ = z • ⟪x, y⟫
  proof: by
  have h₁ : z • x = (z : Complex) • x := by simp
  rw [h₁]; rw [← star_inner]; rw [inner_smul_right_complex]
  simp

@[simp]

中文:
引理 inner_smul_left_real
  条件: {z : 实数} {x y : E}
  结论: ⟪z • x, y⟫ = z • ⟪x, y⟫
  证明: by
  have h₁ : z • x = (z : Complex) • x := by simp
  rw [h₁]; rw [← star_inner]; rw [inner_smul_right_complex]
  simp

@[simp]

Depends on / 依赖: inner_smul_right_complex, star_inner
-/
lemma inner_smul_left_real {z : Real} {x y : E} : ⟪z • x, y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • x = (z : Complex) • x := by simp
  rw [h₁]; rw [← star_inner]; rw [inner_smul_right_complex]
  simp

@[simp]
/--
lemma `inner_smul_right_real` / 引理 `inner_smul_right_real`

English:
lemma inner_smul_right_real
  given: {z : Real} {x y : E}
  statement: ⟪x, z • y⟫ = z • ⟪x, y⟫
  proof: by
  have h₁ : z • y = (z : Complex) • y := by simp
  rw [h₁]; rw [← star_inner]; rw [inner_smul_left_complex]
  simp

中文:
引理 inner_smul_right_real
  条件: {z : 实数} {x y : E}
  结论: ⟪x, z • y⟫ = z • ⟪x, y⟫
  证明: by
  have h₁ : z • y = (z : Complex) • y := by simp
  rw [h₁]; rw [← star_inner]; rw [inner_smul_left_complex]
  simp

Depends on / 依赖: inner_smul_left_complex, star_inner
-/
lemma inner_smul_right_real {z : Real} {x y : E} : ⟪x, z • y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • y = (z : Complex) • y := by simp
  rw [h₁]; rw [← star_inner]; rw [inner_smul_left_complex]
  simp

/--
Definition of `innerₛₗ` / `innerₛₗ` 的定义

English:
definition innerₛₗ
  signature: : E ->ₗ⋆[Complex] E ->ₗ[Complex] A where
  body: { toFun := fun y => ⟪x, y⟫
               map_add' := fun z y => by simp
               map_smul' := fun z y => by simp }
  map_add' z y := by ext; simp
  map_smul' z y := by ext; simp

中文:
定义 innerₛₗ
  签名: : E ->ₗ⋆[Complex] E ->ₗ[Complex] A where
  定义体: { toFun := fun y => ⟪x, y⟫
               map_add' := fun z y => by simp
               map_smul' := fun z y => by simp }
  map_add' z y := by ext; simp
  map_smul' z y := by ext; simp
-/
def innerₛₗ : E ->ₗ⋆[Complex] E ->ₗ[Complex] A where
  toFun x := { toFun := fun y => ⟪x, y⟫
               map_add' := fun z y => by simp
               map_smul' := fun z y => by simp }
  map_add' z y := by ext; simp
  map_smul' z y := by ext; simp

/--
lemma `innerₛₗ_apply` / 引理 `innerₛₗ_apply`

English:
lemma innerₛₗ_apply
  given: {x y : E}
  statement: innerₛₗ x y = ⟪x, y⟫
  proof: rfl

中文:
引理 innerₛₗ_apply
  条件: {x y : E}
  结论: innerₛₗ x y = ⟪x, y⟫
  证明: rfl
-/
lemma innerₛₗ_apply {x y : E} : innerₛₗ x y = ⟪x, y⟫ := rfl

/--
lemma `inner_zero_right` / 引理 `inner_zero_right`

English:
lemma inner_zero_right
  given: {x : E}
  statement: ⟪x, 0⟫ = 0
  proof: by simp [← innerₛₗ_apply]

中文:
引理 inner_zero_right
  条件: {x : E}
  结论: ⟪x, 0⟫ = 0
  证明: by simp [← innerₛₗ_apply]
-/
@[simp] lemma inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by simp [← innerₛₗ_apply]
/--
lemma `inner_zero_left` / 引理 `inner_zero_left`

English:
lemma inner_zero_left
  given: {x : E}
  statement: ⟪0, x⟫ = 0
  proof: by simp [← innerₛₗ_apply]

中文:
引理 inner_zero_left
  条件: {x : E}
  结论: ⟪0, x⟫ = 0
  证明: by simp [← innerₛₗ_apply]
-/
@[simp] lemma inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by simp [← innerₛₗ_apply]
/--
lemma `inner_neg_right` / 引理 `inner_neg_right`

English:
lemma inner_neg_right
  given: {x y : E}
  statement: ⟪x, -y⟫ = -⟪x, y⟫
  proof: by simp [← innerₛₗ_apply]

中文:
引理 inner_neg_right
  条件: {x y : E}
  结论: ⟪x, -y⟫ = -⟪x, y⟫
  证明: by simp [← innerₛₗ_apply]
-/
@[simp] lemma inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ := by simp [← innerₛₗ_apply]
/--
lemma `inner_neg_left` / 引理 `inner_neg_left`

English:
lemma inner_neg_left
  given: {x y : E}
  statement: ⟪-x, y⟫ = -⟪x, y⟫
  proof: by simp [← innerₛₗ_apply]

中文:
引理 inner_neg_left
  条件: {x y : E}
  结论: ⟪-x, y⟫ = -⟪x, y⟫
  证明: by simp [← innerₛₗ_apply]
-/
@[simp] lemma inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ := by simp [← innerₛₗ_apply]
/--
lemma `inner_sub_right` / 引理 `inner_sub_right`

English:
lemma inner_sub_right
  given: {x y z : E}
  statement: ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
  proof: by
  simp [← innerₛₗ_apply]

中文:
引理 inner_sub_right
  条件: {x y z : E}
  结论: ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
  证明: by
  simp [← innerₛₗ_apply]
-/
@[simp] lemma inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [← innerₛₗ_apply]
/--
lemma `inner_sub_left` / 引理 `inner_sub_left`

English:
lemma inner_sub_left
  given: {x y z : E}
  statement: ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
  proof: by
  simp [← innerₛₗ_apply]

@[simp]

中文:
引理 inner_sub_left
  条件: {x y z : E}
  结论: ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
  证明: by
  simp [← innerₛₗ_apply]

@[simp]
-/
@[simp] lemma inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [← innerₛₗ_apply]

@[simp]
/--
lemma `inner_sum_right` / 引理 `inner_sum_right`

English:
lemma inner_sum_right
  given: {ι : Type*} {s : Finset ι} {x : E} {y : ι -> E}
  proof: map_sum (innerₛₗ x) ..

@[simp]

中文:
引理 inner_sum_right
  条件: {ι : 类型} {s : Finset ι} {x : E} {y : ι -> E}
  证明: map_sum (innerₛₗ x) ..

@[simp]

Depends on / 依赖: map_sum
-/
lemma inner_sum_right {ι : Type*} {s : Finset ι} {x : E} {y : ι -> E} :
    ⟪x, ∑ i in s, y i⟫ = ∑ i in s, ⟪x, y i⟫ :=
  map_sum (innerₛₗ x) ..

@[simp]
/--
lemma `inner_sum_left` / 引理 `inner_sum_left`

English:
lemma inner_sum_left
  given: {ι : Type*} {s : Finset ι} {x : ι -> E} {y : E}
  proof: map_sum (innerₛₗ.flip y) ..

中文:
引理 inner_sum_left
  条件: {ι : 类型} {s : Finset ι} {x : ι -> E} {y : E}
  证明: map_sum (innerₛₗ.flip y) ..

Depends on / 依赖: map_sum
-/
lemma inner_sum_left {ι : Type*} {s : Finset ι} {x : ι -> E} {y : E} :
    ⟪∑ i in s, x i, y⟫ = ∑ i in s, ⟪x i, y⟫ :=
  map_sum (innerₛₗ.flip y) ..

end StarModule

@[simp]
/--
lemma `isSelfAdjoint_inner_self` / 引理 `isSelfAdjoint_inner_self`

English:
lemma isSelfAdjoint_inner_self
  given: {x : E}
  statement: IsSelfAdjoint ⟪x, x⟫
  proof: star_inner _ _

中文:
引理 isSelfAdjoint_inner_self
  条件: {x : E}
  结论: IsSelfAdjoint ⟪x, x⟫
  证明: star_inner _ _

Depends on / 依赖: star_inner
-/
lemma isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint ⟪x, x⟫ := star_inner _ _

end general

section norm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [AddCommGroup E]
  [Module Complex E] [SMul A E] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner A x y

open scoped InnerProductSpace in
/-- The norm associated with a Hilbert C⋆-module. It is not registered as a norm, since a type
might already have a norm defined on it. -/
@[instance_reducible]
/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: (A : Type*) {E : Type*} [Norm A] [Inner A E]
  body: √‖⟪x, x⟫_A‖

中文:
定义 norm
  签名: (A : 类型) {E : 类型} [Norm A] [Inner A E]
  定义体: √‖⟪x, x⟫_A‖
-/
noncomputable def norm (A : Type*) {E : Type*} [Norm A] [Inner A E] : Norm E where
  norm x := √‖⟪x, x⟫_A‖

section
include A

variable (A)

/--
lemma `norm_sq_eq` / 引理 `norm_sq_eq`

English:
lemma norm_sq_eq
  given: {x : E}
  statement: ‖x‖ ^ 2 = ‖⟪x, x⟫‖
  proof: by simp [norm_eq_sqrt_norm_inner_self (A := A)]

中文:
引理 norm_sq_eq
  条件: {x : E}
  结论: ‖x‖ ^ 2 = ‖⟪x, x⟫‖
  证明: by simp [norm_eq_sqrt_norm_inner_self (A := A)]

Depends on / 依赖: norm_eq_sqrt_norm_inner_self
-/
lemma norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]

/--
lemma `norm_nonneg` / 引理 `norm_nonneg`

English:
lemma norm_nonneg
  given: {x : E}
  statement: 0 <= ‖x‖
  proof: by simp [norm_eq_sqrt_norm_inner_self (A := A)]

中文:
引理 norm_nonneg
  条件: {x : E}
  结论: 0 <= ‖x‖
  证明: by simp [norm_eq_sqrt_norm_inner_self (A := A)]
-/
protected lemma norm_nonneg {x : E} : 0 <= ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]

/--
lemma `norm_pos` / 引理 `norm_pos`

English:
lemma norm_pos
  given: {x : E} (hx : x != 0)
  statement: 0 < ‖x‖
  proof: by
  simp only [norm_eq_sqrt_norm_inner_self (A := A), Real.sqrt_pos, norm_pos_iff]
  intro H
  rw [inner_self] at H
  exact hx H

中文:
引理 norm_pos
  条件: {x : E} (hx : x != 0)
  结论: 0 < ‖x‖
  证明: by
  simp only [norm_eq_sqrt_norm_inner_self (A := A), Real.sqrt_pos, norm_pos_iff]
  intro H
  rw [inner_self] at H
  exact hx H
-/
protected lemma norm_pos {x : E} (hx : x != 0) : 0 < ‖x‖ := by
  simp only [norm_eq_sqrt_norm_inner_self (A := A), Real.sqrt_pos, norm_pos_iff]
  intro H
  rw [inner_self] at H
  exact hx H

/--
lemma `norm_zero` / 引理 `norm_zero`

English:
lemma norm_zero
  statement: ‖(0 : E)‖ = 0
  proof: by simp [norm_eq_sqrt_norm_inner_self (A := A)]

中文:
引理 norm_zero
  结论: ‖(0 : E)‖ = 0
  证明: by simp [norm_eq_sqrt_norm_inner_self (A := A)]
-/
protected lemma norm_zero : ‖(0 : E)‖ = 0 := by simp [norm_eq_sqrt_norm_inner_self (A := A)]

/--
lemma `norm_zero_iff` / 引理 `norm_zero_iff`

English:
lemma norm_zero_iff
  given: (x : E)
  statement: ‖x‖ = 0 ↔ x = 0
  proof: ⟨fun h => by simpa [norm_eq_sqrt_norm_inner_self (A := A), inner_self] using h,
    fun h => by simp [h, norm_eq_sqrt_norm_inner_self (A := A)]⟩

中文:
引理 norm_zero_iff
  条件: (x : E)
  结论: ‖x‖ = 0 ↔ x = 0
  证明: ⟨fun h => by simpa [norm_eq_sqrt_norm_inner_self (A := A), inner_self] using h,
    fun h => by simp [h, norm_eq_sqrt_norm_inner_self (A := A)]⟩

Depends on / 依赖: inner_self, norm_eq_sqrt_norm_inner_self
-/
lemma norm_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0 :=
  ⟨fun h => by simpa [norm_eq_sqrt_norm_inner_self (A := A), inner_self] using h,
    fun h => by simp [h, norm_eq_sqrt_norm_inner_self (A := A)]⟩

end

variable [StarOrderedRing A]

open scoped InnerProductSpace in
/--
lemma `inner_mul_inner_swap_le` / 引理 `inner_mul_inner_swap_le`

English:
lemma inner_mul_inner_swap_le
  given: {x y : E}
  statement: ⟪x, y⟫ * ⟪y, x⟫ <= ‖x‖ ^ 2 • ⟪y, y⟫
  proof: by
  rcases eq_or_ne x 0 with h | h
  · simp [h, CStarModule.norm_zero A (E := E)]
  · have h₁ : forall (a : A),
        (0 : A) <= ‖x‖ ^ 2 • (a * star a) - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := fun a => by
      calc (0 : A) <= ⟪a •

中文:
引理 inner_mul_inner_swap_le
  条件: {x y : E}
  结论: ⟪x, y⟫ * ⟪y, x⟫ <= ‖x‖ ^ 2 • ⟪y, y⟫
  证明: by
  rcases eq_or_ne x 0 with h | h
  · simp [h, CStarModule.norm_zero A (E := E)]
  · have h₁ : forall (a : A),
        (0 : A) <= ‖x‖ ^ 2 • (a * star a) - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := fun a => by
      calc (0 : A) <= ⟪a •

Depends on / 依赖: CStarModule, CStarModule.norm_zero, eq_or_ne, inner_op_smul_right, inner_self_nonneg, inner_sub_right, norm_zero
-/
lemma inner_mul_inner_swap_le {x y : E} : ⟪x, y⟫ * ⟪y, x⟫ <= ‖x‖ ^ 2 • ⟪y, y⟫ := by
  rcases eq_or_ne x 0 with h | h
  · simp [h, CStarModule.norm_zero A (E := E)]
  · have h₁ : forall (a : A),
        (0 : A) <= ‖x‖ ^ 2 • (a * star a) - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := fun a => by
      calc (0 : A) <= ⟪a • x - ‖x‖ ^ 2 • y, a • x - ‖x‖ ^ 2 • y⟫_A := by
                      exact inner_self_nonneg
            _ = a * ⟪x, x⟫ * star a - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      simp only [inner_sub_right, inner_op_smul_right, inner_sub_left,
                        inner_op_smul_left, inner_smul_left_real, mul_sub, mul_smul_comm,
                        inner_smul_right_real, smul_sub, mul_assoc]
                      abel
            _ <= ‖x‖ ^ 2 • (a * star a) - ‖x‖ ^ 2 • (a * ⟪y, x⟫)
                  - ‖x‖ ^ 2 • (⟪x, y⟫ * star a) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      gcongr
                      calc _ <= ‖⟪x, x⟫_A‖ • (a * star a) :=
                          CStarAlgebra.star_right_conjugate_le_norm_smul
                        _ = (√‖⟪x, x⟫_A‖) ^ 2 • (a * star a) := by
                          rw [Real.sq_sqrt]
                          positivity
                        _ = ‖x‖ ^ 2 • (a * star a) := by rw [← norm_eq_sqrt_norm_inner_self]
    specialize h₁ ⟪x, y⟫
    simp only [star_inner, sub_self, zero_sub, le_neg_add_iff_add_le, add_zero] at h₁
    rwa [smul_le_smul_iff_of_pos_left (pow_pos (CStarModule.norm_pos A h) _)] at h₁

open scoped InnerProductSpace in
variable (E) in
/--
lemma `norm_inner_le` / 引理 `norm_inner_le`

English:
lemma norm_inner_le
  given: {x y : E}
  statement: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
  proof: by
  have := calc ‖⟪x, y⟫‖ ^ 2 = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
                rw [← star_inner x]; rw [CStarRing.norm_self_mul_star]; rw [pow_two]
    _ <= ‖‖x‖ ^ 2 • ⟪y, y⟫‖ := by
                refine CStarAlgebra.norm_le_norm_of_nonneg_of_le ?_ inner_mul_inner_swap_le
                rw [← star_inner

中文:
引理 norm_inner_le
  条件: {x y : E}
  结论: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
  证明: by
  have := calc ‖⟪x, y⟫‖ ^ 2 = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
                rw [← star_inner x]; rw [CStarRing.norm_self_mul_star]; rw [pow_two]
    _ <= ‖‖x‖ ^ 2 • ⟪y, y⟫‖ := by
                refine CStarAlgebra.norm_le_norm_of_nonneg_of_le ?_ inner_mul_inner_swap_le
                rw [← star_inner

Depends on / 依赖: CStarAlgebra, CStarAlgebra.norm_le_norm_of_nonneg_of_le, CStarRing, CStarRing.norm_self_mul_star, Real.sq_sqrt, inner_mul_inner_swap_le, mul_pow, mul_star_self_nonneg, norm_eq_sqrt_norm_inner_self, norm_le_norm_of_nonneg_of_le, norm_nonneg, norm_self_mul_star, norm_smul, pow_le_po, pow_two, sq_sqrt, star_inner
-/
lemma norm_inner_le {x y : E} : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ := by
  have := calc ‖⟪x, y⟫‖ ^ 2 = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
                rw [← star_inner x]; rw [CStarRing.norm_self_mul_star]; rw [pow_two]
    _ <= ‖‖x‖ ^ 2 • ⟪y, y⟫‖ := by
                refine CStarAlgebra.norm_le_norm_of_nonneg_of_le ?_ inner_mul_inner_swap_le
                rw [← star_inner x]
                exact mul_star_self_nonneg ⟪x, y⟫_A
    _ = ‖x‖ ^ 2 * ‖⟪y, y⟫‖ := by simp [norm_smul]
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
                simp only [norm_eq_sqrt_norm_inner_self (A := A), norm_nonneg, Real.sq_sqrt]
    _ = (‖x‖ * ‖y‖) ^ 2 := by simp only [mul_pow]
  refine (pow_le_pow_iff_left₀ (norm_nonneg ⟪x, y⟫_A) ?_ (by simp)).mp this
  exact mul_nonneg (CStarModule.norm_nonneg A) (CStarModule.norm_nonneg A)

include A in
variable (A) in
/--
lemma `norm_triangle` / 引理 `norm_triangle`

English:
lemma norm_triangle
  given: (x y : E)
  statement: ‖x + y‖ <= ‖x‖ + ‖y‖
  proof: by
  have h : ‖x + y‖ ^ 2 <= (‖x‖ + ‖y‖) ^ 2 := by
    calc _ <= ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
          simp only [norm_eq_sqrt_norm_inner_self (A := A), inner_add_right, inner_add_left,
            ← add_assoc, norm_nonneg, Real.sq_sqrt]
          exact norm_add₃_le
      _ <= ‖⟪x,

中文:
引理 norm_triangle
  条件: (x y : E)
  结论: ‖x + y‖ <= ‖x‖ + ‖y‖
  证明: by
  have h : ‖x + y‖ ^ 2 <= (‖x‖ + ‖y‖) ^ 2 := by
    calc _ <= ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
          simp only [norm_eq_sqrt_norm_inner_self (A := A), inner_add_right, inner_add_left,
            ← add_assoc, norm_nonneg, Real.sq_sqrt]
          exact norm_add₃_le
      _ <= ‖⟪x,
-/
protected lemma norm_triangle (x y : E) : ‖x + y‖ <= ‖x‖ + ‖y‖ := by
  have h : ‖x + y‖ ^ 2 <= (‖x‖ + ‖y‖) ^ 2 := by
    calc _ <= ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
          simp only [norm_eq_sqrt_norm_inner_self (A := A), inner_add_right, inner_add_left,
            ← add_assoc, norm_nonneg, Real.sq_sqrt]
          exact norm_add₃_le
      _ <= ‖⟪x, x⟫‖ + ‖⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by gcongr; exact norm_add_le _ _
      _ <= ‖⟪x, x⟫‖ + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖⟪y, y⟫‖ := by gcongr <;> exact norm_inner_le E
      _ = ‖x‖ ^ 2 + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
          simp [norm_eq_sqrt_norm_inner_self (A := A)]
      _ = (‖x‖ + ‖y‖) ^ 2 := by simp only [add_pow_two, add_left_inj]; ring
  refine (pow_le_pow_iff_left₀ (CStarModule.norm_nonneg A) ?_ (by simp)).mp h
  exact add_nonneg (CStarModule.norm_nonneg A) (CStarModule.norm_nonneg A)

include A in
variable (A) in
/--
lemma `normedSpaceCore` / 引理 `normedSpaceCore`

English:
lemma normedSpaceCore
  statement: NormedSpace.Core Complex E where
  proof: (CStarModule.norm_nonneg A)
  norm_eq_zero_iff x := norm_zero_iff A x
  norm_smul c x := by simp [norm_eq_sqrt_norm_inner_self (A := A), norm_smul, ← mul_assoc]
  norm_triangle x y := CStarModule.norm_triangle A x y

中文:
引理 normedSpaceCore
  结论: NormedSpace.Core Complex E where
  证明: (CStarModule.norm_nonneg A)
  norm_eq_zero_iff x := norm_zero_iff A x
  norm_smul c x := by simp [norm_eq_sqrt_norm_inner_self (A := A), norm_smul, ← mul_assoc]
  norm_triangle x y := CStarModule.norm_triangle A x y

Depends on / 依赖: CStarModule, CStarModule.norm_nonneg, norm_nonneg
-/
lemma normedSpaceCore : NormedSpace.Core Complex E where
  norm_nonneg _ := (CStarModule.norm_nonneg A)
  norm_eq_zero_iff x := norm_zero_iff A x
  norm_smul c x := by simp [norm_eq_sqrt_norm_inner_self (A := A), norm_smul, ← mul_assoc]
  norm_triangle x y := CStarModule.norm_triangle A x y

variable (A) in
/--
Definition of `normedAddCommGroup` / `normedAddCommGroup` 的定义

English:
abbreviation normedAddCommGroup
  signature: : NormedAddCommGroup E
  body: NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

中文:
缩写 normedAddCommGroup
  签名: : NormedAddCommGroup E
  定义体: NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

Depends on / 依赖: CStarModule, CStarModule.normedSpaceCore, NormedAddCommGroup, NormedAddCommGroup.ofCore, normedSpaceCore, ofCore
-/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup E :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

open scoped InnerProductSpace in
/--
lemma `norm_eq_csSup` / 引理 `norm_eq_csSup`

English:
lemma norm_eq_csSup
  given: (v : E)
  proof: by
  let instNACG : NormedAddCommGroup E := NormedAddCommGroup.ofCore (normedSpaceCore A)
  let instNS : NormedSpace Complex E := .ofCore (normedSpaceCore A)
refine Eq.symm IsGreatest.csSup_eq ⟨⟨‖v‖⁻¹ • v, ?_, ?_⟩, ?_⟩
  · simpa only [norm_smul, norm_inv, norm_norm] using inv_mul_le_one_of_le₀ le_rf

中文:
引理 norm_eq_csSup
  条件: (v : E)
  证明: by
  let instNACG : NormedAddCommGroup E := NormedAddCommGroup.ofCore (normedSpaceCore A)
  let instNS : NormedSpace Complex E := .ofCore (normedSpaceCore A)
refine Eq.symm IsGreatest.csSup_eq ⟨⟨‖v‖⁻¹ • v, ?_, ?_⟩, ?_⟩
  · simpa only [norm_smul, norm_inv, norm_norm] using inv_mul_le_one_of_le₀ le_rf

Depends on / 依赖: Eq.symm, IsGreatest, IsGreatest.csSup_eq, NormedAddCommGroup, NormedAddCommGroup.ofCore, NormedSpace, csSup_eq, instNACG, instNS, le_rfl, mul_assoc, norm_inner_le, norm_inv, norm_norm, norm_smul, norm_sq_eq, normedSpaceCore, ofCore, pow_two
-/
lemma norm_eq_csSup (v : E) :
    ‖v‖ = sSup { ‖⟪w, v⟫_A‖ | (w : E) (_ : ‖w‖ <= 1) } := by
  let instNACG : NormedAddCommGroup E := NormedAddCommGroup.ofCore (normedSpaceCore A)
  let instNS : NormedSpace Complex E := .ofCore (normedSpaceCore A)
refine Eq.symm IsGreatest.csSup_eq ⟨⟨‖v‖⁻¹ • v, ?_, ?_⟩, ?_⟩
  · simpa only [norm_smul, norm_inv, norm_norm] using inv_mul_le_one_of_le₀ le_rfl (by positivity)
  · simp [norm_smul, ← norm_sq_eq, pow_two, ← mul_assoc]
  · rintro - ⟨w, hw, rfl⟩
    calc _ <= ‖w‖ * ‖v‖ := norm_inner_le E
      _ <= 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := by simp

end norm

section NormedAddCommGroup

open scoped InnerProductSpace

/- Note: one generally creates a `CStarModule` instance for a type `E` first before getting the
`NormedAddCommGroup` and `NormedSpace` instances via `CStarModule.normedSpaceCore`, especially by
using `NormedAddCommGroup.ofCoreReplaceAll` and `NormedSpace.ofCore`. See
`Analysis.CStarAlgebra.Module.Constructions` for examples. -/
variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [SMul A E]
  [NormedAddCommGroup E] [NormedSpace Complex E] [CStarModule A E]

/--
Definition of `innerSL` / `innerSL` 的定义

English:
definition innerSL
  signature: : E ->L⋆[Complex] E ->L[Complex] A
  body: LinearMap.mkContinuous₂ (innerₛₗ : E ->ₗ⋆[Complex] E ->ₗ[Complex] A) 1 fun x y => by
    simp [innerₛₗ_apply, norm_inner_le E]

中文:
定义 innerSL
  签名: : E ->L⋆[Complex] E ->L[Complex] A
  定义体: LinearMap.mkContinuous₂ (innerₛₗ : E ->ₗ⋆[Complex] E ->ₗ[Complex] A) 1 fun x y => by
    simp [innerₛₗ_apply, norm_inner_le E]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, norm_inner_le
-/
noncomputable def innerSL : E ->L⋆[Complex] E ->L[Complex] A :=
LinearMap.mkContinuous₂ (innerₛₗ : E ->ₗ⋆[Complex] E ->ₗ[Complex] A) 1 fun x y => by
    simp [innerₛₗ_apply, norm_inner_le E]

/--
lemma `innerSL_apply` / 引理 `innerSL_apply`

English:
lemma innerSL_apply
  given: {x y : E}
  statement: innerSL x y = ⟪x, y⟫_A
  proof: rfl

@[continuity, fun_prop]

中文:
引理 innerSL_apply
  条件: {x y : E}
  结论: innerSL x y = ⟪x, y⟫_A
  证明: rfl

@[continuity, fun_prop]
-/
lemma innerSL_apply {x y : E} : innerSL x y = ⟪x, y⟫_A := rfl

@[continuity, fun_prop]
/--
lemma `continuous_inner` / 引理 `continuous_inner`

English:
lemma continuous_inner
  statement: Continuous (fun x : E × E => ⟪x.1, x.2⟫_A)
  proof: by
  simp_rw [← innerSL_apply]
  fun_prop

中文:
引理 continuous_inner
  结论: Continuous (fun x : E × E => ⟪x.1, x.2⟫_A)
  证明: by
  simp_rw [← innerSL_apply]
  fun_prop

Depends on / 依赖: fun_prop, innerSL_apply, simp_rw
-/
lemma continuous_inner : Continuous (fun x : E × E => ⟪x.1, x.2⟫_A) := by
  simp_rw [← innerSL_apply]
  fun_prop

end NormedAddCommGroup

end CStarModule
