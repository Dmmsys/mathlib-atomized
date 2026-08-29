/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finsupp.SMulWithZero

/-!
# The pointwise product on `Finsupp`.

For the convolution product on `Finsupp` when the domain has a binary operation,
see the type synonyms `AddMonoidAlgebra`
(which is in turn used to define `Polynomial` and `MvPolynomial`)
and `MonoidAlgebra`.
-/

@[expose] public section


noncomputable section

open Finset

universe u₁ u₂ u₃ u₄ u₅

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace Finsupp

/-! ### Declarations about the pointwise product on `Finsupp`s -/


section

variable [MulZeroClass β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (α ->₀ β)
  body: ⟨zipWith (· * ·) (mul_zero 0)⟩

中文:
实例 :
  签名: Mul (α ->₀ β)
  定义体: ⟨zipWith (· * ·) (mul_zero 0)⟩

Depends on / 依赖: Mcongr, PFunctor, PFunctor.M.dest, Quot.factor_mk_eq, Quot.lift, Quot.mk, abs_map, comp_map, factor_mk_eq, mul_zero, zipWith
-/
instance : Mul (α ->₀ β) :=
  ⟨zipWith (· * ·) (mul_zero 0)⟩

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (g₁ g₂ : α ->₀ β)
  statement: ⇑(g₁ * g₂) = g₁ * g₂
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (g₁ g₂ : α ->₀ β)
  结论: ⇑(g₁ * g₂) = g₁ * g₂
  证明: rfl

@[simp]

Depends on / 依赖: Cofix.corec, Cofix.dest, abs_map, abs_repr, comp_map, corecF_eq
-/
theorem coe_mul (g₁ g₂ : α ->₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: {g₁ g₂ : α ->₀ β} {a : α}
  statement: (g₁ * g₂) a = g₁ a * g₂ a
  proof: rfl

@[simp]

中文:
定理 mul_apply
  条件: {g₁ g₂ : α ->₀ β} {a : α}
  结论: (g₁ * g₂) a = g₁ a * g₂ a
  证明: rfl

@[simp]

Depends on / 依赖: Cofix.bisim_aux, Or.inr, Quot.factor_mk_eq, Quot.mk, bisim_aux, comp_map, factor_mk_eq
-/
theorem mul_apply {g₁ g₂ : α ->₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl

@[simp]
/--
theorem `single_mul` / 定理 `single_mul`

English:
theorem single_mul
  given: (a : α) (b₁ b₂ : β)
  statement: single a (b₁ * b₂) = single a b₁ * single a b₂
  proof: (zipWith_single_single _ _ _ _ _).symm

中文:
定理 single_mul
  条件: (a : α) (b₁ b₂ : β)
  结论: single a (b₁ * b₂) = single a b₁ * single a b₂
  证明: (zipWith_single_single _ _ _ _ _).symm

Depends on / 依赖: Cofix.bisim_rel, PFunctor, PFunctor.map_eq, Quot.sound, abs_map, bisim_rel, liftr_iff, map_eq, zipWith_single_single
-/
theorem single_mul (a : α) (b₁ b₂ : β) : single a (b₁ * b₂) = single a b₁ * single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm

/--
lemma `support_mul_subset_left` / 引理 `support_mul_subset_left`

English:
lemma support_mul_subset_left
  given: {g₁ g₂ : α ->₀ β}
  proof: fun x hx => by
  aesop

中文:
引理 support_mul_subset_left
  条件: {g₁ g₂ : α ->₀ β}
  证明: fun x hx => by
  aesop
-/
lemma support_mul_subset_left {g₁ g₂ : α ->₀ β} :
    (g₁ * g₂).support subseteq g₁.support := fun x hx => by
  aesop

/--
lemma `support_mul_subset_right` / 引理 `support_mul_subset_right`

English:
lemma support_mul_subset_right
  given: {g₁ g₂ : α ->₀ β}
  proof: fun x hx => by
  aesop

中文:
引理 support_mul_subset_right
  条件: {g₁ g₂ : α ->₀ β}
  证明: fun x hx => by
  aesop
-/
lemma support_mul_subset_right {g₁ g₂ : α ->₀ β} :
    (g₁ * g₂).support subseteq g₂.support := fun x hx => by
  aesop

/--
theorem `support_mul` / 定理 `support_mul`

English:
theorem support_mul
  given: [DecidableEq α] {g₁ g₂ : α ->₀ β}
  proof: subset_inter support_mul_subset_left support_mul_subset_right

中文:
定理 support_mul
  条件: [DecidableEq α] {g₁ g₂ : α ->₀ β}
  证明: subset_inter support_mul_subset_left support_mul_subset_right

Depends on / 依赖: subset_inter, support_mul_subset_left, support_mul_subset_right
-/
theorem support_mul [DecidableEq α] {g₁ g₂ : α ->₀ β} :
    (g₁ * g₂).support subseteq g₁.support inter g₂.support :=
  subset_inter support_mul_subset_left support_mul_subset_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulZeroClass (α ->₀ β)
  body: DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

中文:
实例 :
  签名: MulZeroClass (α ->₀ β)
  定义体: DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulZeroClass, coe_injective, coe_mul, coe_zero, mulZeroClass
-/
instance : MulZeroClass (α ->₀ β) :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: β] : SemigroupWithZero (α ->₀ β)
  body: DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

中文:
实例 [SemigroupWithZero
  签名: β] : SemigroupWithZero (α ->₀ β)
  定义体: DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semigroupWithZero, coe_injective, coe_mul, coe_zero, semigroupWithZero
-/
instance [SemigroupWithZero β] : SemigroupWithZero (α ->₀ β) :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: β] : NonUnitalNonAssocSemiring (α ->₀ β)
  body: DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 [NonUnitalNonAssocSemiring
  签名: β] : NonUnitalNonAssocSemiring (α ->₀ β)
  定义体: DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalNonAssocSemiring, coe_add, coe_injective, coe_mul, coe_zero, nonUnitalNonAssocSemiring
-/
instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α ->₀ β) :=
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: β] : NonUnitalSemiring (α ->₀ β)
  body: DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 [NonUnitalSemiring
  签名: β] : NonUnitalSemiring (α ->₀ β)
  定义体: DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalSemiring, coe_add, coe_injective, coe_mul, coe_zero, nonUnitalSemiring
-/
instance [NonUnitalSemiring β] : NonUnitalSemiring (α ->₀ β) :=
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: β] : NonUnitalCommSemiring (α ->₀ β)
  body: DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

中文:
实例 [NonUnitalCommSemiring
  签名: β] : NonUnitalCommSemiring (α ->₀ β)
  定义体: DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalCommSemiring, coe_add, coe_injective, coe_mul, coe_zero, nonUnitalCommSemiring
-/
instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α ->₀ β) :=
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: β] : NonUnitalNonAssocRing (α ->₀ β)
  body: DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [NonUnitalNonAssocRing
  签名: β] : NonUnitalNonAssocRing (α ->₀ β)
  定义体: DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalNonAssocRing, coe_add, coe_injective, coe_mul, coe_neg, coe_sub, coe_zero, nonUnitalNonAssocRing
-/
instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α ->₀ β) :=
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: β] : NonUnitalRing (α ->₀ β)
  body: DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 [NonUnitalRing
  签名: β] : NonUnitalRing (α ->₀ β)
  定义体: DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalRing, coe_add, coe_injective, coe_mul, coe_neg, coe_sub, coe_zero, nonUnitalRing
-/
instance [NonUnitalRing β] : NonUnitalRing (α ->₀ β) :=
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: β] : NonUnitalCommRing (α ->₀ β)
  body: DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [NonUnitalCommRing
  签名: β] : NonUnitalCommRing (α ->₀ β)
  定义体: DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.nonUnitalCommRing, coe_add, coe_injective, coe_mul, coe_neg, coe_sub, coe_zero, nonUnitalCommRing
-/
instance [NonUnitalCommRing β] : NonUnitalCommRing (α ->₀ β) :=
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/--
lemma `pointwise_smul_support_finite` / 引理 `pointwise_smul_support_finite`

English:
lemma pointwise_smul_support_finite
  statement: [Zero γ] [SMulZeroClass β γ] (f : α -> β)
  proof: Set.Finite.subset g.hasFiniteSupport (by simp; grind [smul_zero])

中文:
引理 pointwise_smul_support_finite
  结论: [Zero γ] [SMulZeroClass β γ] (f : α -> β)
  证明: Set.Finite.subset g.hasFiniteSupport (by simp; grind [smul_zero])

Depends on / 依赖: Finite, Set.Finite.subset, g.hasFiniteSupport, hasFiniteSupport, smul_zero, subset
-/
lemma pointwise_smul_support_finite [Zero γ] [SMulZeroClass β γ] (f : α -> β)
    (g : α ->₀ γ) : (fun x => f x • g x).support.Finite :=
  Set.Finite.subset g.hasFiniteSupport (by simp; grind [smul_zero])

-- TODO(Paul-Lez): add a `DFinsupp` version of this.
-- Note: this creates an instance diamond with `SMul (α → β) (α →₀ (α → β))`, so this is an
-- def rather than an instance.
-- see Note [reducible non-instances]
/--
Definition of `pointwiseScalar` / `pointwiseScalar` 的定义

English:
abbreviation pointwiseScalar
  signature: [Zero γ] [SMulZeroClass β γ]
  body: Finsupp.ofSupportFinite (fun a => f a • g a) (pointwise_smul_support_finite ..)

中文:
缩写 pointwiseScalar
  签名: [Zero γ] [SMulZeroClass β γ]
  定义体: Finsupp.ofSupportFinite (fun a => f a • g a) (pointwise_smul_support_finite ..)

Depends on / 依赖: Finsupp, Finsupp.ofSupportFinite, ofSupportFinite, pointwise_smul_support_finite
-/
abbrev pointwiseScalar [Zero γ] [SMulZeroClass β γ] : SMul (α -> β) (α ->₀ γ) where
  smul f g := Finsupp.ofSupportFinite (fun a => f a • g a) (pointwise_smul_support_finite ..)

/--
Instance `pointwiseScalarSemiring` / 实例 `pointwiseScalarSemiring`

English:
instance pointwiseScalarSemiring
  signature: [Semiring β]
  body: pointwiseScalar

@[simp]

中文:
实例 pointwiseScalarSemiring
  签名: [Semiring β]
  定义体: pointwiseScalar

@[simp]

Depends on / 依赖: pointwiseScalar
-/
instance pointwiseScalarSemiring [Semiring β] : SMul (α -> β) (α ->₀ β) := pointwiseScalar

@[simp]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: [Semiring β] (f : α -> β) (g : α ->₀ β)
  statement: ⇑(f • g) = f • ⇑g
  proof: rfl

中文:
定理 coe_pointwise_smul
  条件: [Semiring β] (f : α -> β) (g : α ->₀ β)
  结论: ⇑(f • g) = f • ⇑g
  证明: rfl
-/
theorem coe_pointwise_smul [Semiring β] (f : α -> β) (g : α ->₀ β) : ⇑(f • g) = f • ⇑g :=
  rfl

/--
Instance `pointwiseModule` / 实例 `pointwiseModule`

English:
instance pointwiseModule
  signature: [Semiring β]
  body: Function.Injective.module _ coeFnAddHom DFunLike.coe_injective coe_pointwise_smul

中文:
实例 pointwiseModule
  签名: [Semiring β]
  定义体: Function.Injective.module _ coeFnAddHom DFunLike.coe_injective coe_pointwise_smul

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.Injective.module, Injective, coeFnAddHom, coe_injective, coe_pointwise_smul, module
-/
instance pointwiseModule [Semiring β] : Module (α -> β) (α ->₀ β) :=
  Function.Injective.module _ coeFnAddHom DFunLike.coe_injective coe_pointwise_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: β] : IsScalarTower β (α -> β) (α ->₀ β) where
  body: by ext; simp [mul_assoc]

中文:
实例 [Semiring
  签名: β] : IsScalarTower β (α -> β) (α ->₀ β) where
  定义体: by ext; simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
instance [Semiring β] : IsScalarTower β (α -> β) (α ->₀ β) where
  smul_assoc r f m := by ext; simp [mul_assoc]

end Finsupp
