/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.GroupWithZero.Prod

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `MulAction M α` and its additive version `AddAction G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `SMul` and `VAdd` that are defined in `Algebra.Group.Defs`;
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `SMulCommClass M N α` and its additive version `VAddCommClass M N α`;
* `IsScalarTower M N α` and its additive version `VAddAssocClass M N α`;
* `IsCentralScalar M α` and its additive version `IsCentralVAdd M N α`.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

@[expose] public section

assert_not_exists Ring

open Function

variable {G G₀ A M M₀ N₀ R α : Type*}

section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ α] {a : G₀}

/--
lemma `MulAction.bijective₀` / 引理 `MulAction.bijective₀`

English:
lemma MulAction.bijective₀
  given: (ha : a != 0)
  statement: Bijective (a • · : α -> α)
  proof: MulAction.bijective Units.mk0 a ha

中文:
引理 MulAction.bijective₀
  条件: (ha : a != 0)
  结论: Bijective (a • · : α -> α)
  证明: MulAction.bijective Units.mk0 a ha
-/
protected lemma MulAction.bijective₀ (ha : a != 0) : Bijective (a • · : α -> α) :=
MulAction.bijective Units.mk0 a ha

/--
lemma `MulAction.injective₀` / 引理 `MulAction.injective₀`

English:
lemma MulAction.injective₀
  given: (ha : a != 0)
  statement: Injective (a • · : α -> α)
  proof: (MulAction.bijective₀ ha).injective

中文:
引理 MulAction.injective₀
  条件: (ha : a != 0)
  结论: Injective (a • · : α -> α)
  证明: (MulAction.bijective₀ ha).injective
-/
protected lemma MulAction.injective₀ (ha : a != 0) : Injective (a • · : α -> α) :=
  (MulAction.bijective₀ ha).injective

/--
lemma `MulAction.surjective₀` / 引理 `MulAction.surjective₀`

English:
lemma MulAction.surjective₀
  given: (ha : a != 0)
  statement: Surjective (a • · : α -> α)
  proof: (MulAction.bijective₀ ha).surjective

中文:
引理 MulAction.surjective₀
  条件: (ha : a != 0)
  结论: Surjective (a • · : α -> α)
  证明: (MulAction.bijective₀ ha).surjective
-/
protected lemma MulAction.surjective₀ (ha : a != 0) : Surjective (a • · : α -> α) :=
  (MulAction.bijective₀ ha).surjective

end GroupWithZero

section DistribMulAction
variable [Group G] [Monoid M] [AddMonoid A]
variable (A)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps +simpRhs]
/--
Definition of `DistribMulAction.toAddEquiv` / `DistribMulAction.toAddEquiv` 的定义

English:
definition DistribMulAction.toAddEquiv
  signature: [DistribMulAction G A] (x : G)
  body: DistribSMul.toAddMonoidHom A x
  __ := MulAction.toPermHom G A x

中文:
定义 DistribMulAction.toAddEquiv
  签名: [DistribMulAction G A] (x : G)
  定义体: DistribSMul.toAddMonoidHom A x
  __ := MulAction.toPermHom G A x

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, toAddMonoidHom
-/
def DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where
  __ := DistribSMul.toAddMonoidHom A x
  __ := MulAction.toPermHom G A x

variable (G)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
/--
Definition of `DistribMulAction.toAddAut` / `DistribMulAction.toAddAut` 的定义

English:
definition DistribMulAction.toAddAut
  signature: [DistribMulAction G A]
  body: toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

中文:
定义 DistribMulAction.toAddAut
  签名: [DistribMulAction G A]
  定义体: toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

Depends on / 依赖: toAddEquiv
-/
def DistribMulAction.toAddAut [DistribMulAction G A] : G ->* Multiplicative (AddAut A) where
  toFun := toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

end DistribMulAction

/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
/--
Definition of `smulMonoidWithZeroHom` / `smulMonoidWithZeroHom` 的定义

English:
definition smulMonoidWithZeroHom
  signature: [MonoidWithZero M₀] [MulZeroOneClass N₀] [MulActionWithZero M₀ N₀]
  body: { smulMonoidHom with map_zero' := smul_zero _ }

中文:
定义 smulMonoidWithZeroHom
  签名: [MonoidWithZero M₀] [MulZeroOneClass N₀] [MulActionWithZero M₀ N₀]
  定义体: { smulMonoidHom with map_zero' := smul_zero _ }

Depends on / 依赖: map_zero, smulMonoidHom, smul_zero
-/
def smulMonoidWithZeroHom [MonoidWithZero M₀] [MulZeroOneClass N₀] [MulActionWithZero M₀ N₀]
    [IsScalarTower M₀ N₀ N₀] [SMulCommClass M₀ N₀ N₀] : M₀ × N₀ ->*₀ N₀ :=
  { smulMonoidHom with map_zero' := smul_zero _ }

/--
lemma `IsUnit.smul_sub_iff_sub_inv_smul` / 引理 `IsUnit.smul_sub_iff_sub_inv_smul`

English:
lemma IsUnit.smul_sub_iff_sub_inv_smul
  statement: [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
  proof: by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a)]; rw [smul_sub]; rw [smul_inv_smul]

中文:
引理 IsUnit.smul_sub_iff_sub_inv_smul
  结论: [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
  证明: by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a)]; rw [smul_sub]; rw [smul_inv_smul]

Depends on / 依赖: isUnit_smul_iff, smul_inv_smul, smul_sub
-/
lemma IsUnit.smul_sub_iff_sub_inv_smul [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
    [IsScalarTower G R R] [SMulCommClass G R R] (r : G) (a : R) :
    IsUnit (r • (1 : R) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a)]; rw [smul_sub]; rw [smul_inv_smul]

/--
theorem `div_smul_div_comm` / 定理 `div_smul_div_comm`

English:
theorem div_smul_div_comm
  statement: [Group G] [GroupWithZero G₀] [MulAction G G₀]
  proof: by
  have (x : G) : x • (0 : G₀) = 0 := by simpa using (smul_assoc x (0 : G₀) (0 : G₀)).symm
  by_cases hb : b = 0
  · simp [hb, this]
  have : h • b != 0 := by
    refine (ne_of_apply_ne (h⁻¹ • ·) ?_)
    simpa [this]
  rw [eq_div_iff_mul_eq this]; rw [smul_mul_smul_comm]
  simp [hb]

中文:
定理 div_smul_div_comm
  结论: [Group G] [GroupWithZero G₀] [MulAction G G₀]
  证明: by
  have (x : G) : x • (0 : G₀) = 0 := by simpa using (smul_assoc x (0 : G₀) (0 : G₀)).symm
  by_cases hb : b = 0
  · simp [hb, this]
  have : h • b != 0 := by
    refine (ne_of_apply_ne (h⁻¹ • ·) ?_)
    simpa [this]
  rw [eq_div_iff_mul_eq this]; rw [smul_mul_smul_comm]
  simp [hb]

Depends on / 依赖: eq_div_iff_mul_eq, ne_of_apply_ne, smul_assoc, smul_mul_smul_comm
-/
theorem div_smul_div_comm [Group G] [GroupWithZero G₀] [MulAction G G₀]
    [IsScalarTower G G₀ G₀] [SMulCommClass G G₀ G₀] (g h : G) (a b : G₀) :
    (g / h) • (a / b) = (g • a) / (h • b) := by
  have (x : G) : x • (0 : G₀) = 0 := by simpa using (smul_assoc x (0 : G₀) (0 : G₀)).symm
  by_cases hb : b = 0
  · simp [hb, this]
  have : h • b != 0 := by
    refine (ne_of_apply_ne (h⁻¹ • ·) ?_)
    simpa [this]
  rw [eq_div_iff_mul_eq this]; rw [smul_mul_smul_comm]
  simp [hb]

/--
theorem `smul_zpow₀'` / 定理 `smul_zpow₀'`

English:
theorem smul_zpow₀'
  statement: [Group G] [GroupWithZero G₀] [MulDistribMulAction G G₀]
  proof: by
  cases n <;> simp

中文:
定理 smul_zpow₀'
  结论: [Group G] [GroupWithZero G₀] [MulDistribMulAction G G₀]
  证明: by
  cases n <;> simp
-/
@[simp] theorem smul_zpow₀' [Group G] [GroupWithZero G₀] [MulDistribMulAction G G₀]
    (g : G) (x : G₀) (n : Int) : g • (x ^ n) = (g • x) ^ n := by
  cases n <;> simp
