/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Tactic.Spread
public import Mathlib.Logic.Function.Iterate

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

Also provided are typeclasses regarding the interaction of different group actions,

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

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M N G H α β γ δ : Type*}

-- Note that https://github.com/leanprover/lean4/pull/13554
-- also makes the instance priority change, so if that is merged then `instance 1100` can
-- be removed here (we still want `to_additive` though).

-- see Note [higher instance priority]
/- See also `Monoid.toMulAction` and `MulZeroClass.toSMulWithZero`. -/
attribute [instance 1100, to_additive /-- See also `AddMonoid.toAddAction` -/] instSMulOfMul

/-- Like `Mul.toSMul`, but multiplies on the right.

See also `Monoid.toOppositeMulAction` and `MonoidWithZero.toOppositeMulActionWithZero`. -/
@[to_additive /-- Like `Add.toVAdd`, but adds on the right.

  See also `AddMonoid.toOppositeAddAction`. -/]
instance (priority := 910) Mul.toSMulMulOpposite (α : Type*) [Mul α] : SMul αᵐᵒᵖ α where
  smul a b := b * a.unop

@[to_additive (attr := simp)]
/--
lemma `smul_eq_mul` / 引理 `smul_eq_mul`

English:
lemma smul_eq_mul
  given: {α : Type*} [Mul α] (a b : α)
  statement: a • b = a * b
  proof: rfl

@[to_additive]

中文:
引理 smul_eq_mul
  条件: {α : 类型} [Mul α] (a b : α)
  结论: a • b = a * b
  证明: rfl

@[to_additive]
-/
lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl

@[to_additive]
/--
lemma `op_smul_eq_mul` / 引理 `op_smul_eq_mul`

English:
lemma op_smul_eq_mul
  given: {α : Type*} [Mul α] (a b : α)
  statement: MulOpposite.op a • b = b * a
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 op_smul_eq_mul
  条件: {α : 类型} [Mul α] (a b : α)
  结论: MulOpposite.op a • b = b * a
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma op_smul_eq_mul {α : Type*} [Mul α] (a b : α) : MulOpposite.op a • b = b * a := rfl

@[to_additive (attr := simp)]
/--
lemma `MulOpposite.smul_eq_mul_unop` / 引理 `MulOpposite.smul_eq_mul_unop`

English:
lemma MulOpposite.smul_eq_mul_unop
  given: [Mul α] (a : αᵐᵒᵖ) (b : α)
  statement: a • b = b * a.unop
  proof: rfl

中文:
引理 MulOpposite.smul_eq_mul_unop
  条件: [Mul α] (a : αᵐᵒᵖ) (b : α)
  结论: a • b = b * a.unop
  证明: rfl
-/
lemma MulOpposite.smul_eq_mul_unop [Mul α] (a : αᵐᵒᵖ) (b : α) : a • b = b * a.unop := rfl

/--
Definition of `AddSemigroupAction` / `AddSemigroupAction` 的定义

English:
class AddSemigroupAction
  parameters: (G P : Type*) [AddSemigroup G]
  extends: VAdd G P
  axioms and operations (1):
    - add_vadd : forall (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p

中文:
类 AddSemigroupAction
  参数: (G P : 类型) [AddSemigroup G]
  继承: VAdd G P
  公理与运算 (1 个):
    - add_vadd : 对任意 (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p
-/
class AddSemigroupAction (G P : Type*) [AddSemigroup G] extends VAdd G P where
  /-- Associativity of `+ᵥ` and `+` -/
  add_vadd : forall (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p

/-- Type class for actions by semigroups, with notation `g • p`.

The `SemigroupAction G P` typeclass says that the semigroup `G` acts multiplicatively on a type `P`.
More precisely this means that the action satisfies the axiom `(g₁ * g₂) • p = g₁ • (g₂ • p)`.
A mathematician might simply say that the semigroup `G` acts on `P`.

For example, if `G` is a semigroup and `X` is a type, if a mathematician says
say "let `G` act on the set `X`" they will probably mean `[SemigroupAction G X]`. -/
@[to_additive (attr := ext)]
/--
Definition of `SemigroupAction` / `SemigroupAction` 的定义

English:
class SemigroupAction
  parameters: (α β : Type*) [Semigroup α]
  extends: SMul α β
  axioms and operations (1):
    - mul_smul((x y : α) (b : β)) : (x * y) • b = x • y • b

中文:
类 SemigroupAction
  参数: (α β : 类型) [Semigroup α]
  继承: SMul α β
  公理与运算 (1 个):
    - mul_smul((x y : α) (b : β)) : (x * y) • b = x • y • b
-/
class SemigroupAction (α β : Type*) [Semigroup α] extends SMul α β where
  /-- Associativity of `•` and `*` -/
  mul_smul (x y : α) (b : β) : (x * y) • b = x • y • b

/--
Definition of `AddAction` / `AddAction` 的定义

English:
class AddAction
  parameters: (G : Type*) (P : Type*) [AddMonoid G]
  extends: AddSemigroupAction G P
  axioms and operations (1):
    - zero_vadd : forall p : P, (0 : G) +ᵥ p = p

中文:
类 AddAction
  参数: (G : 类型) (P : 类型) [AddMonoid G]
  继承: AddSemigroupAction G P
  公理与运算 (1 个):
    - zero_vadd : 对任意 p : P, (0 : G) +ᵥ p = p
-/
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends AddSemigroupAction G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : forall p : P, (0 : G) +ᵥ p = p

/--
Type class for monoid actions on types, with notation `g • p`.

The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`.
More precisely this means that the action satisfies the two axioms `1 • p = p` and
`(g₁ * g₂) • p = g₁ • (g₂ • p)`. A mathematician might simply say that the monoid `G`
acts on `P`.

For example, if `G` is a group and `X` is a type, if a mathematician says
say "let `G` act on the set `X`" they will probably mean `[MulAction G X]`.
-/
@[to_additive (attr := ext, wikidata Q288465)]
/--
Definition of `MulAction` / `MulAction` 的定义

English:
class MulAction
  parameters: (α : Type*) (β : Type*) [Monoid α]
  extends: SemigroupAction α β
  axioms and operations (1):
    - one_smul : forall b : β, (1 : α) • b = b

中文:
类 MulAction
  参数: (α : 类型) (β : 类型) [Monoid α]
  继承: SemigroupAction α β
  公理与运算 (1 个):
    - one_smul : 对任意 b : β, (1 : α) • b = b
-/
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SemigroupAction α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : forall b : β, (1 : α) • b = b

/-! ### Scalar tower and commuting actions -/

/--
Definition of `VAddCommClass` / `VAddCommClass` 的定义

English:
class VAddCommClass
  parameters: (M N α : Type*) [VAdd M α] [VAdd N α]
  axioms and operations (1):
    - vadd_comm : forall (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)

中文:
类 VAddCommClass
  参数: (M N α : 类型) [VAdd M α] [VAdd N α]
  公理与运算 (1 个):
    - vadd_comm : 对任意 (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)
-/
class VAddCommClass (M N α : Type*) [VAdd M α] [VAdd N α] : Prop where
  /-- `+ᵥ` is left commutative -/
  vadd_comm : forall (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive]
/--
Definition of `SMulCommClass` / `SMulCommClass` 的定义

English:
class SMulCommClass
  parameters: (M N α : Type*) [SMul M α] [SMul N α]
  axioms and operations (1):
    - smul_comm : forall (m : M) (n : N) (a : α), m • n • a = n • m • a

中文:
类 SMulCommClass
  参数: (M N α : 类型) [SMul M α] [SMul N α]
  公理与运算 (1 个):
    - smul_comm : 对任意 (m : M) (n : N) (a : α), m • n • a = n • m • a
-/
class SMulCommClass (M N α : Type*) [SMul M α] [SMul N α] : Prop where
  /-- `•` is left commutative -/
  smul_comm : forall (m : M) (n : N) (a : α), m • n • a = n • m • a

export SemigroupAction (mul_smul)
export AddSemigroupAction (add_vadd)
export SMulCommClass (smul_comm)
export VAddCommClass (vadd_comm)

library_note «bundled maps over different rings» /--
Frequently, we find ourselves wanting to express a bilinear map `M →ₗ[R] N →ₗ[R] P` or an
equivalence between maps `(M →ₗ[R] N) ≃ₗ[R] (M' →ₗ[R] N')` where the maps have an associated ring
`R`. Unfortunately, using definitions like these requires that `R` satisfy `CommSemiring R`, and
not just `Semiring R`. Using `M →ₗ[R] N →+ P` and `(M →ₗ[R] N) ≃+ (M' →ₗ[R] N')` avoids this
problem, but throws away structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `SMulCommClass S R` on the appropriate modules. When
the caller has `CommSemiring R`, they can set `S = R` and `smulCommClass_self` will populate the
instance. If the caller only has `Semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`AddCommMonoid.nat_smulCommClass` or `AddCommMonoid.nat_smulCommClass'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `LinearMap.prod_equiv`.
-/

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive]
/--
lemma `SMulCommClass.symm` / 引理 `SMulCommClass.symm`

English:
lemma SMulCommClass.symm
  given: (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α]
  proof: (smul_comm a a' b).symm

中文:
引理 SMulCommClass.symm
  条件: (M N α : 类型) [SMul M α] [SMul N α] [SMulCommClass M N α]
  证明: (smul_comm a a' b).symm

Depends on / 依赖: smul_comm
-/
lemma SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass N M α where smul_comm a' a b := (smul_comm a a' b).symm

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc VAddCommClass.symm

@[to_additive]
/--
lemma `Function.Injective.smulCommClass` / 引理 `Function.Injective.smulCommClass`

English:
lemma Function.Injective.smulCommClass
  statement: [SMul M α] [SMul N α] [SMul M β] [SMul N β]
  proof: hf by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

@[to_additive]

中文:
引理 Function.Injective.smulCommClass
  结论: [SMul M α] [SMul N α] [SMul M β] [SMul N β]
  证明: hf by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

@[to_additive]

Depends on / 依赖: smul_comm
-/
lemma Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α -> β} (hf : Injective f) (h₁ : forall (c : M) x, f (c • x) = c • f x)
    (h₂ : forall (c : N) x, f (c • x) = c • f x) : SMulCommClass M N α where
smul_comm c₁ c₂ x := hf by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

@[to_additive]
/--
lemma `Function.Surjective.smulCommClass` / 引理 `Function.Surjective.smulCommClass`

English:
lemma Function.Surjective.smulCommClass
  statement: [SMul M α] [SMul N α] [SMul M β] [SMul N β]
  proof: hf.forall.2 fun x => by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

@[to_additive]

中文:
引理 Function.Surjective.smulCommClass
  结论: [SMul M α] [SMul N α] [SMul M β] [SMul N β]
  证明: hf.forall.2 fun x => by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

@[to_additive]

Depends on / 依赖: hf.forall, smul_comm
-/
lemma Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α -> β} (hf : Surjective f) (h₁ : forall (c : M) x, f (c • x) = c • f x)
    (h₂ : forall (c : N) x, f (c • x) = c • f x) : SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x => by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

@[to_additive]
/--
Instance `smulCommClass_self` / 实例 `smulCommClass_self`

English:
instance smulCommClass_self
  signature: (M α : Type*) [CommMonoid M] [MulAction M α]
  body: by rw [← mul_smul, mul_comm, mul_smul]

中文:
实例 smulCommClass_self
  签名: (M α : 类型) [CommMonoid M] [MulAction M α]
  定义体: by rw [← mul_smul, mul_comm, mul_smul]

Depends on / 依赖: mul_comm, mul_smul
-/
instance smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulCommClass M M α where
  smul_comm a a' b := by rw [← mul_smul, mul_comm, mul_smul]

/--
Definition of `VAddAssocClass` / `VAddAssocClass` 的定义

English:
class VAddAssocClass
  parameters: (M N α : Type*) [VAdd M N] [VAdd N α] [VAdd M α]
  axioms and operations (1):
    - vadd_assoc : forall (x : M) (y : N) (z : α), (x +ᵥ y) +ᵥ z = x +ᵥ y +ᵥ z

中文:
类 VAddAssocClass
  参数: (M N α : 类型) [VAdd M N] [VAdd N α] [VAdd M α]
  公理与运算 (1 个):
    - vadd_assoc : 对任意 (x : M) (y : N) (z : α), (x +ᵥ y) +ᵥ z = x +ᵥ y +ᵥ z
-/
class VAddAssocClass (M N α : Type*) [VAdd M N] [VAdd N α] [VAdd M α] : Prop where
  /-- Associativity of `+ᵥ` -/
  vadd_assoc : forall (x : M) (y : N) (z : α), (x +ᵥ y) +ᵥ z = x +ᵥ y +ᵥ z

/-- An instance of `IsScalarTower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
@[to_additive]
/--
Definition of `IsScalarTower` / `IsScalarTower` 的定义

English:
class IsScalarTower
  parameters: (M N α : Type*) [SMul M N] [SMul N α] [SMul M α]
  axioms and operations (1):
    - smul_assoc : forall (x : M) (y : N) (z : α), (x • y) • z = x • y • z

中文:
类 IsScalarTower
  参数: (M N α : 类型) [SMul M N] [SMul N α] [SMul M α]
  公理与运算 (1 个):
    - smul_assoc : 对任意 (x : M) (y : N) (z : α), (x • y) • z = x • y • z
-/
class IsScalarTower (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] : Prop where
  /-- Associativity of `•` -/
  smul_assoc : forall (x : M) (y : N) (z : α), (x • y) • z = x • y • z

@[to_additive (attr := simp)]
/--
lemma `smul_assoc` / 引理 `smul_assoc`

English:
lemma smul_assoc
  statement: {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
  proof: IsScalarTower.smul_assoc x y z

@[to_additive]

中文:
引理 smul_assoc
  结论: {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
  证明: IsScalarTower.smul_assoc x y z

@[to_additive]

Depends on / 依赖: IsScalarTower, IsScalarTower.smul_assoc, smul_assoc
-/
lemma smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
    (z : α) : (x • y) • z = x • y • z := IsScalarTower.smul_assoc x y z

@[to_additive]
/--
Instance `Semigroup.isScalarTower` / 实例 `Semigroup.isScalarTower`

English:
instance Semigroup.isScalarTower
  signature: [Semigroup α]
  body: ⟨mul_assoc⟩

中文:
实例 Semigroup.isScalarTower
  签名: [Semigroup α]
  定义体: ⟨mul_assoc⟩

Depends on / 依赖: mul_assoc
-/
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α := ⟨mul_assoc⟩

/--
Definition of `SMulDistribClass` / `SMulDistribClass` 的定义

English:
class SMulDistribClass
  parameters: (G R S : Type*) [SMul G R] [SMul G S] [SMul R S]
  axioms and operations (1):
    - smul_distrib_smul((g : G) (r : R) (s : S)) : g • r • s = (g • r) • (g • s)

中文:
类 SMulDistribClass
  参数: (G R S : 类型) [SMul G R] [SMul G S] [SMul R S]
  公理与运算 (1 个):
    - smul_distrib_smul((g : G) (r : R) (s : S)) : g • r • s = (g • r) • (g • s)
-/
class SMulDistribClass (G R S : Type*) [SMul G R] [SMul G S] [SMul R S] : Prop where
  smul_distrib_smul (g : G) (r : R) (s : S) : g • r • s = (g • r) • (g • s)

export SMulDistribClass (smul_distrib_smul)

/--
Definition of `IsCentralVAdd` / `IsCentralVAdd` 的定义

English:
class IsCentralVAdd
  parameters: (M α : Type*) [VAdd M α] [VAdd Mᵃᵒᵖ α]
  axioms and operations (1):
    - op_vadd_eq_vadd : forall (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a

中文:
类 IsCentralVAdd
  参数: (M α : 类型) [VAdd M α] [VAdd Mᵃᵒᵖ α]
  公理与运算 (1 个):
    - op_vadd_eq_vadd : 对任意 (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a
-/
class IsCentralVAdd (M α : Type*) [VAdd M α] [VAdd Mᵃᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_vadd_eq_vadd : forall (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a

/-- A typeclass indicating that the right (aka `MulOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
@[to_additive]
/--
Definition of `IsCentralScalar` / `IsCentralScalar` 的定义

English:
class IsCentralScalar
  parameters: (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α]
  axioms and operations (1):
    - op_smul_eq_smul : forall (m : M) (a : α), MulOpposite.op m • a = m • a

中文:
类 IsCentralScalar
  参数: (M α : 类型) [SMul M α] [SMul Mᵐᵒᵖ α]
  公理与运算 (1 个):
    - op_smul_eq_smul : 对任意 (m : M) (a : α), MulOpposite.op m • a = m • a
-/
class IsCentralScalar (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_smul_eq_smul : forall (m : M) (a : α), MulOpposite.op m • a = m • a

@[to_additive]
/--
lemma `IsCentralScalar.unop_smul_eq_smul` / 引理 `IsCentralScalar.unop_smul_eq_smul`

English:
lemma IsCentralScalar.unop_smul_eq_smul
  statement: {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
  proof: by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm

中文:
引理 IsCentralScalar.unop_smul_eq_smul
  结论: {M α : 类型} [SMul M α] [SMul Mᵐᵒᵖ α]
  证明: by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm

Depends on / 依赖: IsCentralScalar, IsCentralScalar.op_smul_eq_smul, op_smul_eq_smul
-/
lemma IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)
export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

attribute [simp] IsCentralScalar.op_smul_eq_smul

-- these instances are very low priority, as there is usually a faster way to find these instances
@[to_additive]
instance (priority := 50) SMulCommClass.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩

@[to_additive]
instance (priority := 50) SMulCommClass.op_right [SMul M α] [SMul N α] [SMul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a => by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩

@[to_additive]
instance (priority := 50) IsScalarTower.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul M N] [SMul Mᵐᵒᵖ N] [IsCentralScalar M N] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α where
  smul_assoc m n a := by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]

@[to_additive]
instance (priority := 50) IsScalarTower.op_right [SMul M α] [SMul M N] [SMul N α]
    [SMul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α where
  smul_assoc m n a := by
    rw [← unop_smul_eq_smul n a]; rw [← unop_smul_eq_smul (m • n) a]; rw [MulOpposite.unop_smul]; rw [smul_assoc]

namespace SMul
variable [SMul M α]

/-- Auxiliary definition for `SMul.comp`, `MulAction.compHom`,
`DistribMulAction.compHom`, `Module.compHom`, etc. -/
@[to_additive (attr := simp, implicit_reducible)
/-- Auxiliary definition for `VAdd.comp`, `AddAction.compHom`, etc. -/]
/--
Definition of `comp.smul` / `comp.smul` 的定义

English:
definition comp.smul
  signature: (g : N -> M) (n : N) (a : α)
  body: g n • a

中文:
定义 comp.smul
  签名: (g : N -> M) (n : N) (a : α)
  定义体: g n • a
-/
def comp.smul (g : N -> M) (n : N) (a : α) : α := g n • a

variable (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`. -/
-- See note [reducible non-instances]
-- Since this is reducible, we make sure to go via
-- `SMul.comp.smul` to prevent typeclass inference unfolding too far
@[to_additive /-- An additive action of `M` on `α` and a function `N → M` induces an additive
action of `N` on `α`. -/]
/--
Definition of `comp` / `comp` 的定义

English:
abbreviation comp
  signature: (g : N -> M)
  body: SMul.comp.smul g

中文:
缩写 comp
  签名: (g : N -> M)
  定义体: SMul.comp.smul g

Depends on / 依赖: SMul.comp.smul
-/
abbrev comp (g : N -> M) : SMul N α where smul := SMul.comp.smul g

variable {α}

/-- Given a tower of scalar actions `M → α → β`, if we use `SMul.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- Given a tower of additive actions `M → α → β`, if we use `SMul.comp` to pull back both of
`M`'s actions by a map `g : N → M`, then we obtain a new tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/]
/--
lemma `comp.isScalarTower` / 引理 `comp.isScalarTower`

English:
lemma comp.isScalarTower
  given: [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N -> M)
  statement: by
  proof: comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

中文:
引理 comp.isScalarTower
  条件: [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N -> M)
  结论: by
  证明: comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

Depends on / 依赖: IsScalarTower
-/
lemma comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N -> M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables. -/]
/--
lemma `comp.smulCommClass` / 引理 `comp.smulCommClass`

English:
lemma comp.smulCommClass
  given: [SMul β α] [SMulCommClass M β α] (g : N -> M)
  proof: comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)

中文:
引理 comp.smulCommClass
  条件: [SMul β α] [SMulCommClass M β α] (g : N -> M)
  证明: comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)
-/
lemma comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N -> M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables. -/]
/--
lemma `comp.smulCommClass'` / 引理 `comp.smulCommClass'`

English:
lemma comp.smulCommClass'
  given: [SMul β α] [SMulCommClass β M α] (g : N -> M)
  proof: comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)

中文:
引理 comp.smulCommClass'
  条件: [SMul β α] [SMulCommClass β M α] (g : N -> M)
  证明: comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)
-/
lemma comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N -> M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)

end SMul

section

/-- Note that the `SMulCommClass α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
/--
lemma `mul_smul_comm` / 引理 `mul_smul_comm`

English:
lemma mul_smul_comm
  given: [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β)
  proof: (smul_comm s x y).symm

中文:
引理 mul_smul_comm
  条件: [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β)
  证明: (smul_comm s x y).symm

Depends on / 依赖: smul_comm
-/
lemma mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) := (smul_comm s x y).symm

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
/--
lemma `smul_mul_assoc` / 引理 `smul_mul_assoc`

English:
lemma smul_mul_assoc
  given: [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β)
  proof: smul_assoc r x y

中文:
引理 smul_mul_assoc
  条件: [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β)
  证明: smul_assoc r x y

Depends on / 依赖: smul_assoc
-/
lemma smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) := smul_assoc r x y

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
/--
lemma `smul_div_assoc` / 引理 `smul_div_assoc`

English:
lemma smul_div_assoc
  given: [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β)
  proof: by simp [div_eq_mul_inv, smul_mul_assoc]

@[to_additive]

中文:
引理 smul_div_assoc
  条件: [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β)
  证明: by simp [div_eq_mul_inv, smul_mul_assoc]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, smul_mul_assoc
-/
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

@[to_additive]
/--
lemma `smul_smul_smul_comm` / 引理 `smul_smul_smul_comm`

English:
lemma smul_smul_smul_comm
  statement: [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
  proof: by rw [smul_assoc, smul_assoc, smul_comm b]

中文:
引理 smul_smul_smul_comm
  结论: [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
  证明: by rw [smul_assoc, smul_assoc, smul_comm b]

Depends on / 依赖: smul_assoc, smul_comm
-/
lemma smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by rw [smul_assoc, smul_assoc, smul_comm b]

/-- Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass arguments are usually
satisfied by `Algebra α β`. -/
@[to_additive]
/--
lemma `smul_mul_smul_comm` / 引理 `smul_mul_smul_comm`

English:
lemma smul_mul_smul_comm
  statement: [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
  proof: by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d

@[to_additive]
alias smul_mul_smul := smul_mul_smul_comm

中文:
引理 smul_mul_smul_comm
  结论: [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
  证明: by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d

@[to_additive]
alias smul_mul_smul := smul_mul_smul_comm

Depends on / 依赖: SMulCommClass, smul_smul_smul_comm
-/
lemma smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β) :
    (a • b) * (c • d) = (a * c) • (b * d) := by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d

@[to_additive]
alias smul_mul_smul := smul_mul_smul_comm

/-- Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass arguments are usually
satisfied by `Algebra α β`. -/
@[to_additive]
/--
lemma `mul_smul_mul_comm` / 引理 `mul_smul_mul_comm`

English:
lemma mul_smul_mul_comm
  statement: [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
  proof: smul_smul_smul_comm a b c d

中文:
引理 mul_smul_mul_comm
  结论: [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
  证明: smul_smul_smul_comm a b c d

Depends on / 依赖: smul_smul_smul_comm
-/
lemma mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) :
    (a * b) • (c * d) = (a • c) * (b • d) := smul_smul_smul_comm a b c d

variable [SMul M α]

@[to_additive]
/--
lemma `SemiconjBy.smul_right` / 引理 `SemiconjBy.smul_right`

English:
lemma SemiconjBy.smul_right
  statement: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
  proof: by
  rw [SemiconjBy]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h.eq]

@[to_additive]

中文:
引理 SemiconjBy.smul_right
  结论: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
  证明: by
  rw [SemiconjBy]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h.eq]

@[to_additive]

Depends on / 依赖: SemiconjBy, h.eq, mul_smul_comm, smul_mul_assoc
-/
lemma SemiconjBy.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
    (h : SemiconjBy x a b) (r : M) : SemiconjBy x (r • a) (r • b) := by
  rw [SemiconjBy]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h.eq]

@[to_additive]
/--
lemma `SemiconjBy.smul_left` / 引理 `SemiconjBy.smul_left`

English:
lemma SemiconjBy.smul_left
  statement: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
  proof: by
  rw [SemiconjBy]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h.eq]

@[to_additive]

中文:
引理 SemiconjBy.smul_left
  结论: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
  证明: by
  rw [SemiconjBy]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h.eq]

@[to_additive]

Depends on / 依赖: SemiconjBy, h.eq, mul_smul_comm, smul_mul_assoc
-/
lemma SemiconjBy.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
    (h : SemiconjBy x a b) (r : M) : SemiconjBy (r • x) a b := by
  rw [SemiconjBy]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h.eq]

@[to_additive]
/--
lemma `Commute.smul_right` / 引理 `Commute.smul_right`

English:
lemma Commute.smul_right
  statement: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
  proof: SemiconjBy.smul_right h r

@[to_additive]

中文:
引理 Commute.smul_right
  结论: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
  证明: SemiconjBy.smul_right h r

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.smul_right, smul_right
-/
lemma Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  SemiconjBy.smul_right h r

@[to_additive]
/--
lemma `Commute.smul_left` / 引理 `Commute.smul_left`

English:
lemma Commute.smul_left
  statement: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
  proof: SemiconjBy.smul_left h r

中文:
引理 Commute.smul_left
  结论: [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
  证明: SemiconjBy.smul_left h r

Depends on / 依赖: SemiconjBy, SemiconjBy.smul_left, smul_left
-/
lemma Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b :=
  SemiconjBy.smul_left h r

end

section
variable [Monoid M] [MulAction M α] {a : M}

@[to_additive]
/--
lemma `smul_smul` / 引理 `smul_smul`

English:
lemma smul_smul
  given: (a₁ a₂ : M) (b : α)
  statement: a₁ • a₂ • b = (a₁ * a₂) • b
  proof: (mul_smul _ _ _).symm

中文:
引理 smul_smul
  条件: (a₁ a₂ : M) (b : α)
  结论: a₁ • a₂ • b = (a₁ * a₂) • b
  证明: (mul_smul _ _ _).symm

Depends on / 依赖: mul_smul
-/
lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

variable (M)

@[to_additive (attr := simp)]
/--
lemma `one_smul` / 引理 `one_smul`

English:
lemma one_smul
  given: (b : α)
  statement: (1 : M) • b = b
  proof: MulAction.one_smul _

中文:
引理 one_smul
  条件: (b : α)
  结论: (1 : M) • b = b
  证明: MulAction.one_smul _

Depends on / 依赖: MulAction, MulAction.one_smul, one_smul
-/
lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _

/-- `SMul` version of `one_mul_eq_id` -/
@[to_additive /-- `VAdd` version of `zero_add_eq_id` -/]
/--
lemma `one_smul_eq_id` / 引理 `one_smul_eq_id`

English:
lemma one_smul_eq_id
  statement: (((1 : M) • ·) : α -> α) = id
  proof: funext one_smul _

中文:
引理 one_smul_eq_id
  结论: (((1 : M) • ·) : α -> α) = id
  证明: funext one_smul _

Depends on / 依赖: one_smul
-/
lemma one_smul_eq_id : (((1 : M) • ·) : α -> α) = id := funext one_smul _

/-- `SMul` version of `comp_mul_left` -/
@[to_additive /-- `VAdd` version of `comp_add_left` -/]
/--
lemma `comp_smul_left` / 引理 `comp_smul_left`

English:
lemma comp_smul_left
  given: (a₁ a₂ : M)
  statement: (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α -> α)
  proof: funext fun _ => (mul_smul _ _ _).symm

中文:
引理 comp_smul_left
  条件: (a₁ a₂ : M)
  结论: (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α -> α)
  证明: funext fun _ => (mul_smul _ _ _).symm

Depends on / 依赖: mul_smul
-/
lemma comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α -> α) :=
  funext fun _ => (mul_smul _ _ _).symm

variable {M}

@[to_additive (attr := simp)]
/--
theorem `smul_iterate` / 定理 `smul_iterate`

English:
theorem smul_iterate
  given: (a : M)
  statement: forall n : Nat, (a • · : α -> α)^[n] = (a ^ n • ·)

中文:
定理 smul_iterate
  条件: (a : M)
  结论: 对任意 n : 自然数, (a • · : α -> α)^[n] = (a ^ n • ·)
-/
theorem smul_iterate (a : M) : forall n : Nat, (a • · : α -> α)^[n] = (a ^ n • ·)
  | 0 => by simp [funext_iff]
  | n + 1 => by ext; simp [smul_iterate, pow_succ, smul_smul]

@[to_additive]
/--
lemma `smul_iterate_apply` / 引理 `smul_iterate_apply`

English:
lemma smul_iterate_apply
  given: (a : M) (n : Nat) (x : α)
  statement: (a • ·)^[n] x = a ^ n • x
  proof: by
  rw [smul_iterate]

中文:
引理 smul_iterate_apply
  条件: (a : M) (n : 自然数) (x : α)
  结论: (a • ·)^[n] x = a ^ n • x
  证明: by
  rw [smul_iterate]

Depends on / 依赖: smul_iterate
-/
lemma smul_iterate_apply (a : M) (n : Nat) (x : α) : (a • ·)^[n] x = a ^ n • x := by
  rw [smul_iterate]

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive
    /-- Pullback an additive action along an injective map respecting `+ᵥ`. -/]
/--
Definition of `Function.Injective.mulAction` / `Function.Injective.mulAction` 的定义

English:
abbreviation Function.Injective.mulAction
  signature: [SMul M β] (f : β -> α) (hf : Injective f)
  body: hf (smul _ _).trans one_smul _ (f x)
mul_smul c₁ c₂ x := hf by simp only [smul, mul_smul]

中文:
缩写 Function.Injective.mulAction
  签名: [SMul M β] (f : β -> α) (hf : Injective f)
  定义体: hf (smul _ _).trans one_smul _ (f x)
mul_smul c₁ c₂ x := hf by simp only [smul, mul_smul]
-/
protected abbrev Function.Injective.mulAction [SMul M β] (f : β -> α) (hf : Injective f)
    (smul : forall (c : M) (x), f (c • x) = c • f x) : MulAction M β where
one_smul x := hf (smul _ _).trans one_smul _ (f x)
mul_smul c₁ c₂ x := hf by simp only [smul, mul_smul]

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive
    /-- Pushforward an additive action along a surjective map respecting `+ᵥ`. -/]
/--
Definition of `Function.Surjective.mulAction` / `Function.Surjective.mulAction` 的定义

English:
abbreviation Function.Surjective.mulAction
  signature: [SMul M β] (f : α -> β) (hf : Surjective f)
  body: by simp [hf.forall, ← smul]
  mul_smul := by simp [hf.forall, ← smul, mul_smul]

中文:
缩写 Function.Surjective.mulAction
  签名: [SMul M β] (f : α -> β) (hf : Surjective f)
  定义体: by simp [hf.forall, ← smul]
  mul_smul := by simp [hf.forall, ← smul, mul_smul]
-/
protected abbrev Function.Surjective.mulAction [SMul M β] (f : α -> β) (hf : Surjective f)
    (smul : forall (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  one_smul := by simp [hf.forall, ← smul]
  mul_smul := by simp [hf.forall, ← smul, mul_smul]

section
variable (M)

-- see Note [higher instance priority]
/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `Semiring.toModule`. -/
@[to_additive
/-- The regular action of a monoid on itself by left addition.

This is promoted to an `AddTorsor` by `addGroup_is_addTorsor`. -/]
instance (priority := 1100) Monoid.toMulAction : MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc

@[to_additive]
/--
Instance `IsScalarTower.left` / 实例 `IsScalarTower.left`

English:
instance IsScalarTower.left
  signature: : IsScalarTower M M α where
  body: mul_smul x y z

@[to_additive]

中文:
实例 IsScalarTower.left
  签名: : IsScalarTower M M α where
  定义体: mul_smul x y z

@[to_additive]

Depends on / 依赖: mul_smul
-/
instance IsScalarTower.left : IsScalarTower M M α where
  smul_assoc x y z := mul_smul x y z

@[to_additive]
instance {R M : Type*} [CommMonoid M] [SMul R M] [IsScalarTower R M M] : SMulCommClass R M M where
  smul_comm r s x := by
    rw [← one_smul M (s • x)]; rw [← smul_assoc]; rw [smul_comm]; rw [smul_assoc]; rw [one_smul]

variable {M}

section Monoid
variable [Monoid N] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]

/--
lemma `smul_pow` / 引理 `smul_pow`

English:
lemma smul_pow
  given: (r : M) (x : N)
  statement: forall n, (r • x) ^ n = r ^ n • x ^ n

中文:
引理 smul_pow
  条件: (r : M) (x : N)
  结论: 对任意 n, (r • x) ^ n = r ^ n • x ^ n
-/
lemma smul_pow (r : M) (x : N) : forall n, (r • x) ^ n = r ^ n • x ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ', smul_pow _ _ n, smul_mul_smul_comm, ← pow_succ', ← pow_succ']

end Monoid

section Group
variable [Group G] [MulAction G α] {g : G} {a b : α}

@[to_additive (attr := simp)]
/--
lemma `inv_smul_smul` / 引理 `inv_smul_smul`

English:
lemma inv_smul_smul
  given: (g : G) (a : α)
  statement: g⁻¹ • g • a = a
  proof: by rw [smul_smul, inv_mul_cancel, one_smul]

@[to_additive (attr := simp)]

中文:
引理 inv_smul_smul
  条件: (g : G) (a : α)
  结论: g⁻¹ • g • a = a
  证明: by rw [smul_smul, inv_mul_cancel, one_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, one_smul, smul_smul
-/
lemma inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a := by rw [smul_smul, inv_mul_cancel, one_smul]

@[to_additive (attr := simp)]
/--
lemma `smul_inv_smul` / 引理 `smul_inv_smul`

English:
lemma smul_inv_smul
  given: (g : G) (a : α)
  statement: g • g⁻¹ • a = a
  proof: by rw [smul_smul, mul_inv_cancel, one_smul]

中文:
引理 smul_inv_smul
  条件: (g : G) (a : α)
  结论: g • g⁻¹ • a = a
  证明: by rw [smul_smul, mul_inv_cancel, one_smul]

Depends on / 依赖: mul_inv_cancel, one_smul, smul_smul
-/
lemma smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel, one_smul]

/--
lemma `inv_smul_eq_iff` / 引理 `inv_smul_eq_iff`

English:
lemma inv_smul_eq_iff
  statement: g⁻¹ • a = b ↔ a = g • b
  proof: ⟨fun h => by rw [← h, smul_inv_smul], fun h => by rw [h, inv_smul_smul]⟩

中文:
引理 inv_smul_eq_iff
  结论: g⁻¹ • a = b ↔ a = g • b
  证明: ⟨fun h => by rw [← h, smul_inv_smul], fun h => by rw [h, inv_smul_smul]⟩
-/
@[to_additive] lemma inv_smul_eq_iff : g⁻¹ • a = b ↔ a = g • b :=
  ⟨fun h => by rw [← h, smul_inv_smul], fun h => by rw [h, inv_smul_smul]⟩

/--
lemma `eq_inv_smul_iff` / 引理 `eq_inv_smul_iff`

English:
lemma eq_inv_smul_iff
  statement: a = g⁻¹ • b ↔ g • a = b
  proof: ⟨fun h => by rw [h, smul_inv_smul], fun h => by rw [← h, inv_smul_smul]⟩

中文:
引理 eq_inv_smul_iff
  结论: a = g⁻¹ • b ↔ g • a = b
  证明: ⟨fun h => by rw [h, smul_inv_smul], fun h => by rw [← h, inv_smul_smul]⟩
-/
@[to_additive] lemma eq_inv_smul_iff : a = g⁻¹ • b ↔ g • a = b :=
  ⟨fun h => by rw [h, smul_inv_smul], fun h => by rw [← h, inv_smul_smul]⟩

section Mul
variable [Mul H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H] {a b : H}

@[to_additive (attr := simp)]
/--
lemma `SemiconjBy.smul_right_iff` / 引理 `SemiconjBy.smul_right_iff`

English:
lemma SemiconjBy.smul_right_iff
  given: {a b x : H} {r : G}
  proof: ⟨fun h => by simpa using h.smul_right r⁻¹, (smul_right · r)⟩

@[to_additive (attr := simp)]

中文:
引理 SemiconjBy.smul_right_iff
  条件: {a b x : H} {r : G}
  证明: ⟨fun h => by simpa using h.smul_right r⁻¹, (smul_right · r)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: h.smul_right, smul_right
-/
lemma SemiconjBy.smul_right_iff {a b x : H} {r : G} :
    SemiconjBy x (r • a) (r • b) ↔ SemiconjBy x a b :=
  ⟨fun h => by simpa using h.smul_right r⁻¹, (smul_right · r)⟩

@[to_additive (attr := simp)]
/--
lemma `SemiconjBy.smul_left_iff` / 引理 `SemiconjBy.smul_left_iff`

English:
lemma SemiconjBy.smul_left_iff
  given: {a b x : H} {r : G}
  proof: ⟨fun h => by simpa using h.smul_left r⁻¹, (smul_left · r)⟩

@[to_additive (attr := simp)]

中文:
引理 SemiconjBy.smul_left_iff
  条件: {a b x : H} {r : G}
  证明: ⟨fun h => by simpa using h.smul_left r⁻¹, (smul_left · r)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: h.smul_left, smul_left
-/
lemma SemiconjBy.smul_left_iff {a b x : H} {r : G} :
    SemiconjBy (r • x) a b ↔ SemiconjBy x a b :=
  ⟨fun h => by simpa using h.smul_left r⁻¹, (smul_left · r)⟩

@[to_additive (attr := simp)]
/--
lemma `Commute.smul_right_iff` / 引理 `Commute.smul_right_iff`

English:
lemma Commute.smul_right_iff
  statement: Commute a (g • b) ↔ Commute a b
  proof: SemiconjBy.smul_right_iff

@[to_additive (attr := simp)]

中文:
引理 Commute.smul_right_iff
  结论: Commute a (g • b) ↔ Commute a b
  证明: SemiconjBy.smul_right_iff

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.smul_right_iff, smul_right_iff
-/
lemma Commute.smul_right_iff : Commute a (g • b) ↔ Commute a b :=
  SemiconjBy.smul_right_iff

@[to_additive (attr := simp)]
/--
lemma `Commute.smul_left_iff` / 引理 `Commute.smul_left_iff`

English:
lemma Commute.smul_left_iff
  statement: Commute (g • a) b ↔ Commute a b
  proof: SemiconjBy.smul_left_iff

中文:
引理 Commute.smul_left_iff
  结论: Commute (g • a) b ↔ Commute a b
  证明: SemiconjBy.smul_left_iff

Depends on / 依赖: SemiconjBy, SemiconjBy.smul_left_iff, smul_left_iff
-/
lemma Commute.smul_left_iff : Commute (g • a) b ↔ Commute a b :=
  SemiconjBy.smul_left_iff

end Mul

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

/--
lemma `smul_inv` / 引理 `smul_inv`

English:
lemma smul_inv
  given: (g : G) (a : H)
  statement: (g • a)⁻¹ = g⁻¹ • a⁻¹
  proof: inv_eq_of_mul_eq_one_right by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]

中文:
引理 smul_inv
  条件: (g : G) (a : H)
  结论: (g • a)⁻¹ = g⁻¹ • a⁻¹
  证明: inv_eq_of_mul_eq_one_right by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]

Depends on / 依赖: inv_eq_of_mul_eq_one_right, mul_inv_cancel, one_smul, smul_mul_smul_comm
-/
lemma smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹ :=
inv_eq_of_mul_eq_one_right by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]

/--
lemma `smul_zpow` / 引理 `smul_zpow`

English:
lemma smul_zpow
  given: (g : G) (a : H) (n : Int)
  statement: (g • a) ^ n = g ^ n • a ^ n
  proof: by
  cases n <;> simp [smul_pow, smul_inv]

中文:
引理 smul_zpow
  条件: (g : G) (a : H) (n : 整数)
  结论: (g • a) ^ n = g ^ n • a ^ n
  证明: by
  cases n <;> simp [smul_pow, smul_inv]

Depends on / 依赖: smul_inv, smul_pow
-/
lemma smul_zpow (g : G) (a : H) (n : Int) : (g • a) ^ n = g ^ n • a ^ n := by
  cases n <;> simp [smul_pow, smul_inv]

end Group
end

/--
lemma `SMulCommClass.of_commMonoid` / 引理 `SMulCommClass.of_commMonoid`

English:
lemma SMulCommClass.of_commMonoid
  proof: by
    rw [← one_smul G (s • x)]; rw [← smul_assoc]; rw [← one_smul G x]; rw [← smul_assoc s 1 x]; rw [smul_comm]; rw [smul_assoc]; rw [one_smul]; rw [smul_assoc]; rw [one_smul]

中文:
引理 SMulCommClass.of_commMonoid
  证明: by
    rw [← one_smul G (s • x)]; rw [← smul_assoc]; rw [← one_smul G x]; rw [← smul_assoc s 1 x]; rw [smul_comm]; rw [smul_assoc]; rw [one_smul]; rw [smul_assoc]; rw [one_smul]

Depends on / 依赖: one_smul, smul_assoc, smul_comm
-/
lemma SMulCommClass.of_commMonoid
    (A B G : Type*) [CommMonoid G] [SMul A G] [SMul B G]
    [IsScalarTower A G G] [IsScalarTower B G G] :
    SMulCommClass A B G where
  smul_comm r s x := by
    rw [← one_smul G (s • x)]; rw [← smul_assoc]; rw [← one_smul G x]; rw [← smul_assoc s 1 x]; rw [smul_comm]; rw [smul_assoc]; rw [one_smul]; rw [smul_assoc]; rw [one_smul]

/--
lemma `IsScalarTower.of_commMonoid` / 引理 `IsScalarTower.of_commMonoid`

English:
lemma IsScalarTower.of_commMonoid
  statement: (R₁ R : Type*)
  proof: by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]

中文:
引理 IsScalarTower.of_commMonoid
  结论: (R₁ R : 类型)
  证明: by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]

Depends on / 依赖: mul_comm, smul_comm, smul_eq_mul
-/
lemma IsScalarTower.of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] [SMulCommClass R₁ R R] : IsScalarTower R₁ R R where
  smul_assoc x₁ y z := by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]

/--
lemma `isScalarTower_iff_smulCommClass_of_commMonoid` / 引理 `isScalarTower_iff_smulCommClass_of_commMonoid`

English:
lemma isScalarTower_iff_smulCommClass_of_commMonoid
  statement: (R₁ R : Type*)
  proof: ⟨fun _ => IsScalarTower.of_commMonoid R₁ R, fun _ => SMulCommClass.of_commMonoid R₁ R R⟩

中文:
引理 isScalarTower_iff_smulCommClass_of_commMonoid
  结论: (R₁ R : 类型)
  证明: ⟨fun _ => IsScalarTower.of_commMonoid R₁ R, fun _ => SMulCommClass.of_commMonoid R₁ R R⟩

Depends on / 依赖: IsScalarTower, IsScalarTower.of_commMonoid, SMulCommClass, SMulCommClass.of_commMonoid, of_commMonoid
-/
lemma isScalarTower_iff_smulCommClass_of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] :
    SMulCommClass R₁ R R ↔ IsScalarTower R₁ R R :=
  ⟨fun _ => IsScalarTower.of_commMonoid R₁ R, fun _ => SMulCommClass.of_commMonoid R₁ R R⟩

end

section CompatibleScalar

@[to_additive]
/--
lemma `smul_one_smul` / 引理 `smul_one_smul`

English:
lemma smul_one_smul
  statement: {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
  proof: by
  rw [smul_assoc]; rw [one_smul]

@[to_additive (attr := simp)]

中文:
引理 smul_one_smul
  结论: {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
  证明: by
  rw [smul_assoc]; rw [one_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: one_smul, smul_assoc
-/
lemma smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc]; rw [one_smul]

@[to_additive (attr := simp)]
/--
lemma `smul_one_mul` / 引理 `smul_one_mul`

English:
lemma smul_one_mul
  given: {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N)
  proof: by rw [smul_mul_assoc, one_mul]

@[to_additive (attr := simp)]

中文:
引理 smul_one_mul
  条件: {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N)
  证明: by rw [smul_mul_assoc, one_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: one_mul, smul_mul_assoc
-/
lemma smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]

@[to_additive (attr := simp)]
/--
lemma `mul_smul_one` / 引理 `mul_smul_one`

English:
lemma mul_smul_one
  given: {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N)
  proof: by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

@[to_additive]

中文:
引理 mul_smul_one
  条件: {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N)
  证明: by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

@[to_additive]

Depends on / 依赖: mul_one, smul_comm, smul_eq_mul
-/
lemma mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

@[to_additive]
/--
lemma `IsScalarTower.of_smul_one_mul` / 引理 `IsScalarTower.of_smul_one_mul`

English:
lemma IsScalarTower.of_smul_one_mul
  statement: {M N} [Monoid N] [SMul M N]
  proof: ⟨fun x y z => by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive]

中文:
引理 IsScalarTower.of_smul_one_mul
  结论: {M N} [Monoid N] [SMul M N]
  证明: ⟨fun x y z => by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive]

Depends on / 依赖: mul_assoc, smul_eq_mul
-/
lemma IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : forall (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z => by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive]
/--
lemma `SMulCommClass.of_mul_smul_one` / 引理 `SMulCommClass.of_mul_smul_one`

English:
lemma SMulCommClass.of_mul_smul_one
  statement: {M N} [Monoid N] [SMul M N]
  proof: ⟨fun x y z => by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

中文:
引理 SMulCommClass.of_mul_smul_one
  结论: {M N} [Monoid N] [SMul M N]
  证明: ⟨fun x y z => by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

Depends on / 依赖: mul_assoc, smul_eq_mul
-/
lemma SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : forall (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z => by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

/--
lemma `IsScalarTower.to₁₂₄` / 引理 `IsScalarTower.to₁₂₄`

English:
lemma IsScalarTower.to₁₂₄
  statement: (M N P Q)
  proof: by rw [← smul_one_smul P, smul_assoc m, smul_assoc, smul_one_smul]

中文:
引理 IsScalarTower.to₁₂₄
  结论: (M N P Q)
  证明: by rw [← smul_one_smul P, smul_assoc m, smul_assoc, smul_one_smul]
-/
@[to_additive] lemma IsScalarTower.to₁₂₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul N P] [SMul N Q] [Monoid P] [MulAction P Q]
    [IsScalarTower M N P] [IsScalarTower M P Q] [IsScalarTower N P Q] : IsScalarTower M N Q where
  smul_assoc m n q := by rw [← smul_one_smul P, smul_assoc m, smul_assoc, smul_one_smul]

/--
lemma `IsScalarTower.to₁₃₄` / 引理 `IsScalarTower.to₁₃₄`

English:
lemma IsScalarTower.to₁₃₄
  statement: (M N P Q)
  proof: by rw [← smul_one_smul N m, smul_assoc, smul_one_smul]

中文:
引理 IsScalarTower.to₁₃₄
  结论: (M N P Q)
  证明: by rw [← smul_one_smul N m, smul_assoc, smul_one_smul]
-/
@[to_additive] lemma IsScalarTower.to₁₃₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul P Q] [Monoid N] [MulAction N P] [MulAction N Q]
    [IsScalarTower M N P] [IsScalarTower M N Q] [IsScalarTower N P Q] : IsScalarTower M P Q where
  smul_assoc m p q := by rw [← smul_one_smul N m, smul_assoc, smul_one_smul]

/--
lemma `IsScalarTower.to₂₃₄` / 引理 `IsScalarTower.to₂₃₄`

English:
lemma IsScalarTower.to₂₃₄
  statement: (M N P Q)
  proof: by obtain ⟨m, rfl⟩ := h n; simp_rw [smul_one_smul, smul_assoc]

中文:
引理 IsScalarTower.to₂₃₄
  结论: (M N P Q)
  证明: by obtain ⟨m, rfl⟩ := h n; simp_rw [smul_one_smul, smul_assoc]
-/
@[to_additive] lemma IsScalarTower.to₂₃₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul P Q] [Monoid N] [MulAction N P] [MulAction N Q]
    [IsScalarTower M N P] [IsScalarTower M N Q] [IsScalarTower M P Q]
    (h : Function.Surjective fun m : M => m • (1 : N)) : IsScalarTower N P Q where
  smul_assoc n p q := by obtain ⟨m, rfl⟩ := h n; simp_rw [smul_one_smul, smul_assoc]

end CompatibleScalar

/-- Typeclass for multiplicative actions on multiplicative structures.

The key axiom here is `smul_mul : g • (x * y) = (g • x) * (g • y)`.
If `G` is a multiplicative group with automorphism group `Γ`, then there is a natural instance of
`MulDistribMulAction Γ G`.

The axiom is also satisfied by a Galois group $Gal(L/K)$ acting on the field `L`,
but here you can use the even stronger class `MulSemiringAction`, which captures
how the action plays with both multiplication and addition. -/
@[ext]
/--
Definition of `MulDistribMulAction` / `MulDistribMulAction` 的定义

English:
class MulDistribMulAction
  parameters: (M N : Type*) [Monoid M] [Monoid N]
  extends: MulAction M N
  axioms and operations (2):
    - smul_one : forall r : M, r • (1 : N) = 1
    - smul_mul : forall (r : M) (x y : N), r • (x * y) = r • x * r • y

中文:
类 MulDistribMulAction
  参数: (M N : 类型) [Monoid M] [Monoid N]
  继承: MulAction M N
  公理与运算 (2 个):
    - smul_one : 对任意 r : M, r • (1 : N) = 1
    - smul_mul : 对任意 (r : M) (x y : N), r • (x * y) = r • x * r • y
-/
class MulDistribMulAction (M N : Type*) [Monoid M] [Monoid N] extends MulAction M N where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : forall r : M, r • (1 : N) = 1
  /-- Distributivity of `•` across `*` -/
  smul_mul : forall (r : M) (x y : N), r • (x * y) = r • x * r • y

/-- Typeclass for additive actions on additive structures.

The key axiom here is `vadd_add : g +ᵥ (x + y) = (g +ᵥ x) + (g +ᵥ y)`.
If `G` is an additive group with additive automorphism group `Γ`, then there is a natural instance
of `AddDistribAddAction Γ G`. -/
@[ext]
/--
Definition of `AddDistribAddAction` / `AddDistribAddAction` 的定义

English:
class AddDistribAddAction
  parameters: (M N : Type*) [AddMonoid M] [AddMonoid N]
  extends: AddAction M N
  axioms and operations (2):
    - vadd_zero : forall r : M, r +ᵥ (0 : N) = 0
    - vadd_add : forall (r : M) (x y : N), r +ᵥ (x + y) = (r +ᵥ x) + (r +ᵥ y)

中文:
类 AddDistribAddAction
  参数: (M N : 类型) [AddMonoid M] [AddMonoid N]
  继承: AddAction M N
  公理与运算 (2 个):
    - vadd_zero : 对任意 r : M, r +ᵥ (0 : N) = 0
    - vadd_add : 对任意 (r : M) (x y : N), r +ᵥ (x + y) = (r +ᵥ x) + (r +ᵥ y)
-/
class AddDistribAddAction (M N : Type*) [AddMonoid M] [AddMonoid N] extends AddAction M N where
  /-- Acting on `0` by a scalar gives `0` -/
  vadd_zero : forall r : M, r +ᵥ (0 : N) = 0
  /-- Distributivity of `+ᵥ` across `+` -/
  vadd_add : forall (r : M) (x y : N), r +ᵥ (x + y) = (r +ᵥ x) + (r +ᵥ y)

export MulDistribMulAction (smul_one)
export AddDistribAddAction (vadd_zero)

attribute [to_additive existing] MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

@[to_additive]
/--
lemma `smul_mul'` / 引理 `smul_mul'`

English:
lemma smul_mul'
  given: (a : M) (b₁ b₂ : N)
  statement: a • (b₁ * b₂) = a • b₁ * a • b₂
  proof: MulDistribMulAction.smul_mul ..

中文:
引理 smul_mul'
  条件: (a : M) (b₁ b₂ : N)
  结论: a • (b₁ * b₂) = a • b₁ * a • b₂
  证明: MulDistribMulAction.smul_mul ..

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.smul_mul, smul_mul
-/
lemma smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul ..

end MulDistribMulAction

section IsCancelSMul

variable (G P : Type*)
-- TODO: IsRightCancelSmul

/--
Definition of `IsLeftCancelVAdd` / `IsLeftCancelVAdd` 的定义

English:
class IsLeftCancelVAdd
  parameters: [VAdd G P]
  axioms and operations (1):
    - left_cancel' : forall (a : G) (b c : P), a +ᵥ b = a +ᵥ c -> b = c

中文:
类 IsLeftCancelVAdd
  参数: [VAdd G P]
  公理与运算 (1 个):
    - left_cancel' : 对任意 (a : G) (b c : P), a +ᵥ b = a +ᵥ c -> b = c
-/
class IsLeftCancelVAdd [VAdd G P] : Prop where
  protected left_cancel' : forall (a : G) (b c : P), a +ᵥ b = a +ᵥ c -> b = c

/-- A scalar multiplication is left-cancellative if it is pointwise injective on the left. -/
@[to_additive]
/--
Definition of `IsLeftCancelSMul` / `IsLeftCancelSMul` 的定义

English:
class IsLeftCancelSMul
  parameters: [SMul G P]
  axioms and operations (1):
    - left_cancel' : forall (a : G) (b c : P), a • b = a • c -> b = c

中文:
类 IsLeftCancelSMul
  参数: [SMul G P]
  公理与运算 (1 个):
    - left_cancel' : 对任意 (a : G) (b c : P), a • b = a • c -> b = c
-/
class IsLeftCancelSMul [SMul G P] : Prop where
  protected left_cancel' : forall (a : G) (b c : P), a • b = a • c -> b = c

@[to_additive]
/--
lemma `IsLeftCancelSMul.left_cancel` / 引理 `IsLeftCancelSMul.left_cancel`

English:
lemma IsLeftCancelSMul.left_cancel
  given: {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P)
  proof: IsLeftCancelSMul.left_cancel' a b c

@[to_additive]

中文:
引理 IsLeftCancelSMul.left_cancel
  条件: {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P)
  证明: IsLeftCancelSMul.left_cancel' a b c

@[to_additive]

Depends on / 依赖: IsLeftCancelSMul, IsLeftCancelSMul.left_cancel, left_cancel
-/
lemma IsLeftCancelSMul.left_cancel {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c -> b = c := IsLeftCancelSMul.left_cancel' a b c

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: G] [IsLeftCancelMul G] : IsLeftCancelSMul G G where
  body: IsLeftCancelMul.mul_left_cancel

中文:
实例 [Mul
  签名: G] [IsLeftCancelMul G] : IsLeftCancelSMul G G where
  定义体: IsLeftCancelMul.mul_left_cancel

Depends on / 依赖: IsLeftCancelMul, IsLeftCancelMul.mul_left_cancel, mul_left_cancel
-/
instance [Mul G] [IsLeftCancelMul G] : IsLeftCancelSMul G G where
  left_cancel' := IsLeftCancelMul.mul_left_cancel

/--
Definition of `IsCancelVAdd` / `IsCancelVAdd` 的定义

English:
class IsCancelVAdd
  parameters: [VAdd G P]
  extends: IsLeftCancelVAdd G P
  axioms and operations (1):
    - right_cancel' : forall (a b : G) (c : P), a +ᵥ c = b +ᵥ c -> a = b

中文:
类 IsCancelVAdd
  参数: [VAdd G P]
  继承: IsLeftCancelVAdd G P
  公理与运算 (1 个):
    - right_cancel' : 对任意 (a b : G) (c : P), a +ᵥ c = b +ᵥ c -> a = b
-/
class IsCancelVAdd [VAdd G P] : Prop extends IsLeftCancelVAdd G P where
  protected right_cancel' : forall (a b : G) (c : P), a +ᵥ c = b +ᵥ c -> a = b

/-- A scalar multiplication is cancellative if it is pointwise injective on the left and right.

A group action is cancellative in this sense if and only if it is **free**.
See `isCancelSMul_iff_eq_one_of_smul_eq` for a more familiar condition. -/
@[to_additive]
/--
Definition of `IsCancelSMul` / `IsCancelSMul` 的定义

English:
class IsCancelSMul
  parameters: [SMul G P]
  extends: IsLeftCancelSMul G P
  axioms and operations (1):
    - right_cancel' : forall (a b : G) (c : P), a • c = b • c -> a = b

中文:
类 IsCancelSMul
  参数: [SMul G P]
  继承: IsLeftCancelSMul G P
  公理与运算 (1 个):
    - right_cancel' : 对任意 (a b : G) (c : P), a • c = b • c -> a = b
-/
class IsCancelSMul [SMul G P] : Prop extends IsLeftCancelSMul G P where
  protected right_cancel' : forall (a b : G) (c : P), a • c = b • c -> a = b

@[to_additive]
/--
lemma `IsCancelSMul.left_cancel` / 引理 `IsCancelSMul.left_cancel`

English:
lemma IsCancelSMul.left_cancel
  given: {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P)
  proof: IsLeftCancelSMul.left_cancel' a b c

@[to_additive]

中文:
引理 IsCancelSMul.left_cancel
  条件: {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P)
  证明: IsLeftCancelSMul.left_cancel' a b c

@[to_additive]

Depends on / 依赖: IsLeftCancelSMul, IsLeftCancelSMul.left_cancel, left_cancel
-/
lemma IsCancelSMul.left_cancel {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c -> b = c := IsLeftCancelSMul.left_cancel' a b c

@[to_additive]
/--
lemma `IsCancelSMul.right_cancel` / 引理 `IsCancelSMul.right_cancel`

English:
lemma IsCancelSMul.right_cancel
  given: {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c : P)
  proof: IsCancelSMul.right_cancel' a b c

@[to_additive]

中文:
引理 IsCancelSMul.right_cancel
  条件: {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c : P)
  证明: IsCancelSMul.right_cancel' a b c

@[to_additive]

Depends on / 依赖: IsCancelSMul, IsCancelSMul.right_cancel, right_cancel
-/
lemma IsCancelSMul.right_cancel {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c : P) :
    a • c = b • c -> a = b := IsCancelSMul.right_cancel' a b c

@[to_additive]
/--
lemma `IsCancelSMul.eq_one_of_smul` / 引理 `IsCancelSMul.eq_one_of_smul`

English:
lemma IsCancelSMul.eq_one_of_smul
  statement: {G P} [Monoid G] [MulAction G P] [IsCancelSMul G P] {g : G}
  proof: IsCancelSMul.right_cancel g 1 x ((one_smul G x).symm ▸ h)

@[to_additive]

中文:
引理 IsCancelSMul.eq_one_of_smul
  结论: {G P} [Monoid G] [MulAction G P] [IsCancelSMul G P] {g : G}
  证明: IsCancelSMul.right_cancel g 1 x ((one_smul G x).symm ▸ h)

@[to_additive]

Depends on / 依赖: IsCancelSMul, IsCancelSMul.right_cancel, one_smul, right_cancel
-/
lemma IsCancelSMul.eq_one_of_smul {G P} [Monoid G] [MulAction G P] [IsCancelSMul G P] {g : G}
    {x : P} (h : g • x = x) : g = 1 :=
  IsCancelSMul.right_cancel g 1 x ((one_smul G x).symm ▸ h)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelMonoid
  signature: G] : IsCancelSMul G G where
  body: IsLeftCancelMul.mul_left_cancel
  right_cancel' _ _ _ := mul_right_cancel

@[to_additive]

中文:
实例 [CancelMonoid
  签名: G] : IsCancelSMul G G where
  定义体: IsLeftCancelMul.mul_left_cancel
  right_cancel' _ _ _ := mul_right_cancel

@[to_additive]

Depends on / 依赖: IsLeftCancelMul, IsLeftCancelMul.mul_left_cancel, mul_left_cancel
-/
instance [CancelMonoid G] : IsCancelSMul G G where
  left_cancel' := IsLeftCancelMul.mul_left_cancel
  right_cancel' _ _ _ := mul_right_cancel

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [MulAction G P] : IsLeftCancelSMul G P where
  body: by rw [← inv_smul_smul a b, h, inv_smul_smul]

中文:
实例 [Group
  签名: G] [MulAction G P] : IsLeftCancelSMul G P where
  定义体: by rw [← inv_smul_smul a b, h, inv_smul_smul]

Depends on / 依赖: inv_smul_smul
-/
instance [Group G] [MulAction G P] : IsLeftCancelSMul G P where
  left_cancel' a b c h := by rw [← inv_smul_smul a b, h, inv_smul_smul]

end IsCancelSMul
