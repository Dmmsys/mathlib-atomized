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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 910) Mul.toSMulMulOpposite (α : Type*) [Mul α] : SMul αᵐᵒᵖ α where
  smul a b := b * a.unop

@[to_additive (attr := simp)]
/-
**smul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl

@[to_additive]
/-
**op_smul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：op_smul_eq_mul {α : Type*} [Mul α] (a b : α) : MulOpposite.op a • b = b * 
a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_smul_eq_mul {α : Type*} [Mul α] (a b : α) : MulOpposite.op a • b = b * a := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.smul_eq_mul_unop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulOpposite.smul_eq_mul_unop [Mul α] (a : αᵐᵒᵖ) (b : α) : a • b = b * a.un
op
参数：a : αᵐᵒᵖ；b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulOpposite.smul_eq_mul_unop [Mul α] (a : αᵐᵒᵖ) (b : α) : a • b = b * a.unop := rfl

/-- Type class for actions by additive semigroups, with notation `g +ᵥ p`.

The `AddSemigroupAction G P` typeclass says that the additive semigroup `G` acts additively on a
type `P`.  More precisely this means that the action satisfies the axiom
`(g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)`.  A mathematician might simply say that the additive semigroup
`G` acts on `P`.

For example, if `A` is an additive semigroup and `X` is a type, if a mathematician says
say "let `A` act on the set `X`" they will usually mean `[AddSemigroupAction A X]`. -/
/-
**AddSemigroupAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → Type u_10 → [AddSemigroup G] → Type (max u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for actions by additive semigroups, with notation `g +ᵥ p`.

The `AddSemigroupAction G P` typeclass says that the additive semigroup `G` acts
 additively on a
type `P`.  More precisely this means that the action satisfies the axiom
`(g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)`.  A mathematician might simply say that the a
dditive semigroup
`G` acts on `P`.

For example, if `A` is an additive semigroup and `X` is a type, if a mathematici
an says
say "let `A` act on the set `X`" they will usually mean `[AddSemigroupAction A X
]`.
-/
class AddSemigroupAction (G P : Type*) [AddSemigroup G] extends VAdd G P where
  /-- Associativity of `+ᵥ` and `+` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ g₂ +ᵥ p

/-- Type class for actions by semigroups, with notation `g • p`.

The `SemigroupAction G P` typeclass says that the semigroup `G` acts multiplicatively on a type `P`.
More precisely this means that the action satisfies the axiom `(g₁ * g₂) • p = g₁ • (g₂ • p)`.
A mathematician might simply say that the semigroup `G` acts on `P`.

For example, if `G` is a semigroup and `X` is a type, if a mathematician says
say "let `G` act on the set `X`" they will probably mean  `[SemigroupAction G X]`. -/
@[to_additive (attr := ext)]
/-
**SemigroupAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_9) → Type u_10 → [Semigroup α] → Type (max u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for actions by semigroups, with notation `g • p`.

The `SemigroupAction G P` typeclass says that the semigroup `G` acts multiplicat
ively on a type `P`.
More precisely this means that the action satisfies the axiom `(g₁ * g₂) • p = g
₁ • (g₂ • p)`.
A mathematician might simply say that the semigroup `G` acts on `P`.

For example, if `G` is a semigroup and `X` is a type, if a mathematician says
say "let `G` act on the set `X`" they will probably mean  `[SemigroupAction G X]
`.
-/
class SemigroupAction (α β : Type*) [Semigroup α] extends SMul α β where
  /-- Associativity of `•` and `*` -/
  mul_smul (x y : α) (b : β) : (x * y) • b = x • y • b

/--
Type class for additive monoid actions on types, with notation `g +ᵥ p`.

The `AddAction G P` typeclass says that the additive monoid `G` acts additively on a type `P`.
More precisely this means that the action satisfies the two axioms `0 +ᵥ p = p` and
`(g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)`. A mathematician might simply say that the additive monoid `G`
acts on `P`.

For example, if `A` is an additive group and `X` is a type, if a mathematician says
say "let `A` act on the set `X`" they will usually mean `[AddAction A X]`.
-/
/-
**AddAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → Type u_10 → [AddMonoid G] → Type (max u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for additive monoid actions on types, with notation `g +ᵥ p`.

The `AddAction G P` typeclass says that the additive monoid `G` acts additively 
on a type `P`.
More precisely this means that the action satisfies the two axioms `0 +ᵥ p = p` 
and
`(g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)`. A mathematician might simply say that the ad
ditive monoid `G`
acts on `P`.

For example, if `A` is an additive group and `X` is a type, if a mathematician s
ays
say "let `A` act on the set `X`" they will usually mean `[AddAction A X]`.
-/
class AddAction (G : Type*) (P : Type*) [AddMonoid G] extends AddSemigroupAction G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p

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
/-
**MulAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_9) → Type u_10 → [Monoid α] → Type (max u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type class for monoid actions on types, with notation `g • p`.

The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on 
a type `P`.
More precisely this means that the action satisfies the two axioms `1 • p = p` a
nd
`(g₁ * g₂) • p = g₁ • (g₂ • p)`. A mathematician might simply say that the monoi
d `G`
acts on `P`.

For example, if `G` is a group and `X` is a type, if a mathematician says
say "let `G` act on the set `X`" they will probably mean `[MulAction G X]`.
-/
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SemigroupAction α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b

/-! ### Scalar tower and commuting actions -/

/-- A typeclass mixin saying that two additive actions on the same space commute. -/
/-
**VAddCommClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → (α : Type u_11) → [VAdd M α] → [VAdd N 
α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass mixin saying that two additive actions on the same space commute.
-/
class VAddCommClass (M N α : Type*) [VAdd M α] [VAdd N α] : Prop where
  /-- `+ᵥ` is left commutative -/
  vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive]
/-
**SMulCommClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → (α : Type u_11) → [SMul M α] → [SMul N 
α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass mixin saying that two multiplicative actions on the same space commu
te.
-/
class SMulCommClass (M N α : Type*) [SMul M α] [SMul N α] : Prop where
  /-- `•` is left commutative -/
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a

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
/-
**SMulCommClass.symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M 
N α] : SMulCommClass N M α where smul_comm a' a b
参数：M N α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…

--- 原说明 ---
Commutativity of actions is a symmetric relation. This lemma can't be an instanc
e because this
would cause a loop in the instance search graph.
-/
lemma SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass N M α where smul_comm a' a b := (smul_comm a a' b).symm

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc VAddCommClass.symm

@[to_additive]
/-
**Function.Injective.smulCommClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N 
β] [SMulCommClass M N β] {f : α -> β} (hf : Injective f) (h₁ : forall (c : M) x,
 f (c • x) = c • f x) (h₂ : forall (c : N) x, f (c • x) = c • f x) : SMulCommCla
ss M N α where smul_comm c₁ c₂ x
参数：hf : Injective f；h₁ : forall (c : M) x, f (c • x) = c • f x；h₂ : forall (c : 
N) x, f (c • x) = c • f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α → β} (hf : Injective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N α where
  smul_comm c₁ c₂ x := hf <| by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

@[to_additive]
/-
**Function.Surjective.smulCommClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N
 β] [SMulCommClass M N α] {f : α -> β} (hf : Surjective f) (h₁ : forall (c : M) 
x, f (c • x) = c • f x) (h₂ : forall (c : N) x, f (c • x) = c • f x) : SMulCommC
lass M N β where smul_comm c₁ c₂
参数：hf : Surjective f；h₁ : forall (c : M) x, f (c • x) = c • f x；h₂ : forall (c :
 N) x, f (c • x) = c • f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α → β} (hf : Surjective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x ↦ by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

@[to_additive]
/-
**smulCommClass_self** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulComm
Class M M α where smul_comm a a' b
参数：M α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
instance smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulCommClass M M α where
  smul_comm a a' b := by rw [← mul_smul, mul_comm, mul_smul]

/-- An instance of `VAddAssocClass M N α` states that the additive action of `M` on `α` is
determined by the additive actions of `M` on `N` and `N` on `α`. -/
/-
**VAddAssocClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → (α : Type u_11) → [VAdd M N] → [VAdd N 
α] → [VAdd M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An instance of `VAddAssocClass M N α` states that the additive action of `M` on 
`α` is
determined by the additive actions of `M` on `N` and `N` on `α`.
-/
class VAddAssocClass (M N α : Type*) [VAdd M N] [VAdd N α] [VAdd M α] : Prop where
  /-- Associativity of `+ᵥ` -/
  vadd_assoc : ∀ (x : M) (y : N) (z : α), (x +ᵥ y) +ᵥ z = x +ᵥ y +ᵥ z

/-- An instance of `IsScalarTower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
@[to_additive]
/-
**IsScalarTower** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → (α : Type u_11) → [SMul M N] → [SMul N 
α] → [SMul M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An instance of `IsScalarTower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`.
-/
class IsScalarTower (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] : Prop where
  /-- Associativity of `•` -/
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z

@[to_additive (attr := simp)]
/-
**smul_assoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x
 : M) (y : N) (z : α) : (x • y) • z = x • y • z
参数：x : M；y : N；z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…
-/
lemma smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α] (x : M) (y : N)
    (z : α) : (x • y) • z = x • y • z := IsScalarTower.smul_assoc x y z

@[to_additive]
/-
**Semigroup.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance Semigroup.isScalarTower [Semigroup α] : IsScalarTower α α α := ⟨mul_assoc⟩

/-- An instance of `SMulDistribClass G R S` states that the multiplicative
action of `G` on `S` is determined by the multiplicative actions of `G` on `R`
and `R` on `S`.

This is similar to `IsScalarTower` except that the action of `G` distributes
over the action of `R` on `S`.

E.g. if `M/L/K` is a tower of galois extensions then `SMulDistribClass Gal(M/K) L M`. -/
/-
**SMulDistribClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → (R : Type u_10) → (S : Type u_11) → [SMul G R] → [SMul G 
S] → [SMul R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An instance of `SMulDistribClass G R S` states that the multiplicative
action of `G` on `S` is determined by the multiplicative actions of `G` on `R`
and `R` on `S`.

This is similar to `IsScalarTower` except that the action of `G` distributes
over the action of `R` on `S`.

E.g. if `M/L/K` is a tower of galois extensions then `SMulDistribClass Gal(M/K) 
L M`.
-/
class SMulDistribClass (G R S : Type*) [SMul G R] [SMul G S] [SMul R S] : Prop where
  smul_distrib_smul (g : G) (r : R) (s : S) : g • r • s = (g • r) • (g • s)

export SMulDistribClass (smul_distrib_smul)

/-- A typeclass indicating that the right (aka `AddOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `+ᵥ`. -/
/-
**IsCentralVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (α : Type u_10) → [VAdd M α] → [VAdd Mᵃᵒᵖ α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass indicating that the right (aka `AddOpposite`) and left actions by `M
` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a versi
on of commutativity
for `+ᵥ`.
-/
class IsCentralVAdd (M α : Type*) [VAdd M α] [VAdd Mᵃᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_vadd_eq_vadd : ∀ (m : M) (a : α), AddOpposite.op m +ᵥ a = m +ᵥ a

/-- A typeclass indicating that the right (aka `MulOpposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
@[to_additive]
/-
**IsCentralScalar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (α : Type u_10) → [SMul M α] → [SMul Mᵐᵒᵖ α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass indicating that the right (aka `MulOpposite`) and left actions by `M
` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a versi
on of commutativity
for `•`.
-/
class IsCentralScalar (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α] : Prop where
  /-- The right and left actions of `M` on `α` are equal. -/
  op_smul_eq_smul : ∀ (m : M) (a : α), MulOpposite.op m • a = m • a

@[to_additive]
/-
**IsCentralScalar.unop_smul_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α] [
IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a
参数：m : Mᵐᵒᵖ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
lemma IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)
export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

attribute [simp] IsCentralScalar.op_smul_eq_smul

-- these instances are very low priority, as there is usually a faster way to find these instances
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) SMulCommClass.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) SMulCommClass.op_right [SMul M α] [SMul N α] [SMul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [SMulCommClass M N α] : SMulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a ↦ by rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) IsScalarTower.op_left [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [SMul M N] [SMul Mᵐᵒᵖ N] [IsCentralScalar M N] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵐᵒᵖ N α where
  smul_assoc m n a := by rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) IsScalarTower.op_right [SMul M α] [SMul M N] [SMul N α]
    [SMul Nᵐᵒᵖ α] [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α where
  smul_assoc m n a := by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]

namespace SMul
variable [SMul M α]

/-- Auxiliary definition for `SMul.comp`, `MulAction.compHom`,
`DistribMulAction.compHom`, `Module.compHom`, etc. -/
@[to_additive (attr := simp, implicit_reducible)
/-- Auxiliary definition for `VAdd.comp`, `AddAction.compHom`, etc. -/]
/-
**SMul.comp.smul** 是 Mathlib 中的一个定义，位于命名空间 `SMul.comp`。
形式化陈述：{M : Type u_1} → {N : Type u_2} → {α : Type u_5} → [SMul M α] → (N → M) → 
N → α → α
参数：N → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comp.smul (g : N → M) (n : N) (a : α) : α := g n • a

variable (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`. -/
-- See note [reducible non-instances]
-- Since this is reducible, we make sure to go via
-- `SMul.comp.smul` to prevent typeclass inference unfolding too far
@[to_additive /-- An additive action of `M` on `α` and a function `N → M` induces an additive
action of `N` on `α`. -/]
/-
**SMul.comp** 是 Mathlib 中的一个缩写定义，位于命名空间 `SMul`。
形式化陈述：comp (g : N -> M) : SMul N α where smul
参数：g : N -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev comp (g : N → M) : SMul N α where smul := SMul.comp.smul g

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
/-
**SMul.comp.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `SMul.comp`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} {β : Type u_6} [inst : SMul
 M α] [inst_1 : SMul M β] [inst_2 : SMul α β]   [IsScalarTower M α β] (g : N → M
), IsScalarTower N α β
参数：g : N → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
lemma comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables. -/]
/-
**SMul.comp.smulCommClass** 是 Mathlib 中的一个定理，位于命名空间 `SMul.comp`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} {β : Type u_6} [inst : SMul
 M α] [inst_1 : SMul β α]   [SMulCommClass M β α] (g : N → M), SMulCommClass N β
 α
参数：g : N → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)

/-- This cannot be an instance because it can cause infinite loops whenever the `SMul` arguments
are still metavariables. -/
@[to_additive
/-- This cannot be an instance because it can cause infinite loops whenever the `VAdd` arguments
are still metavariables. -/]
/-
**SMul.comp.smulCommClass'** 是 Mathlib 中的一个定理，位于命名空间 `SMul.comp`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} {β : Type u_6} [inst : SMul
 M α] [inst_1 : SMul β α]   [SMulCommClass β M α] (g : N → M), SMulCommClass β N
 α
参数：g : N → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)

end SMul

section

/-- Note that the `SMulCommClass α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
/-
**mul_smul_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
 x * s • y = s • (x * y)
参数：s : α；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…

--- 原说明 ---
Note that the `SMulCommClass α β β` typeclass argument is usually satisfied by `
Algebra α β`.
-/
lemma mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s : α) (x y : β) :
    x * s • y = s • (x * y) := (smul_comm s x y).symm

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
/-
**smul_mul_assoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) 
: r • x * y = r • (x * y)
参数：r : α；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z

--- 原说明 ---
Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `
Algebra α β`.
-/
lemma smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x * y = r • (x * y) := smul_assoc r x y

/-- Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `Algebra α β`. -/
@[to_additive]
/-
**smul_div_assoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (
x y : β) : r • x / y = r • (x / y)
参数：r : α；x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note that the `IsScalarTower α β β` typeclass argument is usually satisfied by `
Algebra α β`.
-/
lemma smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

@[to_additive]
/-
**smul_smul_smul_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
 [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : 
β) (c : γ) (d : δ) : (a • b) • c • d = (a • c) • b • d
参数：a : α；b : β；c : γ；d : δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by rw [smul_assoc, smul_assoc, smul_comm b]

/-- Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass arguments are usually
satisfied by `Algebra α β`. -/
@[to_additive]
/-
**smul_mul_smul_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β] [IsSca
larTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β) : (a • b) 
* (c • d) = (a * c) • (b * d)
参数：a : α；b : β；c : α；d : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…

--- 原说明 ---
Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass argument
s are usually
satisfied by `Algebra α β`.
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
/-
**mul_smul_mul_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β] [IsScal
arTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) : (a * b) • (c * d) = (
a • c) * (b • d)
参数：a b : α；c d : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…

--- 原说明 ---
Note that the `IsScalarTower α β β` and `SMulCommClass α β β` typeclass argument
s are usually
satisfied by `Algebra α β`.
-/
lemma mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) :
    (a * b) • (c * d) = (a • c) * (b • d) := smul_smul_smul_comm a b c d

variable [SMul M α]

@[to_additive]
/-
**SemiconjBy.smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] 
{x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy x (r • a) (r • b)
参数：h : SemiconjBy x a b；r : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
-/
lemma SemiconjBy.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
    (h : SemiconjBy x a b) (r : M) : SemiconjBy x (r • a) (r • b) := by
  rw [SemiconjBy, mul_smul_comm, smul_mul_assoc, h.eq]

@[to_additive]
/-
**SemiconjBy.smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {
x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy (r • x) a b
参数：h : SemiconjBy x a b；r : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
-/
lemma SemiconjBy.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {x a b : α}
    (h : SemiconjBy x a b) (r : M) : SemiconjBy (r • x) a b := by
  rw [SemiconjBy, mul_smul_comm, smul_mul_assoc, h.eq]

@[to_additive]
/-
**Commute.smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a 
b : α} (h : Commute a b) (r : M) : Commute a (r • b)
参数：h : Commute a b；r : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.smul_right`：SemiconjBy.smul_right [Mul α] [SMulCommClass M α 
α] [IsScalarTower M α α] {x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy
 x (r • a) …
-/
lemma Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) :=
  SemiconjBy.smul_right h r

@[to_additive]
/-
**Commute.smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b
 : α} (h : Commute a b) (r : M) : Commute (r • a) b
参数：h : Commute a b；r : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.smul_left`：SemiconjBy.smul_left [Mul α] [SMulCommClass M α α]
 [IsScalarTower M α α] {x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy (
r • x) a b
-/
lemma Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b :=
  SemiconjBy.smul_left h r

end

section
variable [Monoid M] [MulAction M α] {a : M}

@[to_additive]
/-
**smul_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
参数：a₁ a₂ : M；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

variable (M)

@[to_additive (attr := simp)]
/-
**one_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_smul (b : α) : (1 : M) • b = b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b
-/
lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _

/-- `SMul` version of `one_mul_eq_id` -/
@[to_additive /-- `VAdd` version of `zero_add_eq_id` -/]
/-
**one_smul_eq_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_smul_eq_id : (((1 : M) • ·) : α -> α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
`SMul` version of `one_mul_eq_id`
-/
lemma one_smul_eq_id : (((1 : M) • ·) : α → α) = id := funext <| one_smul _

/-- `SMul` version of `comp_mul_left` -/
@[to_additive /-- `VAdd` version of `comp_add_left` -/]
/-
**comp_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α ->
 α)
参数：a₁ a₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
`SMul` version of `comp_mul_left`
-/
lemma comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α → α) :=
  funext fun _ ↦ (mul_smul _ _ _).symm

variable {M}

@[to_additive (attr := simp)]
/-
**smul_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {α : Type u_5} [inst : Monoid M] [inst_1 : MulAction M α]
 (a : M) (n : ℕ),   (fun x => a • x)^[n] = fun x => a ^ n • x
参数：a : M；n : ℕ；fun x => a • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_iterate (a : M) : ∀ n : ℕ, (a • · : α → α)^[n] = (a ^ n • ·)
  | 0 => by simp [funext_iff]
  | n + 1 => by ext; simp [smul_iterate, pow_succ, smul_smul]

@[to_additive]
/-
**smul_iterate_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_iterate_apply (a : M) (n : Nat) (x : α) : (a • ·)^[n] x = a ^ n • x
参数：a : M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_iterate`：∀ {M : Type u_1} {α : Type u_5} [inst : Monoid M] [inst_1 
: MulAction M α] (a : M) (n : ℕ),   (fun x => a • x)^[n] = fun x => a ^ n • x
-/
lemma smul_iterate_apply (a : M) (n : ℕ) (x : α) : (a • ·)^[n] x = a ^ n • x := by
  rw [smul_iterate]

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive
    /-- Pullback an additive action along an injective map respecting `+ᵥ`. -/]
/-
**Function.Injective.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{M : Type u_1} →   {α : Type u_5} →     {β : Type u_6} →       [inst : Mon
oid M] →         [inst_1 : MulAction M α] →           [inst_2 : SMul M β] →     
        (f : β → α) → Function.Injective f → (∀ (c : M) (x : β), f (c • x) = c •
 f x) → MulAction M β
参数：f : β → α；∀ (c : M) (x : β), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Injective.mulAction [SMul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  one_smul x := hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul c₁ c₂ x := hf <| by simp only [smul, mul_smul]

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[to_additive
    /-- Pushforward an additive action along a surjective map respecting `+ᵥ`. -/]
/-
**Function.Surjective.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：{M : Type u_1} →   {α : Type u_5} →     {β : Type u_6} →       [inst : Mon
oid M] →         [inst_1 : MulAction M α] →           [inst_2 : SMul M β] →     
        (f : α → β) → Function.Surjective f → (∀ (c : M) (x : α), f (c • x) = c 
• f x) → MulAction M β
参数：f : α → β；∀ (c : M) (x : α), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Surjective.mulAction [SMul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 1100) Monoid.toMulAction : MulAction M M where
  smul := (· * ·)
  one_smul := one_mul
  mul_smul := mul_assoc

@[to_additive]
/-
**IsScalarTower.left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsScalarTower.left : IsScalarTower M M α where smul_assoc x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
instance IsScalarTower.left : IsScalarTower M M α where
  smul_assoc x y z := mul_smul x y z

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [CommMonoid M] [SMul R M] [IsScalarTower R M M] : SMulCommClass R M M where
  smul_comm r s x := by
    rw [← one_smul M (s • x), ← smul_assoc, smul_comm, smul_assoc, one_smul]

variable {M}

section Monoid
variable [Monoid N] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]

/-
**smul_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N] [ins
t_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N] (r : M) (x : 
N) (n : ℕ), (r • x) ^ n = r ^ n • x ^ n
参数：r : M；x : N；n : ℕ；r • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_pow (r : M) (x : N) : ∀ n, (r • x) ^ n = r ^ n • x ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ', smul_pow _ _ n, smul_mul_smul_comm, ← pow_succ', ← pow_succ']

end Monoid

section Group
variable [Group G] [MulAction G α] {g : G} {a b : α}

@[to_additive (attr := simp)]
/-
**inv_smul_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a := by rw [smul_smul, inv_mul_cancel, one_smul]

@[to_additive (attr := simp)]
/-
**smul_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel, one_smul]
/-
**inv_smul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_1 : MulAction G α] 
{g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
@[to_additive] lemma inv_smul_eq_iff : g⁻¹ • a = b ↔ a = g • b :=
  ⟨fun h ↦ by rw [← h, smul_inv_smul], fun h ↦ by rw [h, inv_smul_smul]⟩
/-
**eq_inv_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_1 : MulAction G α] 
{g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
@[to_additive] lemma eq_inv_smul_iff : a = g⁻¹ • b ↔ g • a = b :=
  ⟨fun h ↦ by rw [h, smul_inv_smul], fun h ↦ by rw [← h, inv_smul_smul]⟩

section Mul
variable [Mul H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H] {a b : H}

@[to_additive (attr := simp)]
/-
**SemiconjBy.smul_right_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.smul_right_iff {a b x : H} {r : G} : SemiconjBy x (r • a) (r • 
b) ↔ SemiconjBy x a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `SemiconjBy.smul_right`：SemiconjBy.smul_right [Mul α] [SMulCommClass M α 
α] [IsScalarTower M α α] {x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy
 x (r • a) …
-/
lemma SemiconjBy.smul_right_iff {a b x : H} {r : G} :
    SemiconjBy x (r • a) (r • b) ↔ SemiconjBy x a b :=
  ⟨fun h ↦ by simpa using h.smul_right r⁻¹, (smul_right · r)⟩

@[to_additive (attr := simp)]
/-
**SemiconjBy.smul_left_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.smul_left_iff {a b x : H} {r : G} : SemiconjBy (r • x) a b ↔ Se
miconjBy x a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `SemiconjBy.smul_left`：SemiconjBy.smul_left [Mul α] [SMulCommClass M α α]
 [IsScalarTower M α α] {x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy (
r • x) a b
-/
lemma SemiconjBy.smul_left_iff {a b x : H} {r : G} :
    SemiconjBy (r • x) a b ↔ SemiconjBy x a b :=
  ⟨fun h ↦ by simpa using h.smul_left r⁻¹, (smul_left · r)⟩

@[to_additive (attr := simp)]
/-
**Commute.smul_right_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.smul_right_iff : Commute a (g • b) ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.smul_right_iff`：SemiconjBy.smul_right_iff {a b x : H} {r : G}
 : SemiconjBy x (r • a) (r • b) ↔ SemiconjBy x a b
-/
lemma Commute.smul_right_iff : Commute a (g • b) ↔ Commute a b :=
  SemiconjBy.smul_right_iff

@[to_additive (attr := simp)]
/-
**Commute.smul_left_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.smul_left_iff : Commute (g • a) b ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.smul_left_iff`：SemiconjBy.smul_left_iff {a b x : H} {r : G} :
 SemiconjBy (r • x) a b ↔ SemiconjBy x a b
-/
lemma Commute.smul_left_iff : Commute (g • a) b ↔ Commute a b :=
  SemiconjBy.smul_left_iff

end Mul

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

/-
**smul_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹
参数：g : G；a : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹ :=
  inv_eq_of_mul_eq_one_right <| by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]
/-
**smul_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_zpow (g : G) (a : H) (n : Int) : (g • a) ^ n = g ^ n • a ^ n
参数：g : G；a : H；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用引理 `smul_inv`：smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹
-/
lemma smul_zpow (g : G) (a : H) (n : ℤ) : (g • a) ^ n = g ^ n • a ^ n := by
  cases n <;> simp [smul_pow, smul_inv]

end Group
end

/-
**SMulCommClass.of_commMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulCommClass.of_commMonoid (A B G : Type*) [CommMonoid G] [SMul A G] [SMu
l B G] [IsScalarTower A G G] [IsScalarTower B G G] : SMulCommClass A B G where s
mul_comm r s x
参数：A B G : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
lemma SMulCommClass.of_commMonoid
    (A B G : Type*) [CommMonoid G] [SMul A G] [SMul B G]
    [IsScalarTower A G G] [IsScalarTower B G G] :
    SMulCommClass A B G where
  smul_comm r s x := by
    rw [← one_smul G (s • x), ← smul_assoc, ← one_smul G x, ← smul_assoc s 1 x,
      smul_comm, smul_assoc, one_smul, smul_assoc, one_smul]
/-
**IsScalarTower.of_commMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsScalarTower.of_commMonoid (R₁ R : Type*) [Monoid R₁] [CommMonoid R] [Mul
Action R₁ R] [SMulCommClass R₁ R R] : IsScalarTower R₁ R R where smul_assoc x₁ y
 z
参数：R₁ R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma IsScalarTower.of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] [SMulCommClass R₁ R R] : IsScalarTower R₁ R R where
  smul_assoc x₁ y z := by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]
/-
**isScalarTower_iff_smulCommClass_of_commMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isScalarTower_iff_smulCommClass_of_commMonoid (R₁ R : Type*) [Monoid R₁] [
CommMonoid R] [MulAction R₁ R] : SMulCommClass R₁ R R ↔ IsScalarTower R₁ R R
参数：R₁ R : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.of_commMonoid`：IsScalarTower.of_commMonoid (R₁ R : Type*) 
[Monoid R₁] [CommMonoid R] [MulAction R₁ R] [SMulCommClass R₁ R R] : IsScalarTow
er R₁ R R where s…
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
-/
lemma isScalarTower_iff_smulCommClass_of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] :
    SMulCommClass R₁ R R ↔ IsScalarTower R₁ R R :=
  ⟨fun _ ↦ IsScalarTower.of_commMonoid R₁ R, fun _ ↦ SMulCommClass.of_commMonoid R₁ R R⟩

end

section CompatibleScalar

@[to_additive]
/-
**smul_one_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [Is
ScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
参数：N；x : M；y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N α] [SMul M α]
    [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]

@[to_additive (attr := simp)]
/-
**smul_one_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M
) (y : N) : x • (1 : N) * y = x • y
参数：x : M；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTower M N N] (x : M) (y : N) :
    x • (1 : N) * y = x • y := by rw [smul_mul_assoc, one_mul]

@[to_additive (attr := simp)]
/-
**mul_smul_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M
) (y : N) : y * x • (1 : N) = x • y
参数：x : M；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

@[to_additive]
/-
**IsScalarTower.of_smul_one_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N] (h : forall (x :
 M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N
参数：h : forall (x : M) (y : N), x • (1 : N) * y = x • y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N :=
  ⟨fun x y z ↦ by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive]
/-
**SMulCommClass.of_mul_smul_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N] (H : forall (x :
 M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N
参数：H : forall (x : M) (y : N), y * x • (1 : N) = x • y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N :=
  ⟨fun x y z ↦ by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

/--
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / P / M` and `Q / P / N` are
scalar towers, then `Q / N / M` is also a scalar tower.
-/
/-
**IsScalarTower.to** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / P / M` and `Q / P / N` are
scalar towers, then `Q / N / M` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₁₂₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul N P] [SMul N Q] [Monoid P] [MulAction P Q]
    [IsScalarTower M N P] [IsScalarTower M P Q] [IsScalarTower N P Q] : IsScalarTower M N Q where
  smul_assoc m n q := by rw [← smul_one_smul P, smul_assoc m, smul_assoc, smul_one_smul]

/--
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / N / M` and `Q / P / N` are
scalar towers, then `Q / P / M` is also a scalar tower.
-/
/-
**IsScalarTower.to** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / N / M` and `Q / P / N` are
scalar towers, then `Q / P / M` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₁₃₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul P Q] [Monoid N] [MulAction N P] [MulAction N Q]
    [IsScalarTower M N P] [IsScalarTower M N Q] [IsScalarTower N P Q] : IsScalarTower M P Q where
  smul_assoc m p q := by rw [← smul_one_smul N m, smul_assoc, smul_one_smul]

/--
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / N / M` and `Q / P / M` are
scalar towers, then `Q / P / N` is also a scalar tower.
-/
/-
**IsScalarTower.to** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `Q / P / N / M` be a tower. If `P / N / M`, `Q / N / M` and `Q / P / M` are
scalar towers, then `Q / P / N` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₂₃₄ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul P Q] [Monoid N] [MulAction N P] [MulAction N Q]
    [IsScalarTower M N P] [IsScalarTower M N Q] [IsScalarTower M P Q]
    (h : Function.Surjective fun m : M ↦ m • (1 : N)) : IsScalarTower N P Q where
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
/-
**MulDistribMulAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → [Monoid M] → [Monoid N] → Type (max u_1
0 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for multiplicative actions on multiplicative structures.

The key axiom here is `smul_mul : g • (x * y) = (g • x) * (g • y)`.
If `G` is a multiplicative group with automorphism group `Γ`, then there is a na
tural instance of
`MulDistribMulAction Γ G`.

The axiom is also satisfied by a Galois group $Gal(L/K)$ acting on the field `L`
,
but here you can use the even stronger class `MulSemiringAction`, which captures
how the action plays with both multiplication and addition.
-/
class MulDistribMulAction (M N : Type*) [Monoid M] [Monoid N] extends MulAction M N where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ r : M, r • (1 : N) = 1
  /-- Distributivity of `•` across `*` -/
  smul_mul : ∀ (r : M) (x y : N), r • (x * y) = r • x * r • y

/-- Typeclass for additive actions on additive structures.

The key axiom here is `vadd_add : g +ᵥ (x + y) = (g +ᵥ x) + (g +ᵥ y)`.
If `G` is an additive group with additive automorphism group `Γ`, then there is a natural instance
of `AddDistribAddAction Γ G`. -/
@[ext]
/-
**AddDistribAddAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → [AddMonoid M] → [AddMonoid N] → Type (m
ax u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for additive actions on additive structures.

The key axiom here is `vadd_add : g +ᵥ (x + y) = (g +ᵥ x) + (g +ᵥ y)`.
If `G` is an additive group with additive automorphism group `Γ`, then there is 
a natural instance
of `AddDistribAddAction Γ G`.
-/
class AddDistribAddAction (M N : Type*) [AddMonoid M] [AddMonoid N] extends AddAction M N where
  /-- Acting on `0` by a scalar gives `0` -/
  vadd_zero : ∀ r : M, r +ᵥ (0 : N) = 0
  /-- Distributivity of `+ᵥ` across `+` -/
  vadd_add : ∀ (r : M) (x y : N), r +ᵥ (x + y) = (r +ᵥ x) + (r +ᵥ y)

export MulDistribMulAction (smul_one)
export AddDistribAddAction (vadd_zero)

attribute [to_additive existing] MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

@[to_additive]
/-
**smul_mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • b₂
参数：a : M；b₁ b₂ : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulAction.smul_mul`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M)   (x y : N
), r • (x * y) = r…
-/
lemma smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul ..

end MulDistribMulAction

section IsCancelSMul

variable (G P : Type*)
-- TODO: IsRightCancelSmul

/-- A vector addition is left-cancellative if it is pointwise injective on the left. -/
/-
**IsLeftCancelVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → (P : Type u_10) → [VAdd G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector addition is left-cancellative if it is pointwise injective on the left.
-/
class IsLeftCancelVAdd [VAdd G P] : Prop where
  protected left_cancel' : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c

/-- A scalar multiplication is left-cancellative if it is pointwise injective on the left. -/
@[to_additive]
/-
**IsLeftCancelSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → (P : Type u_10) → [SMul G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scalar multiplication is left-cancellative if it is pointwise injective on the
 left.
-/
class IsLeftCancelSMul [SMul G P] : Prop where
  protected left_cancel' : ∀ (a : G) (b c : P), a • b = a • c → b = c

@[to_additive]
/-
**IsLeftCancelSMul.left_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftCancelSMul.left_cancel {G P} [SMul G P] [IsLeftCancelSMul G P] (a : 
G) (b c : P) : a • b = a • c -> b = c
参数：a : G；b c : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftCancelSMul.left_cancel'`：∀ {G : Type u_9} {P : Type u_10} {inst : 
SMul G P} [self : IsLeftCancelSMul G P] (a : G) (b c : P),   a • b = a • c → b =
 c
-/
lemma IsLeftCancelSMul.left_cancel {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul G] [IsLeftCancelMul G] : IsLeftCancelSMul G G where
  left_cancel' := IsLeftCancelMul.mul_left_cancel

/-- A vector addition is cancellative if it is pointwise injective on the left and right.

A group action is cancellative in this sense if and only if it is **free**.
See `isCancelVAdd_iff_eq_zero_of_vadd_eq` for a more familiar condition. -/
/-
**IsCancelVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → (P : Type u_10) → [VAdd G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector addition is cancellative if it is pointwise injective on the left and r
ight.

A group action is cancellative in this sense if and only if it is **free**.
See `isCancelVAdd_iff_eq_zero_of_vadd_eq` for a more familiar condition.
-/
class IsCancelVAdd [VAdd G P] : Prop extends IsLeftCancelVAdd G P where
  protected right_cancel' : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

/-- A scalar multiplication is cancellative if it is pointwise injective on the left and right.

A group action is cancellative in this sense if and only if it is **free**.
See `isCancelSMul_iff_eq_one_of_smul_eq` for a more familiar condition. -/
@[to_additive]
/-
**IsCancelSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_9) → (P : Type u_10) → [SMul G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scalar multiplication is cancellative if it is pointwise injective on the left
 and right.

A group action is cancellative in this sense if and only if it is **free**.
See `isCancelSMul_iff_eq_one_of_smul_eq` for a more familiar condition.
-/
class IsCancelSMul [SMul G P] : Prop extends IsLeftCancelSMul G P where
  protected right_cancel' : ∀ (a b : G) (c : P), a • c = b • c → a = b

@[to_additive]
/-
**IsCancelSMul.left_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCancelSMul.left_cancel {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c 
: P) : a • b = a • c -> b = c
参数：a : G；b c : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftCancelSMul.left_cancel'`：∀ {G : Type u_9} {P : Type u_10} {inst : 
SMul G P} [self : IsLeftCancelSMul G P] (a : G) (b c : P),   a • b = a • c → b =
 c
· 使用定理 `IsCancelSMul.toIsLeftCancelSMul`：∀ {G : Type u_9} {P : Type u_10} {inst 
: SMul G P} [self : IsCancelSMul G P], IsLeftCancelSMul G P
-/
lemma IsCancelSMul.left_cancel {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

@[to_additive]
/-
**IsCancelSMul.right_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCancelSMul.right_cancel {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c
 : P) : a • c = b • c -> a = b
参数：a b : G；c : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelSMul.right_cancel'`：∀ {G : Type u_9} {P : Type u_10} {inst : SMu
l G P} [self : IsCancelSMul G P] (a b : G) (c : P), a • c = b • c → a = b
-/
lemma IsCancelSMul.right_cancel {G P} [SMul G P] [IsCancelSMul G P] (a b : G) (c : P) :
    a • c = b • c → a = b := IsCancelSMul.right_cancel' a b c

@[to_additive]
/-
**IsCancelSMul.eq_one_of_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCancelSMul.eq_one_of_smul {G P} [Monoid G] [MulAction G P] [IsCancelSMul
 G P] {g : G} {x : P} (h : g • x = x) : g = 1
参数：h : g • x = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCancelSMul.right_cancel`：IsCancelSMul.right_cancel {G P} [SMul G P] [I
sCancelSMul G P] (a b : G) (c : P) : a • c = b • c -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma IsCancelSMul.eq_one_of_smul {G P} [Monoid G] [MulAction G P] [IsCancelSMul G P] {g : G}
    {x : P} (h : g • x = x) : g = 1 :=
  IsCancelSMul.right_cancel g 1 x ((one_smul G x).symm ▸ h)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelMonoid G] : IsCancelSMul G G where
  left_cancel' := IsLeftCancelMul.mul_left_cancel
  right_cancel' _ _ _ := mul_right_cancel

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] [MulAction G P] : IsLeftCancelSMul G P where
  left_cancel' a b c h := by rw [← inv_smul_smul a b, h, inv_smul_smul]

end IsCancelSMul

