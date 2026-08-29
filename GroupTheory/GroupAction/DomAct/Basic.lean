/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.GroupWithZero.Action.Hom
public import Mathlib.Algebra.Ring.Defs
public meta import Mathlib.Tactic.ToDual

/-!
# Type tags for right action on the domain of a function

By default, `M` acts on `α → β` if it acts on `β`, and the action is given by
`(c • f) a = c • (f a)`.

In some cases, it is useful to consider another action: if `M` acts on `α` on the left, then it acts
on `α → β` on the right so that `(c • f) a = f (c • a)`. E.g., this action is used to reformulate
the Mean Ergodic Theorem in terms of an operator on `L²`.

## Main definitions

- `DomMulAct M` (notation: `Mᵈᵐᵃ`): type synonym for `Mᵐᵒᵖ`; if `M` multiplicatively acts on `α`,
  then `Mᵈᵐᵃ` acts on `α → β` for any type `β`;
- `DomAddAct M` (notation: `Mᵈᵃᵃ`): the additive version.

We also define actions of `Mᵈᵐᵃ` on:

- `α → β` provided that `M` acts on `α`;
- `A →* B` provided that `M` acts on `A` by a `MulDistribMulAction`;
- `A →+ B` provided that `M` acts on `A` by a `DistribMulAction`.

## Implementation details

### Motivation

Right action can be represented in `mathlib` as an action of the opposite group `Mᵐᵒᵖ`. However,
this "domain shift" action cannot be an instance because this would create a "diamond"
(a.k.a. ambiguous notation): if `M` is a monoid, then how does `Mᵐᵒᵖ` act on `M → M`? On the one
hand, `Mᵐᵒᵖ` acts on `M` by `c • a = a * c.unop`, thus we have an action
`(c • f) a = f a * c.unop`. On the other hand, `M` acts on itself by multiplication on the left, so
with this new instance we would have `(c • f) a = f (c.unop * a)`. Clearly, these are two different
actions, so both of them cannot be instances in the library.

To overcome this difficulty, we introduce a type synonym `DomMulAct M := Mᵐᵒᵖ` (notation:
`Mᵈᵐᵃ`). This new type carries the same algebraic structures as `Mᵐᵒᵖ` but acts on `α → β` by this
new action. So, e.g., `Mᵈᵐᵃ` acts on `(M → M) → M` by `DomMulAct.mk c • F f = F (fun a ↦ c • f a)`
while `(Mᵈᵐᵃ)ᵈᵐᵃ` (which is isomorphic to `M`) acts on `(M → M) → M` by
`DomMulAct.mk (DomMulAct.mk c) • F f = F (fun a ↦ f (c • a))`.

### Action on bundled homomorphisms

If the action of `M` on `A` preserves some structure, then `Mᵈᵐᵃ` acts on bundled homomorphisms from
`A` to any type `B` that preserve the same structure. Examples (some of them are not yet in the
library) include:

- a `MulDistribMulAction` generates an action on `A →* B`;
- a `DistribMulAction` generates an action on `A →+ B`;
- an action on `α` that commutes with action of some other monoid `N` generates an action on
  `α →[N] β`;
- a `DistribMulAction` on an `R`-module that commutes with scalar multiplications by `c : R`
  generates an action on `R`-linear maps from this module;
- a continuous action on `X` generates an action on `C(X, Y)`;
- a measurable action on `X` generates an action on `{ f : X → Y // Measurable f }`;
- a quasi-measure-preserving action on `X` generates an action on `X →ₘ[μ] Y`;
- a measure-preserving action generates an isometric action on `MeasureTheory.Lp _ _ _`.

### Left action vs right action

It is common in the literature to consider the left action given by `(c • f) a = f (c⁻¹ • a)`
instead of the action defined in this file. However, this left action is defined only if `c` belongs
to a group, not to a monoid, so we decided to go with the right action.

The left action can be written in terms of `DomMulAct` as `(DomMulAct.mk c)⁻¹ • f`. As for higher
level dynamics objects (orbits, invariant functions etc), they coincide for the left and for the
right action, so lemmas can be formulated in terms of `DomMulAct`.

## Keywords

group action, function, domain
-/

@[expose] public section

open Function

/-- If `M` multiplicatively acts on `α`, then `DomMulAct M` acts on `α → β` as well as some
bundled maps from `α`. This is a type synonym for `MulOpposite M`, so this corresponds to a right
action of `M`. -/
@[to_additive /-- If `M` additively acts on `α`, then `DomAddAct M` acts on `α → β` as
well as some bundled maps from `α`. This is a type synonym for `AddOpposite M`, so this corresponds
to a right action of `M`. -/]
/--
Definition of `DomMulAct` / `DomMulAct` 的定义

English:
definition DomMulAct
  signature: (M : Type*)
  body: MulOpposite M

@[inherit_doc] postfix:max "ᵈᵐᵃ" => DomMulAct
@[inherit_doc] postfix:max "ᵈᵃᵃ" => DomAddAct

中文:
定义 DomMulAct
  签名: (M : 类型)
  定义体: MulOpposite M

@[inherit_doc] postfix:max "ᵈᵐᵃ" => DomMulAct
@[inherit_doc] postfix:max "ᵈᵃᵃ" => DomAddAct

Depends on / 依赖: MulOpposite
-/
def DomMulAct (M : Type*) := MulOpposite M

@[inherit_doc] postfix:max "ᵈᵐᵃ" => DomMulAct
@[inherit_doc] postfix:max "ᵈᵃᵃ" => DomAddAct

namespace DomMulAct

variable {M : Type*}

/-- Equivalence between `M` and `Mᵈᵐᵃ`. -/
@[to_additive /-- Equivalence between `M` and `Mᵈᵐᵃ`. -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : M ≃ Mᵈᵐᵃ
  body: MulOpposite.opEquiv

中文:
定义 mk
  签名: : M ≃ Mᵈᵐᵃ
  定义体: MulOpposite.opEquiv

Depends on / 依赖: MulOpposite, MulOpposite.opEquiv, opEquiv
-/
def mk : M ≃ Mᵈᵐᵃ := MulOpposite.opEquiv

/-!
### Copy instances from `Mᵐᵒᵖ`
-/

set_option hygiene false in
run_cmd
  for n in [`Mul, `One, `Inv, `Semigroup, `CommSemigroup, `LeftCancelSemigroup,
    `RightCancelSemigroup, `MulOneClass, `Monoid, `CommMonoid, `LeftCancelMonoid,
    `RightCancelMonoid, `CancelMonoid, `CancelCommMonoid, `InvolutiveInv, `DivInvMonoid,
    `InvOneClass, `DivInvOneMonoid, `DivisionMonoid, `DivisionCommMonoid, `Group,
    `CommGroup, `NonAssocSemiring, `NonUnitalSemiring, `Semiring,
    `Ring, `CommRing].map Lean.mkIdent do
  Lean.Elab.Command.elabCommand (← `(
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [$n
  signature: Mᵐᵒᵖ] : n Mᵈᵐᵃ
  body: ‹_›
  ))

中文:
实例 [$n
  签名: Mᵐᵒᵖ] : n Mᵈᵐᵃ
  定义体: ‹_›
  ))
-/
@[to_additive] instance [$n Mᵐᵒᵖ] : n Mᵈᵐᵃ := ‹_›
  ))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: Mᵐᵒᵖ] [IsLeftCancelMul Mᵐᵒᵖ] : IsLeftCancelMul Mᵈᵐᵃ
  body: ‹_›

中文:
实例 [Mul
  签名: Mᵐᵒᵖ] [IsLeftCancelMul Mᵐᵒᵖ] : IsLeftCancelMul Mᵈᵐᵃ
  定义体: ‹_›
-/
@[to_additive] instance [Mul Mᵐᵒᵖ] [IsLeftCancelMul Mᵐᵒᵖ] : IsLeftCancelMul Mᵈᵐᵃ := ‹_›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: Mᵐᵒᵖ] [IsRightCancelMul Mᵐᵒᵖ] : IsRightCancelMul Mᵈᵐᵃ
  body: ‹_›

中文:
实例 [Mul
  签名: Mᵐᵒᵖ] [IsRightCancelMul Mᵐᵒᵖ] : IsRightCancelMul Mᵈᵐᵃ
  定义体: ‹_›
-/
@[to_additive] instance [Mul Mᵐᵒᵖ] [IsRightCancelMul Mᵐᵒᵖ] : IsRightCancelMul Mᵈᵐᵃ := ‹_›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: Mᵐᵒᵖ] [IsCancelMul Mᵐᵒᵖ] : IsCancelMul Mᵈᵐᵃ
  body: ‹_›

@[to_additive (attr := simp)]

中文:
实例 [Mul
  签名: Mᵐᵒᵖ] [IsCancelMul Mᵐᵒᵖ] : IsCancelMul Mᵈᵐᵃ
  定义体: ‹_›

@[to_additive (attr := simp)]
-/
@[to_additive] instance [Mul Mᵐᵒᵖ] [IsCancelMul Mᵐᵒᵖ] : IsCancelMul Mᵈᵐᵃ := ‹_›

@[to_additive (attr := simp)]
/--
lemma `mk_one` / 引理 `mk_one`

English:
lemma mk_one
  given: [One M]
  statement: mk (1 : M) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mk_one
  条件: [One M]
  结论: mk (1 : M) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mk_one [One M] : mk (1 : M) = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mk_one` / 引理 `symm_mk_one`

English:
lemma symm_mk_one
  given: [One M]
  statement: mk.symm (1 : Mᵈᵐᵃ) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mk_one
  条件: [One M]
  结论: mk.symm (1 : Mᵈᵐᵃ) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mk_one [One M] : mk.symm (1 : Mᵈᵐᵃ) = 1 := rfl

@[to_additive (attr := simp)]
/--
lemma `mk_mul` / 引理 `mk_mul`

English:
lemma mk_mul
  given: [Mul M] (a b : M)
  statement: mk (a * b) = mk b * mk a
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mk_mul
  条件: [Mul M] (a b : M)
  结论: mk (a * b) = mk b * mk a
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mk_mul [Mul M] (a b : M) : mk (a * b) = mk b * mk a := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mk_mul` / 引理 `symm_mk_mul`

English:
lemma symm_mk_mul
  given: [Mul M] (a b : Mᵈᵐᵃ)
  statement: mk.symm (a * b) = mk.symm b * mk.symm a
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mk_mul
  条件: [Mul M] (a b : Mᵈᵐᵃ)
  结论: mk.symm (a * b) = mk.symm b * mk.symm a
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mk_mul [Mul M] (a b : Mᵈᵐᵃ) : mk.symm (a * b) = mk.symm b * mk.symm a := rfl

@[to_additive (attr := simp)]
/--
lemma `mk_inv` / 引理 `mk_inv`

English:
lemma mk_inv
  given: [Inv M] (a : M)
  statement: mk (a⁻¹) = (mk a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mk_inv
  条件: [Inv M] (a : M)
  结论: mk (a⁻¹) = (mk a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mk_inv [Inv M] (a : M) : mk (a⁻¹) = (mk a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mk_inv` / 引理 `symm_mk_inv`

English:
lemma symm_mk_inv
  given: [Inv M] (a : Mᵈᵐᵃ)
  statement: mk.symm (a⁻¹) = (mk.symm a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mk_inv
  条件: [Inv M] (a : Mᵈᵐᵃ)
  结论: mk.symm (a⁻¹) = (mk.symm a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mk_inv [Inv M] (a : Mᵈᵐᵃ) : mk.symm (a⁻¹) = (mk.symm a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `mk_pow` / 引理 `mk_pow`

English:
lemma mk_pow
  given: [Monoid M] (a : M) (n : Nat)
  statement: mk (a ^ n) = mk a ^ n
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mk_pow
  条件: [Monoid M] (a : M) (n : 自然数)
  结论: mk (a ^ n) = mk a ^ n
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mk_pow [Monoid M] (a : M) (n : Nat) : mk (a ^ n) = mk a ^ n := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mk_pow` / 引理 `symm_mk_pow`

English:
lemma symm_mk_pow
  given: [Monoid M] (a : Mᵈᵐᵃ) (n : Nat)
  statement: mk.symm (a ^ n) = mk.symm a ^ n
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_mk_pow
  条件: [Monoid M] (a : Mᵈᵐᵃ) (n : 自然数)
  结论: mk.symm (a ^ n) = mk.symm a ^ n
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_mk_pow [Monoid M] (a : Mᵈᵐᵃ) (n : Nat) : mk.symm (a ^ n) = mk.symm a ^ n := rfl

@[to_additive (attr := simp)]
/--
lemma `mk_zpow` / 引理 `mk_zpow`

English:
lemma mk_zpow
  given: [DivInvMonoid M] (a : M) (n : Int)
  statement: mk (a ^ n) = mk a ^ n
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mk_zpow
  条件: [DivInvMonoid M] (a : M) (n : 整数)
  结论: mk (a ^ n) = mk a ^ n
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mk_zpow [DivInvMonoid M] (a : M) (n : Int) : mk (a ^ n) = mk a ^ n := rfl

@[to_additive (attr := simp)]
/--
lemma `symm_mk_zpow` / 引理 `symm_mk_zpow`

English:
lemma symm_mk_zpow
  given: [DivInvMonoid M] (a : Mᵈᵐᵃ) (n : Int)
  statement: mk.symm (a ^ n) = mk.symm a ^ n
  proof: rfl

中文:
引理 symm_mk_zpow
  条件: [DivInvMonoid M] (a : Mᵈᵐᵃ) (n : 整数)
  结论: mk.symm (a ^ n) = mk.symm a ^ n
  证明: rfl
-/
lemma symm_mk_zpow [DivInvMonoid M] (a : Mᵈᵐᵃ) (n : Int) : mk.symm (a ^ n) = mk.symm a ^ n := rfl

variable {β α N : Type*}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] : SMul Mᵈᵐᵃ (α -> β) where
  body: f (mk.symm c • a)

@[to_additive]

中文:
实例 [SMul
  签名: M α] : SMul Mᵈᵐᵃ (α -> β) where
  定义体: f (mk.symm c • a)

@[to_additive]

Depends on / 依赖: mk.symm
-/
instance [SMul M α] : SMul Mᵈᵐᵃ (α -> β) where
  smul c f a := f (mk.symm c • a)

@[to_additive]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMul M α] (c : Mᵈᵐᵃ) (f : α -> β) (a : α)
  statement: (c • f) a = f (mk.symm c • a)
  proof: rfl

@[to_additive]

中文:
定理 smul_apply
  条件: [SMul M α] (c : Mᵈᵐᵃ) (f : α -> β) (a : α)
  结论: (c • f) a = f (mk.symm c • a)
  证明: rfl

@[to_additive]
-/
theorem smul_apply [SMul M α] (c : Mᵈᵐᵃ) (f : α -> β) (a : α) : (c • f) a = f (mk.symm c • a) := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [SMul N β] : SMulCommClass Mᵈᵐᵃ N (α -> β) where
  body: rfl

@[to_additive]

中文:
实例 [SMul
  签名: M α] [SMul N β] : SMulCommClass Mᵈᵐᵃ N (α -> β) where
  定义体: rfl

@[to_additive]
-/
instance [SMul M α] [SMul N β] : SMulCommClass Mᵈᵐᵃ N (α -> β) where
  smul_comm _ _ _ := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [SMul N β] : SMulCommClass N Mᵈᵐᵃ (α -> β) where
  body: rfl

@[to_additive]

中文:
实例 [SMul
  签名: M α] [SMul N β] : SMulCommClass N Mᵈᵐᵃ (α -> β) where
  定义体: rfl

@[to_additive]
-/
instance [SMul M α] [SMul N β] : SMulCommClass N Mᵈᵐᵃ (α -> β) where
  smul_comm _ _ _ := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α -> β) where
  body: funext fun _ => congr_arg f (smul_comm _ _ _).symm

@[to_additive]

中文:
实例 [SMul
  签名: M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α -> β) where
  定义体: funext fun _ => congr_arg f (smul_comm _ _ _).symm

@[to_additive]

Depends on / 依赖: congr_arg, smul_comm
-/
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α -> β) where
  smul_comm _ _ f := funext fun _ => congr_arg f (smul_comm _ _ _).symm

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [FaithfulSMul M α] [Nontrivial β] : FaithfulSMul Mᵈᵐᵃ (α -> β) where
  body: mk.symm.injective eq_of_smul_eq_smul fun a : α => by
    rcases exists_pair_ne β with ⟨x, y, hne⟩
    contrapose! hne
    have := Classical.decEq α
    replace h := congr_fun (h (update (const α x) (mk.symm c₂ • a) y)) a
    simpa [smul_apply, hne] using h

中文:
实例 [SMul
  签名: M α] [FaithfulSMul M α] [Nontrivial β] : FaithfulSMul Mᵈᵐᵃ (α -> β) where
  定义体: mk.symm.injective eq_of_smul_eq_smul fun a : α => by
    rcases exists_pair_ne β with ⟨x, y, hne⟩
    contrapose! hne
    have := Classical.decEq α
    replace h := congr_fun (h (update (const α x) (mk.symm c₂ • a) y)) a
    simpa [smul_apply, hne] using h

Depends on / 依赖: Classical, Classical.decEq, congr_fun, contrapose, eq_of_smul_eq_smul, exists_pair_ne, injective, mk.symm, mk.symm.injective, replace, smul_apply, update
-/
instance [SMul M α] [FaithfulSMul M α] [Nontrivial β] : FaithfulSMul Mᵈᵐᵃ (α -> β) where
eq_of_smul_eq_smul {c₁ c₂} h := mk.symm.injective eq_of_smul_eq_smul fun a : α => by
    rcases exists_pair_ne β with ⟨x, y, hne⟩
    contrapose! hne
    have := Classical.decEq α
    replace h := congr_fun (h (update (const α x) (mk.symm c₂ • a) y)) a
    simpa [smul_apply, hne] using h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M α] [Zero β] : SMulZeroClass Mᵈᵐᵃ (α -> β) where
  body: rfl

中文:
实例 [SMul
  签名: M α] [Zero β] : SMulZeroClass Mᵈᵐᵃ (α -> β) where
  定义体: rfl
-/
instance [SMul M α] [Zero β] : SMulZeroClass Mᵈᵐᵃ (α -> β) where
  smul_zero _ := rfl

instance {A : Type*} [SMul M α] [AddZeroClass A] : DistribSMul Mᵈᵐᵃ (α -> A) where
  smul_add _ _ _ := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [MulAction M α] : MulAction Mᵈᵐᵃ (α -> β) where
  body: funext fun _ => congr_arg f (one_smul _ _)
  mul_smul _ _ f := funext fun _ => congr_arg f (mul_smul _ _ _)

中文:
实例 [Monoid
  签名: M] [MulAction M α] : MulAction Mᵈᵐᵃ (α -> β) where
  定义体: funext fun _ => congr_arg f (one_smul _ _)
  mul_smul _ _ f := funext fun _ => congr_arg f (mul_smul _ _ _)

Depends on / 依赖: congr_arg, one_smul
-/
instance [Monoid M] [MulAction M α] : MulAction Mᵈᵐᵃ (α -> β) where
  one_smul f := funext fun _ => congr_arg f (one_smul _ _)
  mul_smul _ _ f := funext fun _ => congr_arg f (mul_smul _ _ _)

instance {A : Type*} [Monoid M] [MulAction M α] [AddMonoid A] : DistribMulAction Mᵈᵐᵃ (α -> A) where
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance {A : Type*} [Monoid M] [MulAction M α] [Monoid A] : MulDistribMulAction Mᵈᵐᵃ (α -> A) where
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

section MonoidHom

variable {M M' A B : Type*} [Monoid M] [Monoid A] [MulDistribMulAction M A] [MulOneClass B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Mᵈᵐᵃ (A ->* B)
  body: f.comp (MulDistribMulAction.toMonoidHom _ (mk.symm c))

中文:
实例 :
  签名: SMul Mᵈᵐᵃ (A ->* B)
  定义体: f.comp (MulDistribMulAction.toMonoidHom _ (mk.symm c))

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, f.comp, mk.symm, toMonoidHom
-/
instance : SMul Mᵈᵐᵃ (A ->* B) where
  smul c f := f.comp (MulDistribMulAction.toMonoidHom _ (mk.symm c))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M'] [MulDistribMulAction M' A] [SMulCommClass M M' A] :
  body: DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [Monoid
  签名: M'] [MulDistribMulAction M' A] [SMulCommClass M M' A] :
  定义体: DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.smulCommClass, coe_injective, smulCommClass
-/
instance [Monoid M'] [MulDistribMulAction M' A] [SMulCommClass M M' A] :
    SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A ->* B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

/--
theorem `smul_monoidHom_apply` / 定理 `smul_monoidHom_apply`

English:
theorem smul_monoidHom_apply
  given: (c : Mᵈᵐᵃ) (f : A ->* B) (a : A)
  statement: (c • f) a = f (mk.symm c • a)
  proof: rfl

@[simp]

中文:
定理 smul_monoidHom_apply
  条件: (c : Mᵈᵐᵃ) (f : A ->* B) (a : A)
  结论: (c • f) a = f (mk.symm c • a)
  证明: rfl

@[simp]
-/
theorem smul_monoidHom_apply (c : Mᵈᵐᵃ) (f : A ->* B) (a : A) : (c • f) a = f (mk.symm c • a) :=
  rfl

@[simp]
/--
theorem `mk_smul_monoidHom_apply` / 定理 `mk_smul_monoidHom_apply`

English:
theorem mk_smul_monoidHom_apply
  given: (c : M) (f : A ->* B) (a : A)
  statement: (mk c • f) a = f (c • a)
  proof: rfl

中文:
定理 mk_smul_monoidHom_apply
  条件: (c : M) (f : A ->* B) (a : A)
  结论: (mk c • f) a = f (c • a)
  证明: rfl
-/
theorem mk_smul_monoidHom_apply (c : M) (f : A ->* B) (a : A) : (mk c • f) a = f (c • a) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Mᵈᵐᵃ (A ->* B)
  body: DFunLike.coe_injective.mulAction (⇑) fun _ _ => rfl

中文:
实例 :
  签名: MulAction Mᵈᵐᵃ (A ->* B)
  定义体: DFunLike.coe_injective.mulAction (⇑) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulAction, coe_injective, mulAction
-/
instance : MulAction Mᵈᵐᵃ (A ->* B) := DFunLike.coe_injective.mulAction (⇑) fun _ _ => rfl

end MonoidHom

section AddMonoidHom

section DistribSMul

variable {A B M M' : Type*} [AddMonoid A] [DistribSMul M A] [AddZeroClass B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Mᵈᵐᵃ (A ->+ B)
  body: f.comp (DistribSMul.toAddMonoidHom _ (mk.symm c))

中文:
实例 :
  签名: SMul Mᵈᵐᵃ (A ->+ B)
  定义体: f.comp (DistribSMul.toAddMonoidHom _ (mk.symm c))

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, f.comp, mk.symm, toAddMonoidHom
-/
instance : SMul Mᵈᵐᵃ (A ->+ B) where
  smul c f := f.comp (DistribSMul.toAddMonoidHom _ (mk.symm c))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: M' A] [SMulCommClass M M' A] : SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A ->+ B)
  body: DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [DistribSMul
  签名: M' A] [SMulCommClass M M' A] : SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A ->+ B)
  定义体: DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.smulCommClass, coe_injective, smulCommClass
-/
instance [DistribSMul M' A] [SMulCommClass M M' A] : SMulCommClass Mᵈᵐᵃ M'ᵈᵐᵃ (A ->+ B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: M' B] : SMulCommClass Mᵈᵐᵃ M' (A ->+ B)
  body: DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [DistribSMul
  签名: M' B] : SMulCommClass Mᵈᵐᵃ M' (A ->+ B)
  定义体: DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.smulCommClass, coe_injective, smulCommClass
-/
instance [DistribSMul M' B] : SMulCommClass Mᵈᵐᵃ M' (A ->+ B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ => rfl) (fun _ _ => rfl)

/--
theorem `smul_addMonoidHom_apply` / 定理 `smul_addMonoidHom_apply`

English:
theorem smul_addMonoidHom_apply
  given: (c : Mᵈᵐᵃ) (f : A ->+ B) (a : A)
  statement: (c • f) a = f (mk.symm c • a)
  proof: rfl

@[simp]

中文:
定理 smul_addMonoidHom_apply
  条件: (c : Mᵈᵐᵃ) (f : A ->+ B) (a : A)
  结论: (c • f) a = f (mk.symm c • a)
  证明: rfl

@[simp]
-/
theorem smul_addMonoidHom_apply (c : Mᵈᵐᵃ) (f : A ->+ B) (a : A) : (c • f) a = f (mk.symm c • a) :=
  rfl

@[simp]
/--
theorem `mk_smul_addMonoidHom_apply` / 定理 `mk_smul_addMonoidHom_apply`

English:
theorem mk_smul_addMonoidHom_apply
  given: (c : M) (f : A ->+ B) (a : A)
  statement: (mk c • f) a = f (c • a)
  proof: rfl

中文:
定理 mk_smul_addMonoidHom_apply
  条件: (c : M) (f : A ->+ B) (a : A)
  结论: (mk c • f) a = f (c • a)
  证明: rfl
-/
theorem mk_smul_addMonoidHom_apply (c : M) (f : A ->+ B) (a : A) : (mk c • f) a = f (c • a) := rfl

/--
theorem `coe_smul_addMonoidHom` / 定理 `coe_smul_addMonoidHom`

English:
theorem coe_smul_addMonoidHom
  given: (c : Mᵈᵐᵃ) (f : A ->+ B)
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

中文:
定理 coe_smul_addMonoidHom
  条件: (c : Mᵈᵐᵃ) (f : A ->+ B)
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl
-/
theorem coe_smul_addMonoidHom (c : Mᵈᵐᵃ) (f : A ->+ B) : ⇑(c • f) = c • ⇑f :=
  rfl

end DistribSMul

variable {A M B : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [AddMonoid A] [DistribMulAction M A] [AddZeroClass B] :
  body: DFunLike.coe_injective.mulAction (⇑) fun _ _ => rfl

中文:
实例 [Monoid
  签名: M] [AddMonoid A] [DistribMulAction M A] [AddZeroClass B] :
  定义体: DFunLike.coe_injective.mulAction (⇑) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulAction, coe_injective, mulAction
-/
instance [Monoid M] [AddMonoid A] [DistribMulAction M A] [AddZeroClass B] :
    MulAction Mᵈᵐᵃ (A ->+ B) := DFunLike.coe_injective.mulAction (⇑) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [AddMonoid A] [DistribMulAction M A] [AddCommMonoid B] :
  body: DFunLike.coe_injective.distribMulAction (AddMonoidHom.coeFn A B) fun _ _ => rfl

中文:
实例 [Monoid
  签名: M] [AddMonoid A] [DistribMulAction M A] [AddCommMonoid B] :
  定义体: DFunLike.coe_injective.distribMulAction (AddMonoidHom.coeFn A B) fun _ _ => rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coeFn, DFunLike, DFunLike.coe_injective.distribMulAction, coe_injective, distribMulAction
-/
instance [Monoid M] [AddMonoid A] [DistribMulAction M A] [AddCommMonoid B] :
    DistribMulAction Mᵈᵐᵃ (A ->+ B) :=
  DFunLike.coe_injective.distribMulAction (AddMonoidHom.coeFn A B) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [Monoid A] [MulDistribMulAction M A] [CommMonoid B] :
  body: DFunLike.coe_injective.mulDistribMulAction (MonoidHom.coeFn A B) fun _ _ => rfl

中文:
实例 [Monoid
  签名: M] [Monoid A] [MulDistribMulAction M A] [CommMonoid B] :
  定义体: DFunLike.coe_injective.mulDistribMulAction (MonoidHom.coeFn A B) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulDistribMulAction, MonoidHom, MonoidHom.coeFn, coe_injective, mulDistribMulAction
-/
instance [Monoid M] [Monoid A] [MulDistribMulAction M A] [CommMonoid B] :
    MulDistribMulAction Mᵈᵐᵃ (A ->* B) :=
  DFunLike.coe_injective.mulDistribMulAction (MonoidHom.coeFn A B) fun _ _ => rfl

end AddMonoidHom

end DomMulAct
