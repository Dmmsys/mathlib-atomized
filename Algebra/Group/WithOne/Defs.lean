/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Option.Basic
public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Tactic.Common

/-!
# Adjoining a zero/one to semigroups and related algebraic structures

This file contains different results about adjoining an element to an algebraic structure which then
behaves like a zero or a one. An example is adjoining a one to a semigroup to obtain a monoid. That
this provides an example of an adjunction is proved in
`Mathlib/Algebra/Category/MonCat/Adjunctions.lean`.

Another result says that adjoining to a group an element `zero` gives a `GroupWithZero`. For more
information about these structures (which are not that standard in informal mathematics, see
`Mathlib/Algebra/GroupWithZero/Basic.lean`)

## TODO

`WithOne.coe_mul` and `WithZero.coe_mul` have inconsistent use of implicit parameters
-/

@[expose] public section

-- Check that we haven't needed to import all the basic lemmas about groups,
-- by asserting a random sample don't exist here:
assert_not_exists inv_involutive div_right_inj pow_ite MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u}

/-- Add an extra element `1` to a type -/
@[to_additive /-- Add an extra element `0` to a type -/]
/--
Definition of `WithOne` / `WithOne` 的定义

English:
definition WithOne
  signature: (α)
  body: Option α

中文:
定义 WithOne
  签名: (α)
  定义体: Option α
-/
def WithOne (α) :=
  Option α

/--
Instance `WithZero.instRepr` / 实例 `WithZero.instRepr`

English:
instance WithZero.instRepr
  signature: [Repr α]
  body: ⟨fun o _ =>
    match o with
    | none => "0"
    | some a => "↑" ++ repr a⟩

中文:
实例 WithZero.instRepr
  签名: [Repr α]
  定义体: ⟨fun o _ =>
    match o with
    | none => "0"
    | some a => "↑" ++ repr a⟩
-/
instance WithZero.instRepr [Repr α] : Repr (WithZero α) :=
  ⟨fun o _ =>
    match o with
    | none => "0"
    | some a => "↑" ++ repr a⟩

namespace WithOne

@[to_additive existing]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Repr
  signature: α] : Repr (WithOne α)
  body: ⟨fun o _ =>
    match o with
    | none => "1"
    | some a => "↑" ++ repr a⟩

@[to_additive]

中文:
实例 [Repr
  签名: α] : Repr (WithOne α)
  定义体: ⟨fun o _ =>
    match o with
    | none => "1"
    | some a => "↑" ++ repr a⟩

@[to_additive]
-/
instance [Repr α] : Repr (WithOne α) :=
  ⟨fun o _ =>
    match o with
    | none => "1"
    | some a => "↑" ++ repr a⟩

@[to_additive]
/--
Instance `instMonad` / 实例 `instMonad`

English:
instance instMonad
  signature: : Monad WithOne
  body: inferInstanceAs Monad Option

@[to_additive]

中文:
实例 instMonad
  签名: : 单子 WithOne
  定义体: inferInstanceAs Monad Option

@[to_additive]
-/
instance instMonad : Monad WithOne :=
inferInstanceAs Monad Option

@[to_additive]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (WithOne α)
  body: ⟨none⟩

@[to_additive]

中文:
实例 instOne
  签名: : 幺 (WithOne α)
  定义体: ⟨none⟩

@[to_additive]
-/
instance instOne : One (WithOne α) :=
  ⟨none⟩

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul α]
  body: ⟨Option.merge (· * ·)⟩

@[to_additive]

中文:
实例 instMul
  签名: [乘法 α]
  定义体: ⟨Option.merge (· * ·)⟩

@[to_additive]

Depends on / 依赖: Option.merge
-/
instance instMul [Mul α] : Mul (WithOne α) :=
  ⟨Option.merge (· * ·)⟩

@[to_additive]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: [Inv α]
  body: ⟨fun a => Option.map Inv.inv a⟩

@[to_additive]

中文:
实例 instInv
  签名: [取逆 α]
  定义体: ⟨fun a => Option.map Inv.inv a⟩

@[to_additive]

Depends on / 依赖: Inv.inv, Option.map
-/
instance instInv [Inv α] : Inv (WithOne α) :=
  ⟨fun a => Option.map Inv.inv a⟩

@[to_additive]
/--
Instance `instInvOneClass` / 实例 `instInvOneClass`

English:
instance instInvOneClass
  signature: [Inv α]
  body: { WithOne.instOne, WithOne.instInv with inv_one := rfl }

@[to_additive]

中文:
实例 instInvOneClass
  签名: [取逆 α]
  定义体: { WithOne.instOne, WithOne.instInv with inv_one := rfl }

@[to_additive]

Depends on / 依赖: WithOne, WithOne.instInv, WithOne.instOne, instInv, instOne, inv_one
-/
instance instInvOneClass [Inv α] : InvOneClass (WithOne α) :=
  { WithOne.instOne, WithOne.instInv with inv_one := rfl }

@[to_additive]
/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (WithOne α)
  body: ⟨1⟩

@[to_additive]

中文:
实例 inhabited
  签名: : 可居 (WithOne α)
  定义体: ⟨1⟩

@[to_additive]

Depends on / 依赖: CommGroupWithZero, CommGroupWithZero.toDivisionCommMonoid, toDivisionCommMonoid
-/
instance inhabited : Inhabited (WithOne α) :=
  ⟨1⟩

@[to_additive]
/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nonempty α]
  body: Option.nontrivial

@[to_additive]

中文:
实例 instNontrivial
  签名: [非空 α]
  定义体: Option.nontrivial

@[to_additive]

Depends on / 依赖: Option.nontrivial, nontrivial
-/
instance instNontrivial [Nonempty α] : Nontrivial (WithOne α) :=
  Option.nontrivial

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Subsingleton (WithOne α)
  body: inferInstanceAs Subsingleton (Option α)

中文:
实例 [是空
  签名: α] : 子单例 (WithOne α)
  定义体: inferInstanceAs Subsingleton (Option α)

Depends on / 依赖: Subsingleton
-/
instance [IsEmpty α] : Subsingleton (WithOne α) :=
inferInstanceAs Subsingleton (Option α)

/-- The canonical map from `α` into `WithOne α` -/
@[to_additive (attr := coe, match_pattern) /-- The canonical map from `α` into `WithZero α` -/]
/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: : α -> WithOne α
  body: Option.some

@[to_additive]

中文:
定义 coe
  签名: : α -> WithOne α
  定义体: Option.some

@[to_additive]

Depends on / 依赖: Option.some
-/
def coe : α -> WithOne α :=
  Option.some

@[to_additive]
/--
Instance `instCoeTC` / 实例 `instCoeTC`

English:
instance instCoeTC
  signature: : CoeTC α (WithOne α)
  body: ⟨coe⟩

@[to_additive]

中文:
实例 instCoeTC
  签名: : CoeTC α (WithOne α)
  定义体: ⟨coe⟩

@[to_additive]
-/
instance instCoeTC : CoeTC α (WithOne α) :=
  ⟨coe⟩

@[to_additive]
/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : WithOne α -> Prop}
  statement: (forall x, p x) ↔ p 1 ∧ forall a : α, p a
  proof: Option.forall

@[to_additive]

中文:
引理 «对任意»
  条件: {p : WithOne α -> 命题}
  结论: (对任意 x, p x) ↔ p 1 ∧ 对任意 a : α, p a
  证明: Option.forall

@[to_additive]
-/
lemma «forall» {p : WithOne α -> Prop} : (forall x, p x) ↔ p 1 ∧ forall a : α, p a := Option.forall

@[to_additive]
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : WithOne α -> Prop}
  statement: (exists x, p x) ↔ p 1 ∨ exists a : α, p a
  proof: Option.exists

中文:
引理 «存在»
  条件: {p : WithOne α -> 命题}
  结论: (存在 x, p x) ↔ p 1 ∨ 存在 a : α, p a
  证明: Option.exists
-/
lemma «exists» {p : WithOne α -> Prop} : (exists x, p x) ↔ p 1 ∨ exists a : α, p a := Option.exists

/-- Recursor for `WithZero` using the preferred forms `0` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `_root_.WithZero.recZeroCoe` / `_root_.WithZero.recZeroCoe` 的定义

English:
definition _root_.WithZero.recZeroCoe
  signature: {motive : WithZero α -> Sort*} (zero : motive 0)

中文:
定义 _root_.WithZero.recZeroCoe
  签名: {motive : WithZero α -> 类型层*} (zero : motive 0)
-/
def _root_.WithZero.recZeroCoe {motive : WithZero α -> Sort*} (zero : motive 0)
    (coe : forall a : α, motive a) : forall n : WithZero α, motive n
  | Option.none => zero
  | Option.some x => coe x

/-- Recursor for `WithOne` using the preferred forms `1` and `↑a`. -/
@[to_additive existing, elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `recOneCoe` / `recOneCoe` 的定义

English:
definition recOneCoe
  signature: {motive : WithOne α -> Sort*} (one : motive 1) (coe : forall a : α, motive a)

中文:
定义 recOneCoe
  签名: {motive : WithOne α -> 类型层*} (one : motive 1) (coe : 对任意 a : α, motive a)
-/
def recOneCoe {motive : WithOne α -> Sort*} (one : motive 1) (coe : forall a : α, motive a) :
    forall n : WithOne α, motive n
  | Option.none => one
  | Option.some x => coe x

@[to_additive (attr := simp)]
/--
lemma `recOneCoe_one` / 引理 `recOneCoe_one`

English:
lemma recOneCoe_one
  given: {motive : WithOne α -> Sort*} (h₁ h₂)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 recOneCoe_one
  条件: {motive : WithOne α -> 类型层*} (h₁ h₂)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma recOneCoe_one {motive : WithOne α -> Sort*} (h₁ h₂) :
    recOneCoe h₁ h₂ (1 : WithOne α) = (h₁ : motive 1) :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `recOneCoe_coe` / 引理 `recOneCoe_coe`

English:
lemma recOneCoe_coe
  given: {motive : WithOne α -> Sort*} (h₁ h₂) (a : α)
  proof: rfl

中文:
引理 recOneCoe_coe
  条件: {motive : WithOne α -> 类型层*} (h₁ h₂) (a : α)
  证明: rfl
-/
lemma recOneCoe_coe {motive : WithOne α -> Sort*} (h₁ h₂) (a : α) :
    recOneCoe h₁ h₂ (a : WithOne α) = (h₂ : forall a : α, motive a) a :=
  rfl

/-- Deconstruct an `x : WithOne α` to the underlying value in `α`, given a proof that `x ≠ 1`. -/
@[to_additive
/-- Deconstruct an `x : WithZero α` to the underlying value in `α`, given a proof that `x ≠ 0`. -/]
/--
Definition of `unone` / `unone` 的定义

English:
definition unone
  signature: : forall {x : WithOne α}, x != 1 -> α | (x : α), _ => x

中文:
定义 unone
  签名: : 对任意 {x : WithOne α}, x != 1 -> α | (x : α), _ => x
-/
def unone : forall {x : WithOne α}, x != 1 -> α | (x : α), _ => x

@[to_additive (attr := simp)]
/--
theorem `unone_coe` / 定理 `unone_coe`

English:
theorem unone_coe
  given: {x : α} (hx : (x : WithOne α) != 1)
  statement: unone hx = x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unone_coe
  条件: {x : α} (hx : (x : WithOne α) != 1)
  结论: unone hx = x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unone_coe {x : α} (hx : (x : WithOne α) != 1) : unone hx = x :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `coe_unone` / 引理 `coe_unone`

English:
lemma coe_unone
  statement: forall {x : WithOne α} (hx : x != 1), unone hx = x

中文:
引理 coe_unone
  结论: 对任意 {x : WithOne α} (hx : x != 1), unone hx = x
-/
lemma coe_unone : forall {x : WithOne α} (hx : x != 1), unone hx = x
  | (x : α), _ => rfl

@[to_additive (attr := simp)]
/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: {a : α}
  statement: (a : WithOne α) != (1 : WithOne α)
  proof: Option.some_ne_none a

@[to_additive (attr := simp)]

中文:
定理 coe_ne_one
  条件: {a : α}
  结论: (a : WithOne α) != (1 : WithOne α)
  证明: Option.some_ne_none a

@[to_additive (attr := simp)]

Depends on / 依赖: Option.some_ne_none, some_ne_none
-/
theorem coe_ne_one {a : α} : (a : WithOne α) != (1 : WithOne α) :=
  Option.some_ne_none a

@[to_additive (attr := simp)]
/--
theorem `one_ne_coe` / 定理 `one_ne_coe`

English:
theorem one_ne_coe
  given: {a : α}
  statement: (1 : WithOne α) != a
  proof: coe_ne_one.symm

@[to_additive]

中文:
定理 one_ne_coe
  条件: {a : α}
  结论: (1 : WithOne α) != a
  证明: coe_ne_one.symm

@[to_additive]

Depends on / 依赖: coe_ne_one, coe_ne_one.symm
-/
theorem one_ne_coe {a : α} : (1 : WithOne α) != a :=
  coe_ne_one.symm

@[to_additive]
/--
theorem `ne_one_iff_exists` / 定理 `ne_one_iff_exists`

English:
theorem ne_one_iff_exists
  given: {x : WithOne α}
  statement: x != 1 ↔ exists a : α, ↑a = x
  proof: Option.ne_none_iff_exists

@[to_additive]

中文:
定理 ne_one_iff_存在
  条件: {x : WithOne α}
  结论: x != 1 ↔ 存在 a : α, ↑a = x
  证明: Option.ne_none_iff_exists

@[to_additive]

Depends on / 依赖: Option.ne_none_iff_exists, ne_none_iff_exists
-/
theorem ne_one_iff_exists {x : WithOne α} : x != 1 ↔ exists a : α, ↑a = x :=
  Option.ne_none_iff_exists

@[to_additive]
/--
Instance `instCanLift` / 实例 `instCanLift`

English:
instance instCanLift
  signature: : CanLift (WithOne α) α (↑) fun a => a != 1 where
  body: ne_one_iff_exists.1

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instCanLift
  签名: : CanLift (WithOne α) α (↑) fun a => a != 1 where
  定义体: ne_one_iff_exists.1

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: ne_one_iff_exists
-/
instance instCanLift : CanLift (WithOne α) α (↑) fun a => a != 1 where
  prf _ := ne_one_iff_exists.1

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {a b : α}
  statement: (a : WithOne α) = b ↔ a = b
  proof: Option.some_inj

@[to_additive]

中文:
定理 coe_inj
  条件: {a b : α}
  结论: (a : WithOne α) = b ↔ a = b
  证明: Option.some_inj

@[to_additive]

Depends on / 依赖: Option.some_inj, some_inj
-/
theorem coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b :=
  Option.some_inj

@[to_additive]
/--
lemma `coe_injective` / 引理 `coe_injective`

English:
lemma coe_injective
  statement: Function.Injective (coe : α -> WithOne α)
  proof: Option.some_injective _

@[to_additive (attr := elab_as_elim)]

中文:
引理 coe_injective
  结论: 函数.单射 (coe : α -> WithOne α)
  证明: Option.some_injective _

@[to_additive (attr := elab_as_elim)]

Depends on / 依赖: Option.some_injective, some_injective
-/
lemma coe_injective : Function.Injective (coe : α -> WithOne α) :=
  Option.some_injective _

@[to_additive (attr := elab_as_elim)]
/--
theorem `cases_on` / 定理 `cases_on`

English:
theorem cases_on
  given: {P : WithOne α -> Prop}
  statement: forall x : WithOne α, P 1 -> (forall a : α, P a) -> P x
  proof: Option.casesOn

@[to_additive]

中文:
定理 cases_on
  条件: {P : WithOne α -> 命题}
  结论: 对任意 x : WithOne α, P 1 -> (对任意 a : α, P a) -> P x
  证明: Option.casesOn

@[to_additive]
-/
protected theorem cases_on {P : WithOne α -> Prop} : forall x : WithOne α, P 1 -> (forall a : α, P a) -> P x :=
  Option.casesOn

@[to_additive]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [Mul α]
  body: (Option.lawfulIdentity_merge _).left_id
  mul_one := (Option.lawfulIdentity_merge _).right_id

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instMulOneClass
  签名: [乘法 α]
  定义体: (Option.lawfulIdentity_merge _).left_id
  mul_one := (Option.lawfulIdentity_merge _).right_id

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Option.lawfulIdentity_merge, lawfulIdentity_merge, left_id
-/
instance instMulOneClass [Mul α] : MulOneClass (WithOne α) where
  one_mul := (Option.lawfulIdentity_merge _).left_id
  mul_one := (Option.lawfulIdentity_merge _).right_id

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: [Mul α] (a b : α)
  statement: (↑(a * b) : WithOne α) = a * b
  proof: rfl

@[to_additive]

中文:
引理 coe_mul
  条件: [乘法 α] (a b : α)
  结论: (↑(a * b) : WithOne α) = a * b
  证明: rfl

@[to_additive]
-/
lemma coe_mul [Mul α] (a b : α) : (↑(a * b) : WithOne α) = a * b := rfl

@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Semigroup α]
  body: instMulOneClass
  mul_assoc
    | 1, b, c => by simp
    | (a : α), 1, c => by simp
    | (a : α), (b : α), 1 => by simp
    | (a : α), (b : α), (c : α) => by simp_rw [← coe_mul, mul_assoc]

@[to_additive]

中文:
实例 instMonoid
  签名: [半群 α]
  定义体: instMulOneClass
  mul_assoc
    | 1, b, c => by simp
    | (a : α), 1, c => by simp
    | (a : α), (b : α), 1 => by simp
    | (a : α), (b : α), (c : α) => by simp_rw [← coe_mul, mul_assoc]

@[to_additive]

Depends on / 依赖: instMulOneClass
-/
instance instMonoid [Semigroup α] : Monoid (WithOne α) where
  __ := instMulOneClass
  mul_assoc
    | 1, b, c => by simp
    | (a : α), 1, c => by simp
    | (a : α), (b : α), 1 => by simp
    | (a : α), (b : α), (c : α) => by simp_rw [← coe_mul, mul_assoc]

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommSemigroup α]

中文:
实例 instCommMonoid
  签名: [交换半群 α]
-/
instance instCommMonoid [CommSemigroup α] : CommMonoid (WithOne α) where
  mul_comm
    | (a : α), (b : α) => congr_arg some (mul_comm a b)
    | (_ : α), 1 => rfl
    | 1, (_ : α) => rfl
    | 1, 1 => rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: [Inv α] (a : α)
  statement: ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹
  proof: rfl

中文:
定理 coe_inv
  条件: [取逆 α] (a : α)
  结论: ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹
  证明: rfl
-/
theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹ :=
  rfl

/--
Specialization of `Option.getD` to values in `WithOne α` that respects API boundaries.
-/
@[to_additive
  /-- Specialization of `Option.getD` to values in `WithZero α` that respects API boundaries. -/]
/--
Definition of `unoneD` / `unoneD` 的定义

English:
definition unoneD
  signature: (d : α) (x : WithOne α)
  body: recOneCoe d id x

@[to_additive (attr := simp)]

中文:
定义 unoneD
  签名: (d : α) (x : WithOne α)
  定义体: recOneCoe d id x

@[to_additive (attr := simp)]

Depends on / 依赖: recOneCoe
-/
def unoneD (d : α) (x : WithOne α) : α := recOneCoe d id x

@[to_additive (attr := simp)]
/--
theorem `unoneD_one` / 定理 `unoneD_one`

English:
theorem unoneD_one
  given: (d : α)
  statement: unoneD d 1 = d
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unoneD_one
  条件: (d : α)
  结论: unoneD d 1 = d
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unoneD_one (d : α) : unoneD d 1 = d :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unoneD_coe` / 定理 `unoneD_coe`

English:
theorem unoneD_coe
  given: (d x : α)
  statement: unoneD d x = x
  proof: rfl

@[to_additive]

中文:
定理 unoneD_coe
  条件: (d x : α)
  结论: unoneD d x = x
  证明: rfl

@[to_additive]
-/
theorem unoneD_coe (d x : α) : unoneD d x = x :=
  rfl

@[to_additive]
/--
theorem `unoneD_eq_iff` / 定理 `unoneD_eq_iff`

English:
theorem unoneD_eq_iff
  given: {d y : α} {x : WithOne α}
  statement: unoneD d x = y ↔ x = y ∨ x = 1 ∧ y = d
  proof: by
  induction x <;> simp [@eq_comm _ d]

@[to_additive (attr := simp)]

中文:
定理 unoneD_eq_iff
  条件: {d y : α} {x : WithOne α}
  结论: unoneD d x = y ↔ x = y ∨ x = 1 ∧ y = d
  证明: by
  induction x <;> simp [@eq_comm _ d]

@[to_additive (attr := simp)]

Depends on / 依赖: eq_comm
-/
theorem unoneD_eq_iff {d y : α} {x : WithOne α} : unoneD d x = y ↔ x = y ∨ x = 1 ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[to_additive (attr := simp)]
/--
theorem `unoneD_eq_self_iff` / 定理 `unoneD_eq_self_iff`

English:
theorem unoneD_eq_self_iff
  given: {d : α} {x : WithOne α}
  statement: unoneD d x = d ↔ x = d ∨ x = 1
  proof: by
  simp [unoneD_eq_iff]

@[to_additive]

中文:
定理 unoneD_eq_self_iff
  条件: {d : α} {x : WithOne α}
  结论: unoneD d x = d ↔ x = d ∨ x = 1
  证明: by
  simp [unoneD_eq_iff]

@[to_additive]

Depends on / 依赖: unoneD_eq_iff
-/
theorem unoneD_eq_self_iff {d : α} {x : WithOne α} : unoneD d x = d ↔ x = d ∨ x = 1 := by
  simp [unoneD_eq_iff]

@[to_additive]
/--
theorem `unoneD_eq_unoneD_iff` / 定理 `unoneD_eq_unoneD_iff`

English:
theorem unoneD_eq_unoneD_iff
  given: {d : α} {x y : WithOne α}
  proof: by
  induction y <;> simp [unoneD_eq_iff, or_comm]

@[to_additive]

中文:
定理 unoneD_eq_unoneD_iff
  条件: {d : α} {x y : WithOne α}
  证明: by
  induction y <;> simp [unoneD_eq_iff, or_comm]

@[to_additive]

Depends on / 依赖: or_comm, unoneD_eq_iff
-/
theorem unoneD_eq_unoneD_iff {d : α} {x y : WithOne α} :
    unoneD d x = unoneD d y ↔ x = y ∨ x = d ∧ y = 1 ∨ x = 1 ∧ y = d := by
  induction y <;> simp [unoneD_eq_iff, or_comm]

@[to_additive]
/--
lemma `unoneD_eq_unone` / 引理 `unoneD_eq_unone`

English:
lemma unoneD_eq_unone
  given: {d : α} {x : WithOne α} (hx : x != 1)
  statement: unoneD d x = unone hx
  proof: by
  simp [unoneD_eq_iff]

中文:
引理 unoneD_eq_unone
  条件: {d : α} {x : WithOne α} (hx : x != 1)
  结论: unoneD d x = unone hx
  证明: by
  simp [unoneD_eq_iff]

Depends on / 依赖: unoneD_eq_iff
-/
lemma unoneD_eq_unone {d : α} {x : WithOne α} (hx : x != 1) : unoneD d x = unone hx := by
  simp [unoneD_eq_iff]

end WithOne
