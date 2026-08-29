/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Logic.Pairwise

import Mathlib.Util.Delaborators

/-!
# Extra lemmas about products of monoids and groups

This file proves lemmas about the instances defined in `Algebra.Group.Pi.Basic` that require more
imports.
-/

@[expose] public section

assert_not_exists AddMonoidWithOne MonoidWithZero

universe u v w

variable {ι α : Type*}
variable {I : Type u}
variable {f : I -> Type v} {M N : ι -> Type*}

variable (i : I)

@[to_additive (attr := simp)]
/--
theorem `Set.range_one` / 定理 `Set.range_one`

English:
theorem Set.range_one
  given: {α β : Type*} [One β] [Nonempty α]
  statement: Set.range (1 : α -> β) = {1}
  proof: range_const

@[to_additive]

中文:
定理 Set.range_one
  条件: {α β : 类型} [One β] [Nonempty α]
  结论: Set.range (1 : α -> β) = {1}
  证明: range_const

@[to_additive]

Depends on / 依赖: range_const
-/
theorem Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.range (1 : α -> β) = {1} :=
  range_const

@[to_additive]
/--
theorem `Set.preimage_one` / 定理 `Set.preimage_one`

English:
theorem Set.preimage_one
  given: {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) in s)]
  proof: Set.preimage_const 1 s

中文:
定理 Set.preimage_one
  条件: {α β : 类型} [One β] (s : Set β) [Decidable ((1 : β) in s)]
  证明: Set.preimage_const 1 s

Depends on / 依赖: Set.preimage_const, preimage_const
-/
theorem Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) in s)] :
    (1 : α -> β) ⁻¹' s = if (1 : β) in s then Set.univ else ∅ :=
  Set.preimage_const 1 s

namespace Pi

@[to_additive]
/--
Instance `instIsMulTorsionFree` / 实例 `instIsMulTorsionFree`

English:
instance instIsMulTorsionFree
  signature: [forall i, Monoid (M i)] [forall i, IsMulTorsionFree (M i)]
  body: by ext i; exact pow_left_injective hn congr_fun hab i

中文:
实例 instIsMulTorsionFree
  签名: [对任意 i, Monoid (M i)] [对任意 i, IsMulTorsionFree (M i)]
  定义体: by ext i; exact pow_left_injective hn congr_fun hab i

Depends on / 依赖: congr_fun, pow_left_injective
-/
instance instIsMulTorsionFree [forall i, Monoid (M i)] [forall i, IsMulTorsionFree (M i)] :
    IsMulTorsionFree (forall i, M i) where
pow_left_injective n hn a b hab := by ext i; exact pow_left_injective hn congr_fun hab i

variable {α β : Type*} [Preorder α] [Preorder β]

/--
lemma `one_mono` / 引理 `one_mono`

English:
lemma one_mono
  given: [One β]
  statement: Monotone (1 : α -> β)
  proof: monotone_const

中文:
引理 one_mono
  条件: [One β]
  结论: Monotone (1 : α -> β)
  证明: monotone_const
-/
@[to_additive] lemma one_mono [One β] : Monotone (1 : α -> β) := monotone_const
/--
lemma `one_anti` / 引理 `one_anti`

English:
lemma one_anti
  given: [One β]
  statement: Antitone (1 : α -> β)
  proof: antitone_const

中文:
引理 one_anti
  条件: [One β]
  结论: Antitone (1 : α -> β)
  证明: antitone_const
-/
@[to_additive] lemma one_anti [One β] : Antitone (1 : α -> β) := antitone_const

end Pi

namespace MulHom

@[to_additive]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M ->ₙ* N)
  statement: (f * g : M -> N) =
  proof: rfl

中文:
定理 coe_mul
  条件: {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M ->ₙ* N)
  结论: (f * g : M -> N) =
  证明: rfl
-/
theorem coe_mul {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M ->ₙ* N) : (f * g : M -> N) =
    fun x => f x * g x := rfl

end MulHom

section MulHom

variable [(i : I) -> Mul (f i)]

/-- A family of MulHom's `f a : γ →ₙ* β a` defines a MulHom `MulHom.pi f : γ →ₙ* Π a, β a`
given by `MulHom.pi f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of AddHom's `f a : γ → β a` defines an AddHom `AddHom.pi f : γ → Π a, β a` given by
  `AddHom.pi f x b = f b x`. -/]
/--
Definition of `MulHom.pi` / `MulHom.pi` 的定义

English:
definition MulHom.pi
  signature: {γ : Type w} [Mul γ] (g : forall i, γ ->ₙ* f i)
  body: g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom := MulHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom_apply := MulHom.pi_apply

@[to_additive]

中文:
定义 MulHom.pi
  签名: {γ : Type w} [Mul γ] (g : 对任意 i, γ ->ₙ* f i)
  定义体: g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom := MulHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom_apply := MulHom.pi_apply

@[to_additive]
-/
def MulHom.pi {γ : Type w} [Mul γ] (g : forall i, γ ->ₙ* f i) : γ ->ₙ* forall i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom := MulHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom_apply := MulHom.pi_apply

@[to_additive]
/--
theorem `MulHom.pi_injective` / 定理 `MulHom.pi_injective`

English:
theorem MulHom.pi_injective
  statement: {γ : Type w} [Nonempty I] [Mul γ] (g : forall i, γ ->ₙ* f i)
  proof: fun _ _ h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((funext_iff.mp h :) i)

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MulHom.injective_pi := MulHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.mulHom_injective := MulHom.pi_injective

中文:
定理 MulHom.pi_injective
  结论: {γ : Type w} [Nonempty I] [Mul γ] (g : 对任意 i, γ ->ₙ* f i)
  证明: fun _ _ h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((funext_iff.mp h :) i)

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MulHom.injective_pi := MulHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.mulHom_injective := MulHom.pi_injective

Depends on / 依赖: div_self, mem_div
-/
theorem MulHom.pi_injective {γ : Type w} [Nonempty I] [Mul γ] (g : forall i, γ ->ₙ* f i)
    (hg : forall i, Function.Injective (g i)) : Function.Injective (MulHom.pi g) := fun _ _ h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((funext_iff.mp h :) i)

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MulHom.injective_pi := MulHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.mulHom_injective := MulHom.pi_injective

variable (f)

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `Function.eval i` as a `MulHom`. -/
@[to_additive (attr := simps)
  /-- Evaluation of functions into an indexed collection of additive semigroups at a point is an
  additive semigroup homomorphism. This is `Function.eval i` as an `AddHom`. -/]
/--
Definition of `Pi.evalMulHom` / `Pi.evalMulHom` 的定义

English:
definition Pi.evalMulHom
  signature: (i : I)
  body: g i
  map_mul' _ _ := Pi.mul_apply _ _ i

中文:
定义 Pi.evalMulHom
  签名: (i : I)
  定义体: g i
  map_mul' _ _ := Pi.mul_apply _ _ i
-/
def Pi.evalMulHom (i : I) : (forall i, f i) ->ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i

/-- A family of MulHom's `f i : M i →ₙ* N i` defines a MulHom
`MulHom.piMap f : (Π i, M i) →ₙ* (Π i, N i)`
given by `MulHom.piMap f x i = f i x`. This is `Pi.map` for `MulHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of AddHom's `f i : M i →ₙ+ N i` defines an AddHom
  `AddHom.piMap f : (Π i, M i) →ₙ+ (Π i, N i)`
  given by `AddHom.piMap f x i = f i x`. This is `Pi.map` for `AddHom`s. -/]
/--
Definition of `MulHom.piMap` / `MulHom.piMap` 的定义

English:
definition MulHom.piMap
  signature: [Π i, Mul (M i)] [Π i, Mul (N i)] (g : Π i, M i ->ₙ* N i)
  body: .pi fun i => (g i).comp (Pi.evalMulHom M i)

中文:
定义 MulHom.piMap
  签名: [Π i, Mul (M i)] [Π i, Mul (N i)] (g : Π i, M i ->ₙ* N i)
  定义体: .pi fun i => (g i).comp (Pi.evalMulHom M i)

Depends on / 依赖: Pi.evalMulHom, evalMulHom
-/
def MulHom.piMap [Π i, Mul (M i)] [Π i, Mul (N i)] (g : Π i, M i ->ₙ* N i) :
    (Π i, M i) ->ₙ* (Π i, N i) :=
  .pi fun i => (g i).comp (Pi.evalMulHom M i)

/-- `Function.const` as a `MulHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddHom`. -/]
/--
Definition of `Pi.constMulHom` / `Pi.constMulHom` 的定义

English:
definition Pi.constMulHom
  signature: (α β : Type*) [Mul β]
  body: Function.const α
  map_mul' _ _ := rfl

中文:
定义 Pi.constMulHom
  签名: (α β : 类型) [Mul β]
  定义体: Function.const α
  map_mul' _ _ := rfl

Depends on / 依赖: Function, Function.const
-/
def Pi.constMulHom (α β : Type*) [Mul β] :
    β ->ₙ* α -> β where
  toFun := Function.const α
  map_mul' _ _ := rfl

/-- Coercion of a `MulHom` into a function is itself a `MulHom`.

See also `MulHom.eval`. -/
@[to_additive (attr := simps) /-- Coercion of an `AddHom` into a function is itself an `AddHom`.

See also `AddHom.eval`. -/]
/--
Definition of `MulHom.coeFn` / `MulHom.coeFn` 的定义

English:
definition MulHom.coeFn
  signature: (α β : Type*) [Mul α] [CommSemigroup β]
  body: g
  map_mul' _ _ := rfl

中文:
定义 MulHom.coeFn
  签名: (α β : 类型) [Mul α] [CommSemigroup β]
  定义体: g
  map_mul' _ _ := rfl
-/
def MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] :
    (α ->ₙ* β) ->ₙ* α -> β where
  toFun g := g
  map_mul' _ _ := rfl

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps) /-- Additive semigroup homomorphism between the function spaces
  `I → α` and `I → β`, induced by an additive semigroup homomorphism `f` between `α` and `β` -/]
/--
Definition of `MulHom.compLeft` / `MulHom.compLeft` 的定义

English:
definition MulHom.compLeft
  signature: {α β : Type*} [Mul α] [Mul β] (f : α ->ₙ* β) (I : Type*)
  body: f ∘ h
  map_mul' _ _ := by ext; simp

中文:
定义 MulHom.compLeft
  签名: {α β : 类型} [Mul α] [Mul β] (f : α ->ₙ* β) (I : 类型)
  定义体: f ∘ h
  map_mul' _ _ := by ext; simp
-/
protected def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α ->ₙ* β) (I : Type*) :
    (I -> α) ->ₙ* I -> β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp

end MulHom

section MonoidHom

variable [(i : I) -> MulOneClass (f i)]

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`Pi.monoidHom f : γ →* Π a, β a` given by `Pi.monoidHom f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid homomorphism
  `Pi.addMonoidHom f : γ →+ Π a, β a` given by `Pi.addMonoidHom f x b = f b x`. -/]
/--
Definition of `MonoidHom.pi` / `MonoidHom.pi` 的定义

English:
definition MonoidHom.pi
  signature: {γ : Type w} [MulOneClass γ] (g : forall i, γ ->* f i)
  body: { MulHom.pi fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.monoidHom := MonoidHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_apply

中文:
定义 MonoidHom.pi
  签名: {γ : Type w} [MulOneClass γ] (g : 对任意 i, γ ->* f i)
  定义体: { MulHom.pi fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.monoidHom := MonoidHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_apply

Depends on / 依赖: MulHom, MulHom.pi, map_one, toMulHom
-/
def MonoidHom.pi {γ : Type w} [MulOneClass γ] (g : forall i, γ ->* f i) :
    γ ->* forall i, f i :=
  { MulHom.pi fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.monoidHom := MonoidHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_apply := MonoidHom.pi_apply

@[to_additive]
/--
theorem `MonoidHom.pi_injective` / 定理 `MonoidHom.pi_injective`

English:
theorem MonoidHom.pi_injective
  statement: {γ : Type w} [Nonempty I] [MulOneClass γ]
  proof: MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MonoidHom.injective_pi := MonoidHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_injective := MonoidHom.pi_injective

中文:
定理 MonoidHom.pi_injective
  结论: {γ : Type w} [Nonempty I] [MulOneClass γ]
  证明: MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MonoidHom.injective_pi := MonoidHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_injective := MonoidHom.pi_injective

Depends on / 依赖: MulHom, MulHom.pi_injective, pi_injective, toMulHom
-/
theorem MonoidHom.pi_injective {γ : Type w} [Nonempty I] [MulOneClass γ]
    (g : forall i, γ ->* f i) (hg : forall i, Function.Injective (g i)) :
    Function.Injective (MonoidHom.pi g) :=
  MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias MonoidHom.injective_pi := MonoidHom.pi_injective

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_injective := MonoidHom.pi_injective

variable (f)

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `Function.eval i` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- Evaluation of functions into an indexed collection of additive
monoids at a point is an additive monoid homomorphism. This is `Function.eval i` as an
`AddMonoidHom`. -/]
/--
Definition of `Pi.evalMonoidHom` / `Pi.evalMonoidHom` 的定义

English:
definition Pi.evalMonoidHom
  signature: (i : I)
  body: g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[simp, norm_cast]

中文:
定义 Pi.evalMonoidHom
  签名: (i : I)
  定义体: g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[simp, norm_cast]
-/
def Pi.evalMonoidHom (i : I) : (forall i, f i) ->* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[simp, norm_cast]
/--
lemma `Pi.coe_evalMonoidHom` / 引理 `Pi.coe_evalMonoidHom`

English:
lemma Pi.coe_evalMonoidHom
  given: (i : I)
  statement: ⇑(evalMonoidHom f i) = Function.eval i
  proof: rfl

中文:
引理 Pi.coe_evalMonoidHom
  条件: (i : I)
  结论: ⇑(evalMonoidHom f i) = Function.eval i
  证明: rfl
-/
lemma Pi.coe_evalMonoidHom (i : I) : ⇑(evalMonoidHom f i) = Function.eval i := rfl

/-- A family of monoid homomorphisms `f i : M i →* N i` defines a monoid homomorphism
`MonoidHom.piMap f : (Π i, M i) →* (Π i, N i)`
given by `MonoidHom.piMap f x i = f i x`. This is `Pi.map` for `MonoidHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of additive monoid homomorphisms `f i : M i →+ N i` defines an additive monoid
  homomorphism `AddMonoidHom.piMap f : (Π i, M i) →+ (Π i, N i)`
  given by `AddMonoidHom.piMap f x i = f i x`. This is `Pi.map` for `AddMonoidHom`s. -/]
/--
Definition of `MonoidHom.piMap` / `MonoidHom.piMap` 的定义

English:
definition MonoidHom.piMap
  signature: [Π i, MulOneClass (M i)] [Π i, MulOneClass (N i)] (g : Π i, M i ->* N i)
  body: .pi fun i => (g i).comp (Pi.evalMonoidHom M i)

中文:
定义 MonoidHom.piMap
  签名: [Π i, MulOneClass (M i)] [Π i, MulOneClass (N i)] (g : Π i, M i ->* N i)
  定义体: .pi fun i => (g i).comp (Pi.evalMonoidHom M i)

Depends on / 依赖: Pi.evalMonoidHom, evalMonoidHom
-/
def MonoidHom.piMap [Π i, MulOneClass (M i)] [Π i, MulOneClass (N i)] (g : Π i, M i ->* N i) :
    (Π i, M i) ->* (Π i, N i) :=
  .pi fun i => (g i).comp (Pi.evalMonoidHom M i)

/-- `Function.const` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddMonoidHom`. -/]
/--
Definition of `Pi.constMonoidHom` / `Pi.constMonoidHom` 的定义

English:
definition Pi.constMonoidHom
  signature: (α β : Type*) [MulOneClass β]
  body: Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 Pi.constMonoidHom
  签名: (α β : 类型) [MulOneClass β]
  定义体: Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Function, Function.const
-/
def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β ->* α -> β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coercion of a `MonoidHom` into a function is itself a `MonoidHom`.

See also `MonoidHom.eval`. -/
@[to_additive (attr := simps) /-- Coercion of an `AddMonoidHom` into a function is itself
an `AddMonoidHom`.

See also `AddMonoidHom.eval`. -/]
/--
Definition of `MonoidHom.coeFn` / `MonoidHom.coeFn` 的定义

English:
definition MonoidHom.coeFn
  signature: (α β : Type*) [MulOneClass α] [CommMonoid β]
  body: g
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 MonoidHom.coeFn
  签名: (α β : 类型) [MulOneClass α] [CommMonoid β]
  定义体: g
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α ->* β) ->* α -> β where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps)
  /-- Additive monoid homomorphism between the function spaces `I → α` and `I → β`, induced by an
  additive monoid homomorphism `f` between `α` and `β` -/]
/--
Definition of `MonoidHom.compLeft` / `MonoidHom.compLeft` 的定义

English:
definition MonoidHom.compLeft
  signature: {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α ->* β)
  body: f ∘ h
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

中文:
定义 MonoidHom.compLeft
  签名: {α β : 类型} [MulOneClass α] [MulOneClass β] (f : α ->* β)
  定义体: f ∘ h
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
-/
protected def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α ->* β)
    (I : Type*) : (I -> α) ->* I -> β where
  toFun h := f ∘ h
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f) in
/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `OneHom` version of `Pi.mulSingle`. -/
@[to_additive
  /-- The zero-preserving homomorphism including a single value into a dependent family of values,
  as functions supported at a point.

  This is the `ZeroHom` version of `Pi.single`. -/]
nonrec def OneHom.mulSingle [forall i, One <| f i] (i : I) : OneHom (f i) (forall i, f i) where
  toFun := mulSingle i
  map_one' := mulSingle_one i

@[to_additive (attr := simp)]
/--
theorem `OneHom.mulSingle_apply` / 定理 `OneHom.mulSingle_apply`

English:
theorem OneHom.mulSingle_apply
  given: [forall i, One <| f i] (i : I) (x : f i)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 OneHom.mulSingle_apply
  条件: [对任意 i, One <| f i] (i : I) (x : f i)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem OneHom.mulSingle_apply [forall i, One <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x := rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `OneHom.coe_mulSingle` / 定理 `OneHom.coe_mulSingle`

English:
theorem OneHom.coe_mulSingle
  given: [forall i, One <| f i] (i : I)
  proof: rfl

中文:
定理 OneHom.coe_mulSingle
  条件: [对任意 i, One <| f i] (i : I)
  证明: rfl
-/
theorem OneHom.coe_mulSingle [forall i, One <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

variable (f) in
/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `MonoidHom` version of `Pi.mulSingle`. -/
@[to_additive
  /-- The additive monoid homomorphism including a single additive monoid into a dependent family
  of additive monoids, as functions supported at a point.

  This is the `AddMonoidHom` version of `Pi.single`. -/]
/--
Definition of `MonoidHom.mulSingle` / `MonoidHom.mulSingle` 的定义

English:
definition MonoidHom.mulSingle
  signature: [forall i, MulOneClass <| f i] (i : I)
  body: { OneHom.mulSingle f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }

@[to_additive (attr := simp)]

中文:
定义 MonoidHom.mulSingle
  签名: [对任意 i, MulOneClass <| f i] (i : I)
  定义体: { OneHom.mulSingle f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }

@[to_additive (attr := simp)]

Depends on / 依赖: OneHom, OneHom.mulSingle, map_mul, mulSingle, one_mul
-/
def MonoidHom.mulSingle [forall i, MulOneClass <| f i] (i : I) : f i ->* forall i, f i :=
  { OneHom.mulSingle f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }

@[to_additive (attr := simp)]
/--
theorem `MonoidHom.mulSingle_apply` / 定理 `MonoidHom.mulSingle_apply`

English:
theorem MonoidHom.mulSingle_apply
  given: [forall i, MulOneClass <| f i] (i : I) (x : f i)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 MonoidHom.mulSingle_apply
  条件: [对任意 i, MulOneClass <| f i] (i : I) (x : f i)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem MonoidHom.mulSingle_apply [forall i, MulOneClass <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `MonoidHom.coe_mulSingle` / 定理 `MonoidHom.coe_mulSingle`

English:
theorem MonoidHom.coe_mulSingle
  given: [forall i, MulOneClass <| f i] (i : I)
  proof: rfl

@[to_additive]

中文:
定理 MonoidHom.coe_mulSingle
  条件: [对任意 i, MulOneClass <| f i] (i : I)
  证明: rfl

@[to_additive]
-/
theorem MonoidHom.coe_mulSingle [forall i, MulOneClass <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

@[to_additive]
/--
theorem `Pi.mulSingle_sup` / 定理 `Pi.mulSingle_sup`

English:
theorem Pi.mulSingle_sup
  given: [forall i, SemilatticeSup (f i)] [forall i, One (f i)] (i : I) (x y : f i)
  proof: Function.update_sup _ _ _ _

@[to_additive]

中文:
定理 Pi.mulSingle_sup
  条件: [对任意 i, SemilatticeSup (f i)] [对任意 i, One (f i)] (i : I) (x y : f i)
  证明: Function.update_sup _ _ _ _

@[to_additive]

Depends on / 依赖: Function, Function.update_sup, update_sup
-/
theorem Pi.mulSingle_sup [forall i, SemilatticeSup (f i)] [forall i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y :=
  Function.update_sup _ _ _ _

@[to_additive]
/--
theorem `Pi.mulSingle_inf` / 定理 `Pi.mulSingle_inf`

English:
theorem Pi.mulSingle_inf
  given: [forall i, SemilatticeInf (f i)] [forall i, One (f i)] (i : I) (x y : f i)
  proof: Function.update_inf _ _ _ _

@[to_additive]

中文:
定理 Pi.mulSingle_inf
  条件: [对任意 i, SemilatticeInf (f i)] [对任意 i, One (f i)] (i : I) (x y : f i)
  证明: Function.update_inf _ _ _ _

@[to_additive]

Depends on / 依赖: Function, Function.update_inf, update_inf
-/
theorem Pi.mulSingle_inf [forall i, SemilatticeInf (f i)] [forall i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊓ y) = Pi.mulSingle i x ⊓ Pi.mulSingle i y :=
  Function.update_inf _ _ _ _

@[to_additive]
/--
theorem `Pi.mulSingle_mul` / 定理 `Pi.mulSingle_mul`

English:
theorem Pi.mulSingle_mul
  given: [forall i, MulOneClass <| f i] (i : I) (x y : f i)
  proof: (MonoidHom.mulSingle f i).map_mul x y

@[to_additive]

中文:
定理 Pi.mulSingle_mul
  条件: [对任意 i, MulOneClass <| f i] (i : I) (x y : f i)
  证明: (MonoidHom.mulSingle f i).map_mul x y

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, map_mul, mulSingle
-/
theorem Pi.mulSingle_mul [forall i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.mulSingle f i).map_mul x y

@[to_additive]
/--
theorem `Pi.mulSingle_inv` / 定理 `Pi.mulSingle_inv`

English:
theorem Pi.mulSingle_inv
  given: [forall i, Group <| f i] (i : I) (x : f i)
  proof: (MonoidHom.mulSingle f i).map_inv x

@[to_additive]

中文:
定理 Pi.mulSingle_inv
  条件: [对任意 i, Group <| f i] (i : I) (x : f i)
  证明: (MonoidHom.mulSingle f i).map_inv x

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, map_inv, mulSingle
-/
theorem Pi.mulSingle_inv [forall i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.mulSingle f i).map_inv x

@[to_additive]
/--
theorem `Pi.mulSingle_div` / 定理 `Pi.mulSingle_div`

English:
theorem Pi.mulSingle_div
  given: [forall i, Group <| f i] (i : I) (x y : f i)
  proof: (MonoidHom.mulSingle f i).map_div x y

@[to_additive]

中文:
定理 Pi.mulSingle_div
  条件: [对任意 i, Group <| f i] (i : I) (x y : f i)
  证明: (MonoidHom.mulSingle f i).map_div x y

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, map_div, mulSingle
-/
theorem Pi.mulSingle_div [forall i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.mulSingle f i).map_div x y

@[to_additive]
/--
theorem `Pi.mulSingle_pow` / 定理 `Pi.mulSingle_pow`

English:
theorem Pi.mulSingle_pow
  given: [forall i, Monoid (f i)] (i : I) (x : f i) (n : Nat)
  proof: (MonoidHom.mulSingle f i).map_pow x n

@[to_additive]

中文:
定理 Pi.mulSingle_pow
  条件: [对任意 i, Monoid (f i)] (i : I) (x : f i) (n : 自然数)
  证明: (MonoidHom.mulSingle f i).map_pow x n

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, map_pow, mulSingle
-/
theorem Pi.mulSingle_pow [forall i, Monoid (f i)] (i : I) (x : f i) (n : Nat) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_pow x n

@[to_additive]
/--
theorem `Pi.mulSingle_zpow` / 定理 `Pi.mulSingle_zpow`

English:
theorem Pi.mulSingle_zpow
  given: [forall i, Group (f i)] (i : I) (x : f i) (n : Int)
  proof: (MonoidHom.mulSingle f i).map_zpow x n

中文:
定理 Pi.mulSingle_zpow
  条件: [对任意 i, Group (f i)] (i : I) (x : f i) (n : 整数)
  证明: (MonoidHom.mulSingle f i).map_zpow x n

Depends on / 依赖: MonoidHom, MonoidHom.mulSingle, map_zpow, mulSingle
-/
theorem Pi.mulSingle_zpow [forall i, Group (f i)] (i : I) (x : f i) (n : Int) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_zpow x n

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `Commute.map` -/
@[to_additive
  /-- The injection into an additive pi group at different indices commutes.

  For injections of commuting elements at the same index, see `AddCommute.map` -/]
/--
theorem `Pi.mulSingle_commute` / 定理 `Pi.mulSingle_commute`

English:
theorem Pi.mulSingle_commute
  given: [forall i, MulOneClass <| f i]
  proof: by
  intro i j hij x y; ext k
  by_cases i = k <;> simp_all

中文:
定理 Pi.mulSingle_commute
  条件: [对任意 i, MulOneClass <| f i]
  证明: by
  intro i j hij x y; ext k
  by_cases i = k <;> simp_all
-/
theorem Pi.mulSingle_commute [forall i, MulOneClass <| f i] :
    Pairwise fun i j => forall (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y; ext k
  by_cases i = k <;> simp_all

/-- The injection into a pi group with the same values commutes. -/
@[to_additive /-- The injection into an additive pi group with the same values commutes. -/]
/--
theorem `Pi.mulSingle_apply_commute` / 定理 `Pi.mulSingle_apply_commute`

English:
theorem Pi.mulSingle_apply_commute
  given: [forall i, MulOneClass <| f i] (x : forall i, f i) (i j : I)
  proof: by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _

@[to_additive]

中文:
定理 Pi.mulSingle_apply_commute
  条件: [对任意 i, MulOneClass <| f i] (x : 对任意 i, f i) (i j : I)
  证明: by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _

@[to_additive]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Pi.mulSingle_commute, eq_or_ne, mulSingle_commute
-/
theorem Pi.mulSingle_apply_commute [forall i, MulOneClass <| f i] (x : forall i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _

@[to_additive]
/--
theorem `Pi.update_eq_div_mul_mulSingle` / 定理 `Pi.update_eq_div_mul_mulSingle`

English:
theorem Pi.update_eq_div_mul_mulSingle
  given: [forall i, Group <| f i] (g : forall i : I, f i) (x : f i)
  proof: by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, eqComm]

@[to_additive]

中文:
定理 Pi.update_eq_div_mul_mulSingle
  条件: [对任意 i, Group <| f i] (g : 对任意 i : I, f i) (x : f i)
  证明: by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, eqComm]

@[to_additive]

Depends on / 依赖: eqComm, eq_or_ne
-/
theorem Pi.update_eq_div_mul_mulSingle [forall i, Group <| f i] (g : forall i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, eqComm]

@[to_additive]
/--
theorem `Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle` / 定理 `Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle`

English:
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle
  statement: {M : Type*} [CommMonoid M]
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := congr_fun h m
    have hn := congr_fun h n
    grind [mul_one, one_mul, mul_apply]
  · aesop (add simp [mulSingle_apply])

中文:
定理 Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle
  结论: {M : 类型} [CommMonoid M]
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := congr_fun h m
    have hn := congr_fun h n
    grind [mul_one, one_mul, mul_apply]
  · aesop (add simp [mulSingle_apply])

Depends on / 依赖: congr_fun, mulSingle_apply, mul_apply, mul_one, one_mul
-/
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u != 1) (hv : v != 1) :
    (mulSingle k u : I -> M) * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n := by
  refine ⟨fun h => ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := congr_fun h m
    have hn := congr_fun h n
    grind [mul_one, one_mul, mul_apply]
  · aesop (add simp [mulSingle_apply])

end Single

section
variable [forall i, Mul <| f i]

@[to_additive]
/--
theorem `SemiconjBy.pi` / 定理 `SemiconjBy.pi`

English:
theorem SemiconjBy.pi
  given: {x y z : forall i, f i} (h : forall i, SemiconjBy (x i) (y i) (z i))
  proof: funext h

@[to_additive]

中文:
定理 SemiconjBy.pi
  条件: {x y z : 对任意 i, f i} (h : 对任意 i, SemiconjBy (x i) (y i) (z i))
  证明: funext h

@[to_additive]
-/
theorem SemiconjBy.pi {x y z : forall i, f i} (h : forall i, SemiconjBy (x i) (y i) (z i)) :
    SemiconjBy x y z :=
  funext h

@[to_additive]
/--
theorem `Pi.semiconjBy_iff` / 定理 `Pi.semiconjBy_iff`

English:
theorem Pi.semiconjBy_iff
  given: {x y z : forall i, f i}
  proof: funext_iff

@[to_additive]

中文:
定理 Pi.semiconjBy_iff
  条件: {x y z : 对任意 i, f i}
  证明: funext_iff

@[to_additive]

Depends on / 依赖: funext_iff
-/
theorem Pi.semiconjBy_iff {x y z : forall i, f i} :
    SemiconjBy x y z ↔ forall i, SemiconjBy (x i) (y i) (z i) := funext_iff

@[to_additive]
/--
theorem `Commute.pi` / 定理 `Commute.pi`

English:
theorem Commute.pi
  given: {x y : forall i, f i} (h : forall i, Commute (x i) (y i))
  statement: Commute x y
  proof: SemiconjBy.pi h

@[to_additive]

中文:
定理 Commute.pi
  条件: {x y : 对任意 i, f i} (h : 对任意 i, Commute (x i) (y i))
  结论: Commute x y
  证明: SemiconjBy.pi h

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.pi
-/
theorem Commute.pi {x y : forall i, f i} (h : forall i, Commute (x i) (y i)) : Commute x y := SemiconjBy.pi h

@[to_additive]
/--
theorem `Pi.commute_iff` / 定理 `Pi.commute_iff`

English:
theorem Pi.commute_iff
  given: {x y : forall i, f i}
  statement: Commute x y ↔ forall i, Commute (x i) (y i)
  proof: semiconjBy_iff

中文:
定理 Pi.commute_iff
  条件: {x y : 对任意 i, f i}
  结论: Commute x y ↔ 对任意 i, Commute (x i) (y i)
  证明: semiconjBy_iff

Depends on / 依赖: semiconjBy_iff
-/
theorem Pi.commute_iff {x y : forall i, f i} : Commute x y ↔ forall i, Commute (x i) (y i) := semiconjBy_iff

end

namespace Function

@[to_additive (attr := simp)]
/--
theorem `update_one` / 定理 `update_one`

English:
theorem update_one
  given: [forall i, One (f i)] [DecidableEq I] (i : I)
  statement: update (1 : forall i, f i) i 1 = 1
  proof: update_eq_self i (1 : (a : I) -> f a)

@[to_additive]

中文:
定理 update_one
  条件: [对任意 i, One (f i)] [DecidableEq I] (i : I)
  结论: update (1 : 对任意 i, f i) i 1 = 1
  证明: update_eq_self i (1 : (a : I) -> f a)

@[to_additive]

Depends on / 依赖: update_eq_self
-/
theorem update_one [forall i, One (f i)] [DecidableEq I] (i : I) : update (1 : forall i, f i) i 1 = 1 :=
  update_eq_self i (1 : (a : I) -> f a)

@[to_additive]
/--
theorem `update_mul` / 定理 `update_mul`

English:
theorem update_mul
  statement: [forall i, Mul (f i)] [DecidableEq I] (f₁ f₂ : forall i, f i) (i : I) (x₁ : f i)
  proof: funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]

中文:
定理 update_mul
  结论: [对任意 i, Mul (f i)] [DecidableEq I] (f₁ f₂ : 对任意 i, f i) (i : I) (x₁ : f i)
  证明: funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
-/
theorem update_mul [forall i, Mul (f i)] [DecidableEq I] (f₁ f₂ : forall i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
/--
theorem `update_inv` / 定理 `update_inv`

English:
theorem update_inv
  given: [forall i, Inv (f i)] [DecidableEq I] (f₁ : forall i, f i) (i : I) (x₁ : f i)
  proof: funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

@[to_additive]

中文:
定理 update_inv
  条件: [对任意 i, Inv (f i)] [DecidableEq I] (f₁ : 对任意 i, f i) (i : I) (x₁ : f i)
  证明: funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

@[to_additive]

Depends on / 依赖: Inv.inv, apply_update
-/
theorem update_inv [forall i, Inv (f i)] [DecidableEq I] (f₁ : forall i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

@[to_additive]
/--
theorem `update_div` / 定理 `update_div`

English:
theorem update_div
  statement: [forall i, Div (f i)] [DecidableEq I] (f₁ f₂ : forall i, f i) (i : I) (x₁ : f i)
  proof: funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm

中文:
定理 update_div
  结论: [对任意 i, Div (f i)] [DecidableEq I] (f₁ f₂ : 对任意 i, f i) (i : I) (x₁ : f i)
  证明: funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm
-/
theorem update_div [forall i, Div (f i)] [DecidableEq I] (f₁ f₂ : forall i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm

variable [One α] [Nonempty ι] {a : α}

@[to_additive (attr := simp)]
/--
theorem `const_eq_one` / 定理 `const_eq_one`

English:
theorem const_eq_one
  statement: const ι a = 1 ↔ a = 1
  proof: @const_inj _ _ _ _ 1

@[to_additive]

中文:
定理 const_eq_one
  结论: const ι a = 1 ↔ a = 1
  证明: @const_inj _ _ _ _ 1

@[to_additive]

Depends on / 依赖: const_inj
-/
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1

@[to_additive]
/--
theorem `const_ne_one` / 定理 `const_ne_one`

English:
theorem const_ne_one
  statement: const ι a != 1 ↔ a != 1
  proof: Iff.not const_eq_one

中文:
定理 const_ne_one
  结论: const ι a != 1 ↔ a != 1
  证明: Iff.not const_eq_one

Depends on / 依赖: Iff.not, const_eq_one
-/
theorem const_ne_one : const ι a != 1 ↔ a != 1 :=
  Iff.not const_eq_one

end Function

section Piecewise

@[to_additive]
/--
theorem `Set.piecewise_mul` / 定理 `Set.piecewise_mul`

English:
theorem Set.piecewise_mul
  statement: [forall i, Mul (f i)] (s : Set I) [forall i, Decidable (i in s)]
  proof: s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

@[to_additive]

中文:
定理 Set.piecewise_mul
  结论: [对任意 i, Mul (f i)] (s : Set I) [对任意 i, Decidable (i in s)]
  证明: s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

@[to_additive]

Depends on / 依赖: s.piecewise_op
-/
theorem Set.piecewise_mul [forall i, Mul (f i)] (s : Set I) [forall i, Decidable (i in s)]
    (f₁ f₂ g₁ g₂ : forall i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

@[to_additive]
/--
theorem `Set.piecewise_inv` / 定理 `Set.piecewise_inv`

English:
theorem Set.piecewise_inv
  given: [forall i, Inv (f i)] (s : Set I) [forall i, Decidable (i in s)] (f₁ g₁ : forall i, f i)
  proof: s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]

中文:
定理 Set.piecewise_inv
  条件: [对任意 i, Inv (f i)] (s : Set I) [对任意 i, Decidable (i in s)] (f₁ g₁ : 对任意 i, f i)
  证明: s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]

Depends on / 依赖: piecewise_op, s.piecewise_op
-/
theorem Set.piecewise_inv [forall i, Inv (f i)] (s : Set I) [forall i, Decidable (i in s)] (f₁ g₁ : forall i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]
/--
theorem `Set.piecewise_div` / 定理 `Set.piecewise_div`

English:
theorem Set.piecewise_div
  statement: [forall i, Div (f i)] (s : Set I) [forall i, Decidable (i in s)]
  proof: s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)

中文:
定理 Set.piecewise_div
  结论: [对任意 i, Div (f i)] (s : Set I) [对任意 i, Decidable (i in s)]
  证明: s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)

Depends on / 依赖: s.piecewise_op
-/
theorem Set.piecewise_div [forall i, Div (f i)] (s : Set I) [forall i, Decidable (i in s)]
    (f₁ f₂ g₁ g₂ : forall i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι -> η)

/-- `Function.extend s f 1` as a bundled hom. -/
@[to_additive (attr := simps) Function.ExtendByZero.hom
/-- `Function.extend s f 0` as a bundled hom. -/]
/--
Definition of `Function.ExtendByOne.hom` / `Function.ExtendByOne.hom` 的定义

English:
definition Function.ExtendByOne.hom
  signature: [MulOneClass R]
  body: Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1

中文:
定义 Function.ExtendByOne.hom
  签名: [MulOneClass R]
  定义体: Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1

Depends on / 依赖: Function, Function.extend, extend
-/
noncomputable def Function.ExtendByOne.hom [MulOneClass R] :
    (ι -> R) ->* η -> R where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1

end Extend

namespace Pi

variable [DecidableEq I] [forall i, Preorder (f i)] [forall i, One (f i)]

@[to_additive]
/--
theorem `mulSingle_mono` / 定理 `mulSingle_mono`

English:
theorem mulSingle_mono
  statement: Monotone (Pi.mulSingle i : f i -> forall i, f i)
  proof: Function.update_mono

@[to_additive]

中文:
定理 mulSingle_mono
  结论: Monotone (Pi.mulSingle i : f i -> 对任意 i, f i)
  证明: Function.update_mono

@[to_additive]

Depends on / 依赖: Function, Function.update_mono, update_mono
-/
theorem mulSingle_mono : Monotone (Pi.mulSingle i : f i -> forall i, f i) :=
  Function.update_mono

@[to_additive]
/--
theorem `mulSingle_strictMono` / 定理 `mulSingle_strictMono`

English:
theorem mulSingle_strictMono
  statement: StrictMono (Pi.mulSingle i : f i -> forall i, f i)
  proof: Function.update_strictMono

@[to_additive]

中文:
定理 mulSingle_strictMono
  结论: StrictMono (Pi.mulSingle i : f i -> 对任意 i, f i)
  证明: Function.update_strictMono

@[to_additive]

Depends on / 依赖: Function, Function.update_strictMono, update_strictMono
-/
theorem mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i -> forall i, f i) :=
  Function.update_strictMono

@[to_additive]
/--
lemma `mulSingle_comp_equiv` / 引理 `mulSingle_comp_equiv`

English:
lemma mulSingle_comp_equiv
  statement: {m n : Type*} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
  proof: by
  ext x
  aesop (add simp Pi.mulSingle_apply)

中文:
引理 mulSingle_comp_equiv
  结论: {m n : 类型} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
  证明: by
  ext x
  aesop (add simp Pi.mulSingle_apply)

Depends on / 依赖: Pi.mulSingle_apply, mulSingle_apply
-/
lemma mulSingle_comp_equiv {m n : Type*} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
    (i : m) (x : α) : Pi.mulSingle i x ∘ σ = Pi.mulSingle (σ.symm i) x := by
  ext x
  aesop (add simp Pi.mulSingle_apply)

end Pi

namespace Sigma

variable {α : Type*} {β : α -> Type*} {γ : forall a, β a -> Type*}

@[to_additive (attr := simp)]
/--
theorem `curry_one` / 定理 `curry_one`

English:
theorem curry_one
  given: [forall a b, One (γ a b)]
  statement: Sigma.curry (1 : (i : Σ a, β a) -> γ i.1 i.2) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 curry_one
  条件: [对任意 a b, One (γ a b)]
  结论: Sigma.curry (1 : (i : Σ a, β a) -> γ i.1 i.2) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem curry_one [forall a b, One (γ a b)] : Sigma.curry (1 : (i : Σ a, β a) -> γ i.1 i.2) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `uncurry_one` / 定理 `uncurry_one`

English:
theorem uncurry_one
  given: [forall a b, One (γ a b)]
  statement: Sigma.uncurry (1 : forall a b, γ a b) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 uncurry_one
  条件: [对任意 a b, One (γ a b)]
  结论: Sigma.uncurry (1 : 对任意 a b, γ a b) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem uncurry_one [forall a b, One (γ a b)] : Sigma.uncurry (1 : forall a b, γ a b) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `curry_mul` / 定理 `curry_mul`

English:
theorem curry_mul
  given: [forall a b, Mul (γ a b)] (x y : (i : Σ a, β a) -> γ i.1 i.2)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 curry_mul
  条件: [对任意 a b, Mul (γ a b)] (x y : (i : Σ a, β a) -> γ i.1 i.2)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem curry_mul [forall a b, Mul (γ a b)] (x y : (i : Σ a, β a) -> γ i.1 i.2) :
    Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `uncurry_mul` / 定理 `uncurry_mul`

English:
theorem uncurry_mul
  given: [forall a b, Mul (γ a b)] (x y : forall a b, γ a b)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 uncurry_mul
  条件: [对任意 a b, Mul (γ a b)] (x y : 对任意 a b, γ a b)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem uncurry_mul [forall a b, Mul (γ a b)] (x y : forall a b, γ a b) :
    Sigma.uncurry (x * y) = Sigma.uncurry x * Sigma.uncurry y :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `curry_inv` / 定理 `curry_inv`

English:
theorem curry_inv
  given: [forall a b, Inv (γ a b)] (x : (i : Σ a, β a) -> γ i.1 i.2)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 curry_inv
  条件: [对任意 a b, Inv (γ a b)] (x : (i : Σ a, β a) -> γ i.1 i.2)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem curry_inv [forall a b, Inv (γ a b)] (x : (i : Σ a, β a) -> γ i.1 i.2) :
    Sigma.curry (x⁻¹) = (Sigma.curry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `uncurry_inv` / 定理 `uncurry_inv`

English:
theorem uncurry_inv
  given: [forall a b, Inv (γ a b)] (x : forall a b, γ a b)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 uncurry_inv
  条件: [对任意 a b, Inv (γ a b)] (x : 对任意 a b, γ a b)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem uncurry_inv [forall a b, Inv (γ a b)] (x : forall a b, γ a b) :
    Sigma.uncurry (x⁻¹) = (Sigma.uncurry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `curry_mulSingle` / 定理 `curry_mulSingle`

English:
theorem curry_mulSingle
  statement: [DecidableEq α] [forall a, DecidableEq (β a)] [forall a b, One (γ a b)]
  proof: by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

@[to_additive (attr := simp)]

中文:
定理 curry_mulSingle
  结论: [DecidableEq α] [对任意 a, DecidableEq (β a)] [对任意 a b, One (γ a b)]
  证明: by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.mulSingle, Pi.one_apply, Sigma.curry_one, Sigma.curry_update, curry_one, curry_update, mulSingle, one_apply
-/
theorem curry_mulSingle [DecidableEq α] [forall a, DecidableEq (β a)] [forall a b, One (γ a b)]
    (i : Σ a, β a) (x : γ i.1 i.2) :
    Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x) := by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

@[to_additive (attr := simp)]
/--
theorem `uncurry_mulSingle_mulSingle` / 定理 `uncurry_mulSingle_mulSingle`

English:
theorem uncurry_mulSingle_mulSingle
  statement: [DecidableEq α] [forall a, DecidableEq (β a)] [forall a b, One (γ a b)]
  proof: by
  rw [← curry_mulSingle ⟨a]; rw [b⟩]; rw [uncurry_curry]

中文:
定理 uncurry_mulSingle_mulSingle
  结论: [DecidableEq α] [对任意 a, DecidableEq (β a)] [对任意 a b, One (γ a b)]
  证明: by
  rw [← curry_mulSingle ⟨a]; rw [b⟩]; rw [uncurry_curry]

Depends on / 依赖: curry_mulSingle, uncurry_curry
-/
theorem uncurry_mulSingle_mulSingle [DecidableEq α] [forall a, DecidableEq (β a)] [forall a b, One (γ a b)]
    (a : α) (b : β a) (x : γ a b) :
    Sigma.uncurry (Pi.mulSingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x := by
  rw [← curry_mulSingle ⟨a]; rw [b⟩]; rw [uncurry_curry]

end Sigma
