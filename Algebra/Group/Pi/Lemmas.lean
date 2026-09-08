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
variable {f : I → Type v} {M N : ι → Type*}

variable (i : I)

@[to_additive (attr := simp)]
/-
**Set.range_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.range (1 : α -> β) 
= {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
-/
theorem Set.range_one {α β : Type*} [One β] [Nonempty α] : Set.range (1 : α → β) = {1} :=
  range_const

@[to_additive]
/-
**Set.preimage_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) in 
s)] : (1 : α -> β) ⁻¹' s = if (1 : β) in s then Set.univ else ∅
参数：s : Set β；(1 : β) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
-/
theorem Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ :=
  Set.preimage_const 1 s

namespace Pi

@[to_additive]
/-
**Pi.instIsMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instIsMulTorsionFree [forall i, Monoid (M i)] [forall i, IsMulTorsionFree 
(M i)] : IsMulTorsionFree (forall i, M i) where pow_left_injective n hn a b hab
参数：M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
instance instIsMulTorsionFree [∀ i, Monoid (M i)] [∀ i, IsMulTorsionFree (M i)] :
    IsMulTorsionFree (∀ i, M i) where
  pow_left_injective n hn a b hab := by ext i; exact pow_left_injective hn <| congr_fun hab i

variable {α β : Type*} [Preorder α] [Preorder β]
/-
**Pi.one_mono** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : One β], Monotone 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
-/
@[to_additive] lemma one_mono [One β] : Monotone (1 : α → β) := monotone_const
/-
**Pi.one_anti** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : One β], Antitone 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_const`：antitone_const [Preorder α] [Preorder β] {c : β} : Antit
one fun _ : α => c
-/
@[to_additive] lemma one_anti [One β] : Antitone (1 : α → β) := antitone_const

end Pi

namespace MulHom

@[to_additive]
/-
**MulHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_mul {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M ->ₙ* N) : (f * g 
: M -> N) = fun x => f x * g x
参数：f g : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul {M N} {_ : Mul M} {_ : CommSemigroup N} (f g : M →ₙ* N) : (f * g : M → N) =
    fun x => f x * g x := rfl

end MulHom

section MulHom

variable [(i : I) → Mul (f i)]

/-- A family of MulHom's `f a : γ →ₙ* β a` defines a MulHom `MulHom.pi f : γ →ₙ* Π a, β a`
given by `MulHom.pi f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of AddHom's `f a : γ → β a` defines an AddHom `AddHom.pi f : γ → Π a, β a` given by
  `AddHom.pi f x b = f b x`. -/]
/-
**MulHom.pi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.pi {γ : Type w} [Mul γ] (g : forall i, γ ->ₙ* f i) : γ ->ₙ* forall 
i, f i where toFun x i
参数：g : forall i, γ ->ₙ* f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.pi {γ : Type w} [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom := MulHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.mulHom_apply := MulHom.pi_apply

@[to_additive]
/-
**MulHom.pi_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.pi_injective {γ : Type w} [Nonempty I] [Mul γ] (g : forall i, γ ->ₙ
* f i) (hg : forall i, Function.Injective (g i)) : Function.Injective (MulHom.pi
 g)
参数：g : forall i, γ ->ₙ* f i；hg : forall i, Function.Injective (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem MulHom.pi_injective {γ : Type w} [Nonempty I] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (MulHom.pi g) := fun _ _ h =>
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
/-
**Pi.evalMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.evalMulHom (i : I) : (forall i, f i) ->ₙ* f i where toFun g
参数：i : I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
-/
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun g := g i
  map_mul' _ _ := Pi.mul_apply _ _ i

/-- A family of MulHom's `f i : M i →ₙ* N i` defines a MulHom
`MulHom.piMap f : (Π i, M i) →ₙ* (Π i, N i)`
given by `MulHom.piMap f x i = f i x`. This is `Pi.map` for `MulHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of AddHom's `f i : M i →ₙ+ N i` defines an AddHom
  `AddHom.piMap f : (Π i, M i) →ₙ+ (Π i, N i)`
  given by `AddHom.piMap f x i = f i x`. This is `Pi.map` for `AddHom`s. -/]
/-
**MulHom.piMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.piMap [Π i, Mul (M i)] [Π i, Mul (N i)] (g : Π i, M i ->ₙ* N i) : (
Π i, M i) ->ₙ* (Π i, N i)
参数：M i；N i；g : Π i, M i ->ₙ* N i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.piMap [Π i, Mul (M i)] [Π i, Mul (N i)] (g : Π i, M i →ₙ* N i) :
    (Π i, M i) →ₙ* (Π i, N i) :=
  .pi fun i ↦ (g i).comp (Pi.evalMulHom M i)

/-- `Function.const` as a `MulHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddHom`. -/]
/-
**Pi.constMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.constMulHom (α β : Type*) [Mul β] : β ->ₙ* α -> β where toFun
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` as a `MulHom`.
-/
def Pi.constMulHom (α β : Type*) [Mul β] :
    β →ₙ* α → β where
  toFun := Function.const α
  map_mul' _ _ := rfl

/-- Coercion of a `MulHom` into a function is itself a `MulHom`.

See also `MulHom.eval`. -/
@[to_additive (attr := simps) /-- Coercion of an `AddHom` into a function is itself an `AddHom`.

See also `AddHom.eval`. -/]
/-
**MulHom.coeFn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] : (α ->ₙ* β) ->ₙ* α -
> β where toFun g
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulHom.coeFn (α β : Type*) [Mul α] [CommSemigroup β] :
    (α →ₙ* β) →ₙ* α → β where
  toFun g := g
  map_mul' _ _ := rfl

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps) /-- Additive semigroup homomorphism between the function spaces
  `I → α` and `I → β`, induced by an additive semigroup homomorphism `f` between `α` and `β` -/]
/-
**MulHom.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：{α : Type u_5} → {β : Type u_6} → [inst : Mul α] → [inst_1 : Mul β] → (α →
ₙ* β) → (I : Type u_7) → (I → α) →ₙ* I → β
参数：α →ₙ* β；I : Type u_7；I → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def MulHom.compLeft {α β : Type*} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type*) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext; simp

end MulHom

section MonoidHom

variable [(i : I) → MulOneClass (f i)]

/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`Pi.monoidHom f : γ →* Π a, β a` given by `Pi.monoidHom f x b = f b x`. -/
@[to_additive (attr := simps)
  /-- A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid homomorphism
  `Pi.addMonoidHom f : γ →+ Π a, β a` given by `Pi.addMonoidHom f x b = f b x`. -/]
/-
**MonoidHom.pi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.pi {γ : Type w} [MulOneClass γ] (g : forall i, γ ->* f i) : γ ->
* forall i, f i
参数：g : forall i, γ ->* f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.pi {γ : Type w} [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  { MulHom.pi fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }

@[to_additive (attr := deprecated (since := "2026-05-29"))] alias Pi.monoidHom := MonoidHom.pi

@[to_additive (attr := deprecated (since := "2026-05-29"))]
alias Pi.monoidHom_apply := MonoidHom.pi_apply

@[to_additive]
/-
**MonoidHom.pi_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.pi_injective {γ : Type w} [Nonempty I] [MulOneClass γ] (g : fora
ll i, γ ->* f i) (hg : forall i, Function.Injective (g i)) : Function.Injective 
(MonoidHom.pi g)
参数：g : forall i, γ ->* f i；hg : forall i, Function.Injective (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.pi_injective`：MulHom.pi_injective {γ : Type w} [Nonempty I] [Mul 
γ] (g : forall i, γ ->ₙ* f i) (hg : forall i, Function.Injective (g i)) : Functi
on.Inject…
-/
theorem MonoidHom.pi_injective {γ : Type w} [Nonempty I] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
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
/-
**Pi.evalMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.evalMonoidHom (i : I) : (forall i, f i) ->* f i where toFun g
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' _ _ := Pi.mul_apply _ _ i

@[simp, norm_cast]
/-
**Pi.coe_evalMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.coe_evalMonoidHom (i : I) : ⇑(evalMonoidHom f i) = Function.eval i
参数：i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.coe_evalMonoidHom (i : I) : ⇑(evalMonoidHom f i) = Function.eval i := rfl

/-- A family of monoid homomorphisms `f i : M i →* N i` defines a monoid homomorphism
`MonoidHom.piMap f : (Π i, M i) →* (Π i, N i)`
given by `MonoidHom.piMap f x i = f i x`. This is `Pi.map` for `MonoidHom`s. -/
@[to_additive (attr := simps!)
  /-- A family of additive monoid homomorphisms `f i : M i →+ N i` defines an additive monoid
  homomorphism  `AddMonoidHom.piMap f : (Π i, M i) →+ (Π i, N i)`
  given by `AddMonoidHom.piMap f x i = f i x`. This is `Pi.map` for `AddMonoidHom`s. -/]
/-
**MonoidHom.piMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.piMap [Π i, MulOneClass (M i)] [Π i, MulOneClass (N i)] (g : Π i
, M i ->* N i) : (Π i, M i) ->* (Π i, N i)
参数：M i；N i；g : Π i, M i ->* N i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.piMap [Π i, MulOneClass (M i)] [Π i, MulOneClass (N i)] (g : Π i, M i →* N i) :
    (Π i, M i) →* (Π i, N i) :=
  .pi fun i ↦ (g i).comp (Pi.evalMonoidHom M i)

/-- `Function.const` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Function.const` as an `AddMonoidHom`. -/]
/-
**Pi.constMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β ->* α -> β where toFun
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` as a `MonoidHom`.
-/
def Pi.constMonoidHom (α β : Type*) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coercion of a `MonoidHom` into a function is itself a `MonoidHom`.

See also `MonoidHom.eval`. -/
@[to_additive (attr := simps) /-- Coercion of an `AddMonoidHom` into a function is itself
an `AddMonoidHom`.

See also `AddMonoidHom.eval`. -/]
/-
**MonoidHom.coeFn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α ->* β) -
>* α -> β where toFun g
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.coeFn (α β : Type*) [MulOneClass α] [CommMonoid β] : (α →* β) →* α → β where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive (attr := simps)
  /-- Additive monoid homomorphism between the function spaces `I → α` and `I → β`, induced by an
  additive monoid homomorphism `f` between `α` and `β` -/]
/-
**MonoidHom.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：{α : Type u_5} →   {β : Type u_6} → [inst : MulOneClass α] → [inst_1 : Mul
OneClass β] → (α →* β) → (I : Type u_7) → (I → α) →* I → β
参数：α →* β；I : Type u_7；I → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def MonoidHom.compLeft {α β : Type*} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type*) : (I → α) →* I → β where
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
nonrec def OneHom.mulSingle [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i) where
  toFun := mulSingle i
  map_one' := mulSingle_one i

@[to_additive (attr := simp)]
/-
**OneHom.mulSingle_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.mulSingle_apply [forall i, One <| f i] (i : I) (x : f i) : mulSingl
e f i x = Pi.mulSingle i x
参数：i : I；x : f i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.mulSingle_apply [∀ i, One <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OneHom.coe_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OneHom.coe_mulSingle [forall i, One <| f i] (i : I) : mulSingle f i = Pi.m
ulSingle (M
参数：i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OneHom.coe_mulSingle [∀ i, One <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

variable (f) in
/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `MonoidHom` version of `Pi.mulSingle`. -/
@[to_additive
  /-- The additive monoid homomorphism including a single additive monoid into a dependent family
  of additive monoids, as functions supported at a point.

  This is the `AddMonoidHom` version of `Pi.single`. -/]
/-
**MonoidHom.mulSingle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.mulSingle [forall i, MulOneClass <| f i] (i : I) : f i ->* foral
l i, f i
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.mulSingle [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.mulSingle f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }

@[to_additive (attr := simp)]
/-
**MonoidHom.mulSingle_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.mulSingle_apply [forall i, MulOneClass <| f i] (i : I) (x : f i)
 : mulSingle f i x = Pi.mulSingle i x
参数：i : I；x : f i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.mulSingle_apply [∀ i, MulOneClass <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MonoidHom.coe_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_mulSingle [forall i, MulOneClass <| f i] (i : I) : mulSingle
 f i = Pi.mulSingle (M
参数：i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidHom.coe_mulSingle [∀ i, MulOneClass <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

@[to_additive]
/-
**Pi.mulSingle_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_sup [forall i, SemilatticeSup (f i)] [forall i, One (f i)] (i
 : I) (x y : f i) : Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y
参数：f i；f i；i : I；x y : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_sup`：update_sup [forall i, SemilatticeSup (π i)] (f : fo
rall i, π i) (i : ι) (a b : π i) : update f i (a ⊔ b) = update f i a ⊔ update f 
i b
-/
theorem Pi.mulSingle_sup [∀ i, SemilatticeSup (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y :=
  Function.update_sup _ _ _ _

@[to_additive]
/-
**Pi.mulSingle_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_inf [forall i, SemilatticeInf (f i)] [forall i, One (f i)] (i
 : I) (x y : f i) : Pi.mulSingle i (x ⊓ y) = Pi.mulSingle i x ⊓ Pi.mulSingle i y
参数：f i；f i；i : I；x y : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_inf`：∀ {ι : Type u_1} {π : ι → Type u_2} [inst : Decidab
leEq ι] [inst_1 : (i : ι) → SemilatticeInf (π i)] (f : (i : ι) → π i)   (i : ι) 
(a b : π …
-/
theorem Pi.mulSingle_inf [∀ i, SemilatticeInf (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊓ y) = Pi.mulSingle i x ⊓ Pi.mulSingle i y :=
  Function.update_inf _ _ _ _

@[to_additive]
/-
**Pi.mulSingle_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_mul [forall i, MulOneClass <| f i] (i : I) (x y : f i) : mulS
ingle i (x * y) = mulSingle i x * mulSingle i y
参数：i : I；x y : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem Pi.mulSingle_mul [∀ i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.mulSingle f i).map_mul x y

@[to_additive]
/-
**Pi.mulSingle_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_inv [forall i, Group <| f i] (i : I) (x : f i) : mulSingle i 
x⁻¹ = (mulSingle i x)⁻¹
参数：i : I；x : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
theorem Pi.mulSingle_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.mulSingle f i).map_inv x

@[to_additive]
/-
**Pi.mulSingle_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_div [forall i, Group <| f i] (i : I) (x y : f i) : mulSingle 
i (x / y) = mulSingle i x / mulSingle i y
参数：i : I；x y : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_div`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
-/
theorem Pi.mulSingle_div [∀ i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.mulSingle f i).map_div x y

@[to_additive]
/-
**Pi.mulSingle_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_pow [forall i, Monoid (f i)] (i : I) (x : f i) (n : Nat) : mu
lSingle i (x ^ n) = mulSingle i x ^ n
参数：f i；i : I；x : f i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem Pi.mulSingle_pow [∀ i, Monoid (f i)] (i : I) (x : f i) (n : ℕ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_pow x n

@[to_additive]
/-
**Pi.mulSingle_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_zpow [forall i, Group (f i)] (i : I) (x : f i) (n : Int) : mu
lSingle i (x ^ n) = mulSingle i x ^ n
参数：f i；i : I；x : f i；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
-/
theorem Pi.mulSingle_zpow [∀ i, Group (f i)] (i : I) (x : f i) (n : ℤ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n :=
  (MonoidHom.mulSingle f i).map_zpow x n

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `Commute.map` -/
@[to_additive
  /-- The injection into an additive pi group at different indices commutes.

  For injections of commuting elements at the same index, see `AddCommute.map` -/]
/-
**Pi.mulSingle_commute** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_commute [forall i, MulOneClass <| f i] : Pairwise fun i j => 
forall (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Pi.mulSingle_eq_of_ne'`：mulSingle_eq_of_ne' {i i' : ι} (h : i != i') (x 
: M i) : mulSingle i x i' = 1
-/
theorem Pi.mulSingle_commute [∀ i, MulOneClass <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y; ext k
  by_cases i = k <;> simp_all

/-- The injection into a pi group with the same values commutes. -/
@[to_additive /-- The injection into an additive pi group with the same values commutes. -/]
/-
**Pi.mulSingle_apply_commute** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_apply_commute [forall i, MulOneClass <| f i] (x : forall i, f
 i) (i j : I) : Commute (mulSingle i (x i)) (mulSingle j (x j))
参数：x : forall i, f i；i j : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `Pi.mulSingle_commute`：Pi.mulSingle_commute [forall i, MulOneClass <| f i
] : Pairwise fun i j => forall (x : f i) (y : f j), Commute (mulSingle i x) (mul
Single j y…

--- 原说明 ---
The injection into a pi group with the same values commutes.
-/
theorem Pi.mulSingle_apply_commute [∀ i, MulOneClass <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _

@[to_additive]
/-
**Pi.update_eq_div_mul_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.update_eq_div_mul_mulSingle [forall i, Group <| f i] (g : forall i : I,
 f i) (x : f i) : Function.update g i x = g / mulSingle i (g i) * mulSingle i x
参数：g : forall i : I, f i；x : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Pi.update_eq_div_mul_mulSingle [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, eqComm]

@[to_additive]
/-
**Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMon
oid M] {k l m n : I} {u v : M} (hu : u != 1) (hv : v != 1) : (mulSingle k u : I 
-> M) * mulSingle l v = mulSingle m u * mulSingle n v ↔ k = m ∧ l = n ∨ u = v ∧ 
k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n
参数：hu : u != 1；hv : v != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.mulSingle_apply`：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingl
e i x : ι -> M) i' = if i' = i then x else 1
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type*} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    (mulSingle k u : I → M) * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := congr_fun h m
    have hn := congr_fun h n
    grind [mul_one, one_mul, mul_apply]
  · aesop (add simp [mulSingle_apply])

end Single

section
variable [∀ i, Mul <| f i]

@[to_additive]
/-
**SemiconjBy.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemiconjBy.pi {x y z : forall i, f i} (h : forall i, SemiconjBy (x i) (y i
) (z i)) : SemiconjBy x y z
参数：h : forall i, SemiconjBy (x i) (y i) (z i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem SemiconjBy.pi {x y z : ∀ i, f i} (h : ∀ i, SemiconjBy (x i) (y i) (z i)) :
    SemiconjBy x y z :=
  funext h

@[to_additive]
/-
**Pi.semiconjBy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.semiconjBy_iff {x y z : forall i, f i} : SemiconjBy x y z ↔ forall i, S
emiconjBy (x i) (y i) (z i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem Pi.semiconjBy_iff {x y z : ∀ i, f i} :
    SemiconjBy x y z ↔ ∀ i, SemiconjBy (x i) (y i) (z i) := funext_iff

@[to_additive]
/-
**Commute.pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.pi {x y : forall i, f i} (h : forall i, Commute (x i) (y i)) : Com
mute x y
参数：h : forall i, Commute (x i) (y i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.pi`：SemiconjBy.pi {x y z : forall i, f i} (h : forall i, Semi
conjBy (x i) (y i) (z i)) : SemiconjBy x y z
-/
theorem Commute.pi {x y : ∀ i, f i} (h : ∀ i, Commute (x i) (y i)) : Commute x y := SemiconjBy.pi h

@[to_additive]
/-
**Pi.commute_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.commute_iff {x y : forall i, f i} : Commute x y ↔ forall i, Commute (x 
i) (y i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.semiconjBy_iff`：Pi.semiconjBy_iff {x y z : forall i, f i} : SemiconjB
y x y z ↔ forall i, SemiconjBy (x i) (y i) (z i)
-/
theorem Pi.commute_iff {x y : ∀ i, f i} : Commute x y ↔ ∀ i, Commute (x i) (y i) := semiconjBy_iff

end

namespace Function

@[to_additive (attr := simp)]
/-
**Function.update_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_one [forall i, One (f i)] [DecidableEq I] (i : I) : update (1 : for
all i, f i) i 1 = 1
参数：f i；i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
-/
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i (1 : (a : I) → f a)

@[to_additive]
/-
**Function.update_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_mul [forall i, Mul (f i)] [DecidableEq I] (f₁ f₂ : forall i, f i) (
i : I) (x₁ : f i) (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * u
pdate f₂ i x₂
参数：f i；f₁ f₂ : forall i, f i；i : I；x₁ : f i；x₂ : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.apply_update₂`：apply_update₂ {ι : Sort*} [DecidableEq ι] {α β γ
 : ι -> Sort*} (f : forall i, α i -> β i -> γ i) (g : forall i, α i) (h : forall
 i, β i) (i …
-/
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
/-
**Function.update_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_inv [forall i, Inv (f i)] [DecidableEq I] (f₁ : forall i, f i) (i :
 I) (x₁ : f i) : update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹
参数：f i；f₁ : forall i, f i；i : I；x₁ : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.apply_update`：apply_update {ι : Sort*} [DecidableEq ι] {α β : ι
 -> Sort*} (f : forall i, α i -> β i) (g : forall i, α i) (i : ι) (v : α i) (j :
 ι) : f j (…
-/
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

@[to_additive]
/-
**Function.update_div** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_div [forall i, Div (f i)] [DecidableEq I] (f₁ f₂ : forall i, f i) (
i : I) (x₁ : f i) (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / u
pdate f₂ i x₂
参数：f i；f₁ f₂ : forall i, f i；i : I；x₁ : f i；x₂ : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.apply_update₂`：apply_update₂ {ι : Sort*} [DecidableEq ι] {α β γ
 : ι -> Sort*} (f : forall i, α i -> β i -> γ i) (g : forall i, α i) (h : forall
 i, β i) (i …
-/
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun _ => (· / ·)) f₁ f₂ i x₁ x₂ j).symm

variable [One α] [Nonempty ι] {a : α}

@[to_additive (attr := simp)]
/-
**Function.const_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_eq_one : const ι a = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.const_inj`：const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = co
nst α y₂ ↔ y₁ = y₂
-/
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1

@[to_additive]
/-
**Function.const_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_ne_one : const ι a != 1 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.const_eq_one`：const_eq_one : const ι a = 1 ↔ a = 1
-/
theorem const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 :=
  Iff.not const_eq_one

end Function

section Piecewise

@[to_additive]
/-
**Set.piecewise_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.piecewise_mul [forall i, Mul (f i)] (s : Set I) [forall i, Decidable (
i in s)] (f₁ f₂ g₁ g₂ : forall i, f i) : s.piecewise (f₁ * f₂) (g₁ * g₂) = s.pie
cewise f₁ g₁ * s.piecewise f₂ g₂
参数：f i；s : Set I；i in s；f₁ f₂ g₁ g₂ : forall i, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_op₂`：piecewise_op₂ {δ' δ'' : α -> Sort*} (f' g' : forall i
, δ' i) (h : forall i, δ i -> δ' i -> δ'' i) : (s.piecewise (fun x => h x (f x) 
(f' x))…
-/
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

@[to_additive]
/-
**Set.piecewise_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.piecewise_inv [forall i, Inv (f i)] (s : Set I) [forall i, Decidable (
i in s)] (f₁ g₁ : forall i, f i) : s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹
参数：f i；s : Set I；i in s；f₁ g₁ : forall i, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_op`：piecewise_op {δ' : α -> Sort*} (h : forall i, δ i -> δ
' i) : (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.p
iecewi…
-/
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]
/-
**Set.piecewise_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.piecewise_div [forall i, Div (f i)] (s : Set I) [forall i, Decidable (
i in s)] (f₁ f₂ g₁ g₂ : forall i, f i) : s.piecewise (f₁ / f₂) (g₁ / g₂) = s.pie
cewise f₁ g₁ / s.piecewise f₂ g₂
参数：f i；s : Set I；i in s；f₁ f₂ g₁ g₂ : forall i, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_op₂`：piecewise_op₂ {δ' δ'' : α -> Sort*} (f' g' : forall i
, δ' i) (h : forall i, δ i -> δ' i -> δ'' i) : (s.piecewise (fun x => h x (f x) 
(f' x))…
-/
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ f₁ _ _ _ fun _ => (· / ·)

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι → η)

/-- `Function.extend s f 1` as a bundled hom. -/
@[to_additive (attr := simps) Function.ExtendByZero.hom
/-- `Function.extend s f 0` as a bundled hom. -/]
/-
**Function.ExtendByOne.hom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.ExtendByOne.hom [MulOneClass R] : (ι -> R) ->* η -> R where toFun
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def Function.ExtendByOne.hom [MulOneClass R] :
    (ι → R) →* η → R where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1

end Extend

namespace Pi

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

@[to_additive]
/-
**Pi.mulSingle_mono** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：mulSingle_mono : Monotone (Pi.mulSingle i : f i -> forall i, f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_mono`：update_mono : Monotone (update f i)
-/
theorem mulSingle_mono : Monotone (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_mono

@[to_additive]
/-
**Pi.mulSingle_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i -> forall i, f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_strictMono`：update_strictMono : StrictMono (update f i)
-/
theorem mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i → ∀ i, f i) :=
  Function.update_strictMono

@[to_additive]
/-
**Pi.mulSingle_comp_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_comp_equiv {m n : Type*} [DecidableEq n] [DecidableEq m] [One α]
 (σ : n ≃ m) (i : m) (x : α) : Pi.mulSingle i x ∘ σ = Pi.mulSingle (σ.symm i) x
参数：σ : n ≃ m；i : m；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_apply`：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingl
e i x : ι -> M) i' = if i' = i then x else 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma mulSingle_comp_equiv {m n : Type*} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
    (i : m) (x : α) : Pi.mulSingle i x ∘ σ = Pi.mulSingle (σ.symm i) x := by
  ext x
  aesop (add simp Pi.mulSingle_apply)

end Pi

namespace Sigma

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

@[to_additive (attr := simp)]
/-
**Sigma.curry_one** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：curry_one [forall a b, One (γ a b)] : Sigma.curry (1 : (i : Σ a, β a) -> γ
 i.1 i.2) = 1
参数：γ a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_one [∀ a b, One (γ a b)] : Sigma.curry (1 : (i : Σ a, β a) → γ i.1 i.2) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.uncurry_one** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：uncurry_one [forall a b, One (γ a b)] : Sigma.uncurry (1 : forall a b, γ a
 b) = 1
参数：γ a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_one [∀ a b, One (γ a b)] : Sigma.uncurry (1 : ∀ a b, γ a b) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.curry_mul** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：curry_mul [forall a b, Mul (γ a b)] (x y : (i : Σ a, β a) -> γ i.1 i.2) : 
Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y
参数：γ a b；x y : (i : Σ a, β a) -> γ i.1 i.2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_mul [∀ a b, Mul (γ a b)] (x y : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.uncurry_mul** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：uncurry_mul [forall a b, Mul (γ a b)] (x y : forall a b, γ a b) : Sigma.un
curry (x * y) = Sigma.uncurry x * Sigma.uncurry y
参数：γ a b；x y : forall a b, γ a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_mul [∀ a b, Mul (γ a b)] (x y : ∀ a b, γ a b) :
    Sigma.uncurry (x * y) = Sigma.uncurry x * Sigma.uncurry y :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.curry_inv** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：curry_inv [forall a b, Inv (γ a b)] (x : (i : Σ a, β a) -> γ i.1 i.2) : Si
gma.curry (x⁻¹) = (Sigma.curry x)⁻¹
参数：γ a b；x : (i : Σ a, β a) -> γ i.1 i.2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_inv [∀ a b, Inv (γ a b)] (x : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x⁻¹) = (Sigma.curry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.uncurry_inv** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：uncurry_inv [forall a b, Inv (γ a b)] (x : forall a b, γ a b) : Sigma.uncu
rry (x⁻¹) = (Sigma.uncurry x)⁻¹
参数：γ a b；x : forall a b, γ a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_inv [∀ a b, Inv (γ a b)] (x : ∀ a b, γ a b) :
    Sigma.uncurry (x⁻¹) = (Sigma.uncurry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.curry_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：curry_mulSingle [DecidableEq α] [forall a, DecidableEq (β a)] [forall a b,
 One (γ a b)] (i : Σ a, β a) (x : γ i.1 i.2) : Sigma.curry (Pi.mulSingle i x) = 
Pi.mulSingle i.1 (Pi.mulSingle i.2 x)
参数：β a；γ a b；i : Σ a, β a；x : γ i.1 i.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.curry_update`：Sigma.curry_update {γ : forall a, β a -> Type*} [Dec
idableEq α] [forall a, DecidableEq (β a)] (i : Σ a, β a) (f : (i : Σ a, β a) -> 
γ i.1 i.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curry_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (i : Σ a, β a) (x : γ i.1 i.2) :
    Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x) := by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

@[to_additive (attr := simp)]
/-
**Sigma.uncurry_mulSingle_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：uncurry_mulSingle_mulSingle [DecidableEq α] [forall a, DecidableEq (β a)] 
[forall a b, One (γ a b)] (a : α) (b : β a) (x : γ a b) : Sigma.uncurry (Pi.mulS
ingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x
参数：β a；γ a b；a : α；b : β a；x : γ a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sigma.curry_mulSingle`：curry_mulSingle [DecidableEq α] [forall a, Decida
bleEq (β a)] [forall a b, One (γ a b)] (i : Σ a, β a) (x : γ i.1 i.2) : Sigma.cu
rry (Pi.mul…
· 使用定理 `Sigma.uncurry_curry`：Sigma.uncurry_curry {γ : forall a, β a -> Type*} (f
 : forall x : Sigma β, γ x.1 x.2) : Sigma.uncurry (Sigma.curry f) = f
-/
theorem uncurry_mulSingle_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (a : α) (b : β a) (x : γ a b) :
    Sigma.uncurry (Pi.mulSingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x := by
  rw [← curry_mulSingle ⟨a, b⟩, uncurry_curry]

end Sigma

