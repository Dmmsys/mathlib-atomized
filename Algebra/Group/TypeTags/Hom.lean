/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Transport algebra morphisms between additive and multiplicative types.
-/

@[expose] public section

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

variable {M N α β : Type*}

/-- Reinterpret `α →+ β` as `Multiplicative α →* Multiplicative β`. -/
@[simps]
/-
**AddMonoidHom.toMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] : (α ->+ β
) ≃ (Multiplicative α ->* Multiplicative β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `α →+ β` as `Multiplicative α →* Multiplicative β`.
-/
def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α →+ β) ≃ (Multiplicative α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f a.toAdd)
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => f (ofAdd a) |>.toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
/-
**AddMonoidHom.coe_toMultiplicative** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.coe_toMultiplicative [AddZeroClass α] [AddZeroClass β] (f : α
 ->+ β) : ⇑(toMultiplicative f) = ofAdd ∘ f ∘ toAdd
参数：f : α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddMonoidHom.coe_toMultiplicative [AddZeroClass α] [AddZeroClass β] (f : α →+ β) :
    ⇑(toMultiplicative f) = ofAdd ∘ f ∘ toAdd := rfl

@[simp]
/-
**AddMonoidHom.toMultiplicative_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicative_id [AddZeroClass α] : (id α).toMultiplicativ
e = .id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddMonoidHom.toMultiplicative_id [AddZeroClass α] : (id α).toMultiplicative = .id _ := rfl

/-- Reinterpret `α →* β` as `Additive α →+ Additive β`. -/
@[simps]
/-
**MonoidHom.toAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] : (α ->* β) ≃ (Additi
ve α ->+ Additive β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `α →* β` as `Additive α →+ Additive β`.
-/
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃ (Additive α →+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f a.toMul)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => (f (ofMul a)).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }

@[simp, norm_cast]
/-
**MonoidHom.coe_toAdditive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_toAdditive [MulOneClass α] [MulOneClass β] (f : α ->* β) : ⇑
(toAdditive f) = ofMul ∘ f ∘ toMul
参数：f : α ->* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonoidHom.coe_toAdditive [MulOneClass α] [MulOneClass β] (f : α →* β) :
    ⇑(toAdditive f) = ofMul ∘ f ∘ toMul := rfl
/-
**MonoidHom.toAdditive_id** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_3} [inst : MulOneClass α], MonoidHom.toAdditive (MonoidHom.i
d α) = AddMonoidHom.id (Additive α)
参数：MonoidHom.id α；Additive α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma MonoidHom.toAdditive_id [MulOneClass α] : (id α).toAdditive = .id _ := rfl

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
/-
**AddMonoidHom.toMultiplicativeRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicativeRight [MulOneClass α] [AddZeroClass β] : (Add
itive α ->+ β) ≃ (α ->* Multiplicative β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `Additive α →+ β` as `α →* Multiplicative β`.
-/
def AddMonoidHom.toMultiplicativeRight [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => (f a.toMul).toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
/-
**AddMonoidHom.coe_toMultiplicativeRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.coe_toMultiplicativeRight [MulOneClass α] [AddZeroClass β] (f
 : Additive α ->+ β) : ⇑(toMultiplicativeRight f) = ofAdd ∘ f ∘ ofMul
参数：f : Additive α ->+ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddMonoidHom.coe_toMultiplicativeRight [MulOneClass α] [AddZeroClass β]
    (f : Additive α →+ β) : ⇑(toMultiplicativeRight f) = ofAdd ∘ f ∘ ofMul := rfl

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps!]
/-
**MonoidHom.toAdditiveLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toAdditiveLeft [MulOneClass α] [AddZeroClass β] : (α ->* Multipl
icative β) ≃ (Additive α ->+ β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `α →* Multiplicative β` as `Additive α →+ β`.
-/
def MonoidHom.toAdditiveLeft [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicativeRight.symm

@[simp, norm_cast]
/-
**MonoidHom.coe_toAdditiveLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_toAdditiveLeft [MulOneClass α] [AddZeroClass β] (f : α ->* M
ultiplicative β) : ⇑(toAdditiveLeft f) = toAdd ∘ f ∘ toMul
参数：f : α ->* Multiplicative β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonoidHom.coe_toAdditiveLeft [MulOneClass α] [AddZeroClass β] (f : α →* Multiplicative β) :
    ⇑(toAdditiveLeft f) = toAdd ∘ f ∘ toMul := rfl

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
/-
**AddMonoidHom.toMultiplicativeLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] : (α ->
+ Additive β) ≃ (Multiplicative α ->* β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `α →+ Additive β` as `Multiplicative α →* β`.
-/
def AddMonoidHom.toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun f := {
    toFun := fun a => (f a.toAdd).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
/-
**AddMonoidHom.coe_toMultiplicativeLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.coe_toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] (f 
: α ->+ Additive β) : ⇑(toMultiplicativeLeft f) = toMul ∘ f ∘ toAdd
参数：f : α ->+ Additive β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddMonoidHom.coe_toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] (f : α →+ Additive β) :
    ⇑(toMultiplicativeLeft f) = toMul ∘ f ∘ toAdd := rfl

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps!]
/-
**MonoidHom.toAdditiveRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toAdditiveRight [AddZeroClass α] [MulOneClass β] : (Multiplicati
ve α ->* β) ≃ (α ->+ Additive β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `Multiplicative α →* β` as `α →+ Additive β`.
-/
def MonoidHom.toAdditiveRight [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicativeLeft.symm

@[simp, norm_cast]
/-
**MonoidHom.coe_toAdditiveRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_toAdditiveRight [AddZeroClass α] [MulOneClass β] (f : Multip
licative α ->* β) : ⇑(toAdditiveRight f) = ofMul ∘ f ∘ ofAdd
参数：f : Multiplicative α ->* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonoidHom.coe_toAdditiveRight [AddZeroClass α] [MulOneClass β] (f : Multiplicative α →* β) :
    ⇑(toAdditiveRight f) = ofMul ∘ f ∘ ofAdd := rfl

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
/-
**proving** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma proving equality in `α →+ Additive β` from equality in `Multiplicative α →* β`. -/
@[ext]
/-
**Multiplicative.monoidHom_ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β] (f g : Multi
plicative α ->* β) (h : f.toAdditiveRight = g.toAdditiveRight) : f = g
参数：f g : Multiplicative α ->* β；h : f.toAdditiveRight = g.toAdditiveRight。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
This ext lemma moves the type tag to the codomain, since most ext lemmas act on 
the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally add
s the inverse ext
lemma proving equality in `α →+ Additive β` from equality in `Multiplicative α →
* β`.
-/
lemma Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β]
    (f g : Multiplicative α →* β) (h : f.toAdditiveRight = g.toAdditiveRight) : f = g :=
  MonoidHom.toAdditiveRight.injective h

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
/-
**proving** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma proving equality in `α →* Multiplicative β` from equality in `Additive α →+ β`. -/
@[ext]
/-
**Additive.addMonoidHom_ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β] (f g : Additive
 α ->+ β) (h : f.toMultiplicativeRight = g.toMultiplicativeRight) : f = g
参数：f g : Additive α ->+ β；h : f.toMultiplicativeRight = g.toMultiplicativeRight。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
This ext lemma moves the type tag to the codomain, since most ext lemmas act on 
the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally add
s the inverse ext
lemma proving equality in `α →* Multiplicative β` from equality in `Additive α →
+ β`.
-/
lemma Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β]
    (f g : Additive α →+ β) (h : f.toMultiplicativeRight = g.toMultiplicativeRight) : f = g :=
  AddMonoidHom.toMultiplicativeRight.injective h

section AddCommMonoid
variable [AddMonoid M] [AddCommMonoid N]

@[simp]
/-
**AddMonoidHom.toMultiplicative_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicative_add (f g : M ->+ N) : (f + g).toMultiplicati
ve = f.toMultiplicative * g.toMultiplicative
参数：f g : M ->+ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AddMonoidHom.toMultiplicative_add (f g : M →+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl

end AddCommMonoid

/-- `AddMonoidHom.toMultiplicativeLeft` as an `AddEquiv`. -/
/-
**AddMonoidHom.toMultiplicativeLeftAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicativeLeftAddEquiv [AddMonoid M] [CommMonoid N] : (
M ->+ Additive N) ≃+ Additive (Multiplicative M ->* N) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`AddMonoidHom.toMultiplicativeLeft` as an `AddEquiv`.
-/
def AddMonoidHom.toMultiplicativeLeftAddEquiv [AddMonoid M] [CommMonoid N] :
    (M →+ Additive N) ≃+ Additive (Multiplicative M →* N) where
  toEquiv := AddMonoidHom.toMultiplicativeLeft.trans Additive.ofMul
  map_add' _ _ := rfl

/-- `AddMonoidHom.toMultiplicativeRight` as an `AddEquiv`. -/
/-
**AddMonoidHom.toMultiplicativeRightAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toMultiplicativeRightAddEquiv [Monoid M] [AddCommMonoid N] : 
(Additive M ->+ N) ≃+ Additive (M ->* Multiplicative N) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`AddMonoidHom.toMultiplicativeRight` as an `AddEquiv`.
-/
def AddMonoidHom.toMultiplicativeRightAddEquiv [Monoid M] [AddCommMonoid N] :
    (Additive M →+ N) ≃+ Additive (M →* Multiplicative N) where
  toEquiv := AddMonoidHom.toMultiplicativeRight.trans Additive.ofMul
  map_add' _ _ := rfl

/-- `MonoidHom.toAdditiveLeft` as a `MulEquiv`. -/
/-
**MonoidHom.toAdditiveLeftMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toAdditiveLeftMulEquiv [Monoid M] [AddCommMonoid N] : (M ->* Mul
tiplicative N) ≃* Multiplicative (Additive M ->+ N) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`MonoidHom.toAdditiveLeft` as a `MulEquiv`.
-/
def MonoidHom.toAdditiveLeftMulEquiv [Monoid M] [AddCommMonoid N] :
    (M →* Multiplicative N) ≃* Multiplicative (Additive M →+ N) where
  toEquiv := MonoidHom.toAdditiveLeft.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

/-- `MonoidHom.toAdditiveRight` as a `MulEquiv`. -/
/-
**MonoidHom.toAdditiveRightMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toAdditiveRightMulEquiv [AddMonoid M] [CommMonoid N] : (Multipli
cative M ->* N) ≃* Multiplicative (M ->+ Additive N) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`MonoidHom.toAdditiveRight` as a `MulEquiv`.
-/
def MonoidHom.toAdditiveRightMulEquiv [AddMonoid M] [CommMonoid N] :
    (Multiplicative M →* N) ≃* Multiplicative (M →+ Additive N) where
  toEquiv := MonoidHom.toAdditiveRight.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl
