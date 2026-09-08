/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Tactic.Push.Attr
public import Mathlib.Logic.Function.Defs
public import Batteries.Tactic.Alias

/-!
# Notation for algebraic operators on pi types

This file provides only the notation for (pointwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on pi types.
See `Mathlib/Algebra/Group/Pi/Basic.lean` for the `Monoid` and `Group` instances. There is also
an instance of the `Star` notation typeclass, but no default notation is included.
-/

@[expose] public section

assert_not_exists Set.range Monoid Preorder

open Function

variable {ι α β : Type*} {G M R : ι → Type*}

namespace Pi

@[deprecated (since := "2026-04-21")]
alias prod := Function.prod

@[deprecated (since := "2026-04-21")]
alias prod_fst_snd := Function.prod_fst_snd

@[deprecated (since := "2026-04-21")]
alias prod_snd_fst := Function.prod_snd_fst

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/

section One
variable [∀ i, One (M i)]

@[to_additive]
/-
**Pi.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instOne : One (forall i, M i) where one _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (∀ i, M i) where one _ := 1

@[to_additive (attr := simp high)]
/-
**Pi.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：one_apply (i : ι) : (1 : forall i, M i) i = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply (i : ι) : (1 : ∀ i, M i) i = 1 := rfl

@[to_additive (attr := push ← high)]
/-
**Pi.one_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：one_def : (1 : forall i, M i) = fun _ => 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : ∀ i, M i) = fun _ ↦ 1 := rfl

variable {M : Type*} [One M]
/-
**Pi._root_.Function.const_one** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma _root_.Function.const_one : const α (1 : M) = 1 := rfl
/-
**Pi.one_comp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {M : Type u_7} [inst : One M] (f : α → β),
 1 ∘ f = 1
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma one_comp (f : α → β) : (1 : β → M) ∘ f = 1 := rfl
/-
**Pi.comp_one** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {M : Type u_7} [inst : One M] (f : M → β),
 f ∘ 1 = Function.const α (f 1)
参数：f : M → β；f 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma comp_one (f : M → β) : f ∘ (1 : α → M) = const α (f 1) := rfl

end One

section Mul
variable [∀ i, Mul (M i)]

@[to_additive]
/-
**Pi.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instMul : Mul (forall i, M i) where mul f g i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (∀ i, M i) where mul f g i := f i * g i

@[to_additive (attr := simp)]
/-
**Pi.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i * g i
参数：f g : forall i, M i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl

@[to_additive (attr := push ←)]
/-
**Pi.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mul_def (f g : forall i, M i) : f * g = fun i => f i * g i
参数：f g : forall i, M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : ∀ i, M i) : f * g = fun i ↦ f i * g i := rfl

variable {M : Type*} [Mul M]

@[to_additive (attr := simp)]
/-
**Pi._root_.Function.const_mul** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.const_mul (a b : M) : const ι a * const ι b = const ι (a * b) := rfl

@[to_additive]
/-
**Pi.mul_comp** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mul_comp (f g : β -> M) (z : α -> β) : (f * g) ∘ z = f ∘ z * g ∘ z
参数：f g : β -> M；z : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_comp (f g : β → M) (z : α → β) : (f * g) ∘ z = f ∘ z * g ∘ z := rfl

end Mul

section Inv
variable [∀ i, Inv (G i)]

@[to_additive]
/-
**Pi.instInv** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instInv : Inv (forall i, G i) where inv f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv (∀ i, G i) where inv f i := (f i)⁻¹

@[to_additive (attr := simp)]
/-
**Pi.inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹
参数：f : forall i, G i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_apply (f : ∀ i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹ := rfl

@[to_additive (attr := push ←)]
/-
**Pi.inv_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：inv_def (f : forall i, G i) : f⁻¹ = fun i => (f i)⁻¹
参数：f : forall i, G i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_def (f : ∀ i, G i) : f⁻¹ = fun i ↦ (f i)⁻¹ := rfl

variable {G : Type*} [Inv G]

@[to_additive]
/-
**Pi._root_.Function.const_inv** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.const_inv (a : G) : (const ι a)⁻¹ = const ι a⁻¹ := rfl

@[to_additive]
/-
**Pi.inv_comp** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：inv_comp (f : β -> G) (g : α -> β) : f⁻¹ ∘ g = (f ∘ g)⁻¹
参数：f : β -> G；g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_comp (f : β → G) (g : α → β) : f⁻¹ ∘ g = (f ∘ g)⁻¹ := rfl
end Inv

section Div
variable [∀ i, Div (G i)]

@[to_additive]
/-
**Pi.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instDiv : Div (forall i, G i) where div f g i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv : Div (∀ i, G i) where div f g i := f i / g i

@[to_additive (attr := simp)]
/-
**Pi.div_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i / g i
参数：f g : forall i, G i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_apply (f g : ∀ i, G i) (i : ι) : (f / g) i = f i / g i := rfl

@[to_additive (attr := push ←)]
/-
**Pi.div_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：div_def (f g : forall i, G i) : f / g = fun i => f i / g i
参数：f g : forall i, G i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_def (f g : ∀ i, G i) : f / g = fun i ↦ f i / g i := rfl

variable {G : Type*} [Div G]

@[to_additive]
/-
**Pi.div_comp** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：div_comp (f g : β -> G) (z : α -> β) : (f / g) ∘ z = f ∘ z / g ∘ z
参数：f g : β -> G；z : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_comp (f g : β → G) (z : α → β) : (f / g) ∘ z = f ∘ z / g ∘ z := rfl

@[to_additive (attr := simp)]
/-
**Pi._root_.Function.const_div** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.const_div (a b : G) : const ι a / const ι b = const ι (a / b) := rfl

end Div

section Pow

variable [∀ i, Pow (M i) α]

@[to_additive (attr := to_additive) instSMul]
/-
**Pi.instPow** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instPow : Pow (forall i, M i) α where pow f a i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow : Pow (∀ i, M i) α where pow f a i := f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
/-
**Pi.pow_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：pow_apply (f : forall i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a
参数：f : forall i, M i；a : α；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_apply (f : ∀ i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a := rfl

@[to_additive (attr := push ←, to_additive) (reorder := 5 6) smul_def]
/-
**Pi.pow_def** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：pow_def (f : forall i, M i) (a : α) : f ^ a = fun i => f i ^ a
参数：f : forall i, M i；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_def (f : ∀ i, M i) (a : α) : f ^ a = fun i ↦ f i ^ a := rfl

variable {M : Type*} [Pow M α]

@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
/-
**Pi._root_.Function.const_pow** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.const_pow (a : M) (b : α) : const ι a ^ b = const ι (a ^ b) := rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
/-
**Pi.pow_comp** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：pow_comp (f : β -> M) (a : α) (g : ι -> β) : (f ^ a) ∘ g = f ∘ g ^ a
参数：f : β -> M；a : α；g : ι -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_comp (f : β → M) (a : α) (g : ι → β) : (f ^ a) ∘ g = f ∘ g ^ a := rfl

end Pow

section Star

variable [∀ i, Star (R i)]

/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (∀ i, R i) where star x i := star (x i)

@[simp]
/-
**Pi.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：star_apply (x : forall i, R i) (i : ι) : star x i = star (x i)
参数：x : forall i, R i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_apply (x : ∀ i, R i) (i : ι) : star x i = star (x i) := rfl

@[push ←]
/-
**Pi.star_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：star_def (x : forall i, R i) : star x = fun i => star (x i)
参数：x : forall i, R i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_def (x : ∀ i, R i) : star x = fun i => star (x i) := rfl

end Star

end Pi

