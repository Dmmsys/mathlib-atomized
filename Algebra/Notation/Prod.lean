/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Data.Prod.Basic

/-!
# Arithmetic operators on (pairwise) product types

This file provides only the notation for (componentwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on
(pairwise) product types. See `Mathlib/Algebra/Group/Prod.lean` for the `Monoid` and `Group`
instances. There is also an instance of the `Star` notation typeclass, but no default notation is
included.

-/

@[expose] public section

assert_not_exists Monoid DenselyOrdered

variable {G H M N P R S : Type*}

namespace Prod

section One

variable [One M] [One N]

@[to_additive]
/-
**Prod.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instOne : One (M × N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (M × N) :=
  ⟨(1, 1)⟩

@[to_additive (attr := simp)]
/-
**Prod.fst_one** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_one : (1 : M × N).1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_one : (1 : M × N).1 = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**Prod.snd_one** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_one : (1 : M × N).2 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_one : (1 : M × N).2 = 1 :=
  rfl

@[to_additive]
/-
**Prod.one_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：one_eq_mk : (1 : M × N) = (1, 1)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq_mk : (1 : M × N) = (1, 1) :=
  rfl

@[to_additive]
/-
**Prod.mk_one_one** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_one_one : ((1 : M), (1 : N)) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one_one : ((1 : M), (1 : N)) = 1 := rfl

@[to_additive (attr := simp)]
/-
**Prod.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_eq_one {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
-/
theorem mk_eq_one {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 := mk_inj

@[to_additive (attr := simp)]
/-
**Prod.swap_one** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_one : (1 : M × N).swap = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_one : (1 : M × N).swap = 1 :=
  rfl

end One

section Mul

variable {M N : Type*} [Mul M] [Mul N]

@[to_additive]
/-
**Prod.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMul : Mul (M × N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
/-
**Prod.fst_mul** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_mul (p q : M × N) : (p * q).1 = p.1 * q.1
参数：p q : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_mul (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl

@[to_additive (attr := simp)]
/-
**Prod.snd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2
参数：p q : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl

@[to_additive (attr := simp)]
/-
**Prod.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b
₂)
参数：a₁ a₂ : M；b₁ b₂ : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

@[to_additive (attr := simp)]
/-
**Prod.swap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_mul (p q : M × N) : (p * q).swap = p.swap * q.swap
参数：p q : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_mul (p q : M × N) : (p * q).swap = p.swap * q.swap := rfl

@[to_additive]
/-
**Prod.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2)
参数：p q : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) := rfl

end Mul

section Inv

variable {G H : Type*} [Inv G] [Inv H]

@[to_additive]
/-
**Prod.instInv** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instInv : Inv (G × H)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv (G × H) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]
/-
**Prod.fst_inv** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_inv (p : G × H) : p⁻¹.1 = p.1⁻¹
参数：p : G × H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_inv (p : G × H) : p⁻¹.1 = p.1⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**Prod.snd_inv** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_inv (p : G × H) : p⁻¹.2 = p.2⁻¹
参数：p : G × H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_inv (p : G × H) : p⁻¹.2 = p.2⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**Prod.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：inv_mk (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹)
参数：a : G；b : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

@[to_additive (attr := simp)]
/-
**Prod.swap_inv** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_inv (p : G × H) : p⁻¹.swap = p.swap⁻¹
参数：p : G × H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_inv (p : G × H) : p⁻¹.swap = p.swap⁻¹ := rfl

end Inv

section Div

variable {G H : Type*} [Div G] [Div H]

@[to_additive]
/-
**Prod.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instDiv : Div (G × H)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv : Div (G × H) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]
/-
**Prod.fst_div** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_div (a b : G × H) : (a / b).1 = a.1 / b.1
参数：a b : G × H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_div (a b : G × H) : (a / b).1 = a.1 / b.1 := rfl

@[to_additive (attr := simp)]
/-
**Prod.snd_div** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_div (a b : G × H) : (a / b).2 = a.2 / b.2
参数：a b : G × H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_div (a b : G × H) : (a / b).2 = a.2 / b.2 := rfl

@[to_additive (attr := simp)]
/-
**Prod.mk_div_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_div_mk (x₁ x₂ : G) (y₁ y₂ : H) : (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y
₂)
参数：x₁ x₂ : G；y₁ y₂ : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_div_mk (x₁ x₂ : G) (y₁ y₂ : H) : (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) := rfl

@[to_additive (attr := simp)]
/-
**Prod.swap_div** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_div (a b : G × H) : (a / b).swap = a.swap / b.swap
参数：a b : G × H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_div (a b : G × H) : (a / b).swap = a.swap / b.swap := rfl
/-
**Prod.div_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {G : Type u_8} {H : Type u_9} [inst : Div G] [inst_1 : Div H] (a b : G ×
 H), a / b = (a.1 / b.1, a.2 / b.2)
参数：a b : G × H；a.1 / b.1, a.2 / b.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma div_def (a b : G × H) : a / b = (a.1 / b.1, a.2 / b.2) := rfl

end Div

section Pow

variable {E α β : Type*} [Pow α E] [Pow β E]

@[to_additive (attr := to_additive) instSMul]
/-
**Prod.instPow** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instPow : Pow (α × β) E where pow p c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_fst]
/-
**Prod.pow_fst** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c
参数：p : α × β；c : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c := rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_snd]
/-
**Prod.pow_snd** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c
参数：p : α × β；c : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c := rfl

@[to_additive (attr := to_additive, simp) (reorder := a b c) smul_mk]
/-
**Prod.pow_mk** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：pow_mk (a : α) (b : β) (c : E) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c)
参数：a : α；b : β；c : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_mk (a : α) (b : β) (c : E) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) := rfl

@[to_additive (attr := to_additive) (reorder := p c) smul_def]
/-
**Prod.pow_def** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c)
参数：p : α × β；c : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) := rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_swap]
/-
**Prod.pow_swap** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c
参数：p : α × β；c : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c := rfl

end Pow

section Star

variable [Star R] [Star S]

/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (R × S) where star x := (star x.1, star x.2)

@[simp]
/-
**Prod.fst_star** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_star (x : R × S) : (star x).1 = star x.1
参数：x : R × S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_star (x : R × S) : (star x).1 = star x.1 := rfl

@[simp]
/-
**Prod.snd_star** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_star (x : R × S) : (star x).2 = star x.2
参数：x : R × S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_star (x : R × S) : (star x).2 = star x.2 := rfl
/-
**Prod.star_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：star_def (x : R × S) : star x = (star x.1, star x.2)
参数：x : R × S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_def (x : R × S) : star x = (star x.1, star x.2) := rfl

end Star


end Prod

