/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Uniquely Decodable Codes

This file defines uniquely decodable codes and proves basic properties.

## Main definitions

* `UniquelyDecodable`: A set of codewords is uniquely decodable if distinct concatenations
  of codewords yield distinct strings.

## Main results

* `UniquelyDecodable.epsilon_not_mem`: Uniquely decodable codes cannot contain the empty
  string.
* `UniquelyDecodable.flatten_injective`: The flatten function is injective on lists of
  codewords from a uniquely decodable code.
-/

@[expose] public section

namespace InformationTheory

variable {α : Type*}

/-- A set of lists is uniquely decodable if distinct concatenations yield distinct strings. -/
/-
**InformationTheory.UniquelyDecodable** 是 Mathlib 中的一个定义，位于命名空间 `InformationTheo
ry`。
形式化陈述：UniquelyDecodable (S : Set (List α)) : Prop
参数：S : Set (List α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of lists is uniquely decodable if distinct concatenations yield distinct s
trings.
-/
def UniquelyDecodable (S : Set (List α)) : Prop :=
  ∀ (L₁ L₂ : List (List α)),
    (∀ w ∈ L₁, w ∈ S) → (∀ w ∈ L₂, w ∈ S) →
    L₁.flatten = L₂.flatten → L₁ = L₂

variable {S : Set (List α)}

/-- If a code is uniquely decodable, it does not contain the empty string.

The empty string can be "decoded" as either zero or two copies of itself,
violating unique decodability. -/
/-
**InformationTheory.UniquelyDecodable.epsilon_not_mem** 是 Mathlib 中的一个定理，位于命名空间 
`InformationTheory.UniquelyDecodable`。
形式化陈述：∀ {α : Type u_1} {S : Set (List α)}, InformationTheory.UniquelyDecodable S
 → [] ∉ S
参数：List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If a code is uniquely decodable, it does not contain the empty string.

The empty string can be "decoded" as either zero or two copies of itself,
violating unique decodability.
-/
lemma UniquelyDecodable.epsilon_not_mem
    (h : UniquelyDecodable S) :
    [] ∉ S := by
  simpa using h [[]] [[], []]
/-
**InformationTheory.UniquelyDecodable.flatten_injective** 是 Mathlib 中的一个定理，位于命名空
间 `InformationTheory.UniquelyDecodable`。
形式化陈述：∀ {α : Type u_1} {S : Set (List α)}, InformationTheory.UniquelyDecodable S
 → Function.Injective fun L => (↑L).flatten
参数：List α；↑L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma UniquelyDecodable.flatten_injective (h : UniquelyDecodable S) :
    Function.Injective (fun (L : {L : List (List α) // ∀ x ∈ L, x ∈ S}) => L.val.flatten) := by
  intro L₁ L₂ hflat
  apply Subtype.ext
  exact h L₁.val L₂.val L₁.prop L₂.prop hflat

end InformationTheory

