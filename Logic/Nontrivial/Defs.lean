/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Tactic.Push.Attr

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `Nontrivial` formalizing this property.

Basic results about nontrivial types are in `Mathlib/Logic/Nontrivial/Basic.lean`.
-/

public section

variable {α : Type*} {β : Type*}

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
/-
**Nontrivial** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate typeclass for expressing that a type is not reduced to a single elemen
t. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive 
dimension.
-/
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y
/-
**nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
-/
theorem nontrivial_iff : Nontrivial α ↔ ∃ x y : α, x ≠ y :=
  ⟨fun h ↦ h.exists_pair_ne, fun h ↦ ⟨h⟩⟩
/-
**exists_pair_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y : α, x != y
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
-/
theorem exists_pair_ne (α : Type*) [Nontrivial α] : ∃ x y : α, x ≠ y :=
  Nontrivial.exists_pair_ne

/-- Pushforward a `Nontrivial` instance along an injective function. -/
/-
**Function.Injective.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Nontrivial α] {f : α → β}, Function.Injec
tive f → Nontrivial β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂

--- 原说明 ---
Pushforward a `Nontrivial` instance along an injective function.
-/
protected theorem Function.Injective.nontrivial [Nontrivial α] {f : α → β}
    (hf : Function.Injective f) : Nontrivial β :=
  let ⟨x, y, h⟩ := exists_pair_ne α
  ⟨⟨f x, f y, hf.ne h⟩⟩

/-- An injective function from a nontrivial type has an argument at
which it does not take a given value. -/
/-
**Function.Injective.exists_ne** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Nontrivial α] {f : α → β}, Function.Injec
tive f → ∀ (y : β), ∃ x, f x ≠ y
参数：y : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {x y : α} {z : β}, f y = z → (f x ≠ z ↔ x ≠ y)

--- 原说明 ---
An injective function from a nontrivial type has an argument at
which it does not take a given value.
-/
protected theorem Function.Injective.exists_ne [Nontrivial α] {f : α → β}
    (hf : Function.Injective f) (y : β) : ∃ x, f x ≠ y := by
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩
  by_cases h : f x₂ = y
  · exact ⟨x₁, (hf.ne_iff' h).2 hx⟩
  · exact ⟨x₂, h⟩

-- See Note [decidable namespace]
/-
**Decidable.exists_ne** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Type u_1} [Nontrivial α] [DecidableEq α] (x : α), ∃ y, y ≠ x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Decidable.exists_ne [Nontrivial α] [DecidableEq α] (x : α) : ∃ y, y ≠ x := by
  rcases exists_pair_ne α with ⟨y, y', h⟩
  by_cases hx : x = y
  · rw [← hx] at h
    exact ⟨y', h.symm⟩
  · exact ⟨y, Ne.symm hx⟩
/-
**exists_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ne [Nontrivial α] (x : α) : exists y, y != x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.exists_ne`：∀ {α : Type u_1} [Nontrivial α] [DecidableEq α] (x 
: α), ∃ y, y ≠ x
-/
theorem exists_ne [Nontrivial α] (x : α) : ∃ y, y ≠ x := by
  classical
  exact Decidable.exists_ne x

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
/-
**nontrivial_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
参数：x y : α；h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nontrivial_of_ne (x y : α) (h : x ≠ y) : Nontrivial α :=
  ⟨⟨x, y, h⟩⟩
/-
**nontrivial_iff_exists_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_iff_exists_ne (x : α) : Nontrivial α ↔ exists y, y != x
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
-/
theorem nontrivial_iff_exists_ne (x : α) : Nontrivial α ↔ ∃ y, y ≠ x :=
  ⟨fun h ↦ @exists_ne α h x, fun ⟨_, hy⟩ ↦ nontrivial_of_ne _ _ hy⟩
/-
**Function.nontrivial_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.nontrivial_of_nontrivial (α β : Type*) [Nontrivial (α -> β)] : No
ntrivial β
参数：α β : Type*；α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
-/
theorem Function.nontrivial_of_nontrivial (α β : Type*) [Nontrivial (α → β)] :
    Nontrivial β := by
  obtain ⟨f, g, h⟩ := exists_pair_ne (α → β)
  rw [ne_eq, funext_iff, Classical.not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial Prop :=
  ⟨⟨True, False, true_ne_false⟩⟩

/-- See Note [lower instance priority]

Note that since this and `instNonemptyOfInhabited` are the most "obvious" way to find a nonempty
instance if no direct instance can be found, we give this a higher priority than the usual `100`.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [lower instance priority]

Note that since this and `instNonemptyOfInhabited` are the most "obvious" way to
 find a nonempty
instance if no direct instance can be found, we give this a higher priority than
 the usual `100`.
-/
instance (priority := 500) Nontrivial.to_nonempty [Nontrivial α] : Nonempty α :=
  let ⟨x, _⟩ := _root_.exists_pair_ne α
  ⟨x⟩
/-
**subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_iff : Subsingleton α ↔ forall x y : α, x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem subsingleton_iff : Subsingleton α ↔ ∀ x y : α, x = y :=
  ⟨by
    intro h
    exact Subsingleton.elim, fun h ↦ ⟨h⟩⟩

@[push]
/-
**not_nontrivial_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_nontrivial_iff_subsingleton : ¬Nontrivial α ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_nontrivial_iff_subsingleton : ¬Nontrivial α ↔ Subsingleton α := by
  simp only [nontrivial_iff, subsingleton_iff, not_exists, Classical.not_not]
/-
**not_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α :=
  fun ⟨⟨x, y, h⟩⟩ ↦ h <| Subsingleton.elim x y
/-
**not_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_nontrivial`：not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α
-/
theorem not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α :=
  fun _ => not_nontrivial _ ‹_›

@[push]
/-
**not_subsingleton_iff_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_subsingleton_iff_nontrivial : ¬Subsingleton α ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma not_subsingleton_iff_nontrivial : ¬Subsingleton α ↔ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton, Classical.not_not]

/-- A type is either a subsingleton or nontrivial. -/
/-
**subsingleton_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_or_nontrivial (α : Type*) : Subsingleton α ∨ Nontrivial α
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p

--- 原说明 ---
A type is either a subsingleton or nontrivial.
-/
theorem subsingleton_or_nontrivial (α : Type*) : Subsingleton α ∨ Nontrivial α := by
  rw [← not_nontrivial_iff_subsingleton, or_comm]
  exact Classical.em _
/-
**false_of_nontrivial_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：false_of_nontrivial_of_subsingleton (α : Type*) [Nontrivial α] [Subsinglet
on α] : False
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_nontrivial`：not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α
-/
theorem false_of_nontrivial_of_subsingleton (α : Type*) [Nontrivial α] [Subsingleton α] : False :=
  not_nontrivial _ ‹_›

/-- Pullback a `Nontrivial` instance along a surjective function. -/
/-
**Function.Surjective.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Nontrivial β] {f : α → β}, Function.Surje
ctive f → Nontrivial α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Pullback a `Nontrivial` instance along a surjective function.
-/
protected theorem Function.Surjective.nontrivial [Nontrivial β] {f : α → β}
    (hf : Function.Surjective f) : Nontrivial α := by
  rcases exists_pair_ne β with ⟨x, y, h⟩
  rcases hf x with ⟨x', hx'⟩
  rcases hf y with ⟨y', hy'⟩
  have : x' ≠ y' := by
    refine fun H ↦ h ?_
    rw [← hx', ← hy', H]
  exact ⟨⟨x', y', this⟩⟩

namespace Bool

/-
**Bool.** 是 Mathlib 中的一个实例，位于命名空间 `Bool`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial Bool :=
  ⟨⟨true, false, nofun⟩⟩

end Bool

/-
**NeZero.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NeZero.nontrivial {α : Type*} [Zero α] (a : α) [NeZero a] : Nontrivial α
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem NeZero.nontrivial {α : Type*} [Zero α] (a : α) [NeZero a] : Nontrivial α :=
  ⟨⟨a, 0, NeZero.ne a⟩⟩
