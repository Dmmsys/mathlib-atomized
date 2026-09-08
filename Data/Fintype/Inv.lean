/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# Computable inverses for injective/surjective functions on finite types

## Main results

* `Function.Injective.invOfMemRange`, `Embedding.invOfMemRange`, `Fintype.bijInv`:
  computable versions of `Function.invFun`.
* `Fintype.choose`: computably obtain a witness for `ExistsUnique`.
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

/-- The inverse of an `hf : injective` function `f : α → β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` and `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = Fintype.card α`.
-/
/-
**Function.Injective.invOfMemRange** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：invOfMemRange : Set.range f -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an `hf : injective` function `f : α → β`, of the type `↥(Set.rang
e f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` an
d `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f hf).symm`.
This function should not usually be used for actual computation because for most
 cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so i
t is O(N) where
`N = Fintype.card α`.
-/
def invOfMemRange : Set.range f → α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.existsUnique_of_mem_range b.property))
/-
**Function.Injective.left_inv_of_invOfMemRange** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Injective`。
形式化陈述：left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b
参数：b : Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : l.choos
e p hp in l ∧ p (l.choose p hp)
-/
theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]
/-
**Function.Injective.right_inv_of_invOfMemRange** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.Injective`。
形式化陈述：right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_
self a⟩ = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : l.choos
e p hp in l ∧ p (l.choose p hp)
-/
theorem right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right
/-
**Function.Injective.invFun_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injecti
ve`。
形式化陈述：invFun_restrict [Nonempty α] : (Set.range f).domRestrict (invFun f) = hf.i
nvOfMemRange
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
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Function.Injective.left_inv_of_invOfMemRange`：left_inv_of_invOfMemRange 
(b : Set.range f) : f (hf.invOfMemRange b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_restrict [Nonempty α] : (Set.range f).domRestrict (invFun f) = hf.invOfMemRange := by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]
/-
**Function.Injective.invOfMemRange_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Injective`。
形式化陈述：invOfMemRange_surjective : Function.Surjective hf.invOfMemRange
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.right_inv_of_invOfMemRange`：right_inv_of_invOfMemRang
e (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOfMemRange_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.range f)

/-- The inverse of an embedding `f : α ↪ β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` and `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = Fintype.card α`.
-/
/-
**Function.Embedding.invOfMemRange** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding
`。
形式化陈述：invOfMemRange : α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f

--- 原说明 ---
The inverse of an embedding `f : α ↪ β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` an
d `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f f.injective).symm`.
This function should not usually be used for actual computation because for most
 cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so i
t is O(N) where
`N = Fintype.card α`.
-/
def invOfMemRange : α :=
  f.injective.invOfMemRange b

@[simp]
/-
**Function.Embedding.left_inv_of_invOfMemRange** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Embedding`。
形式化陈述：left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.left_inv_of_invOfMemRange`：left_inv_of_invOfMemRange 
(b : Set.range f) : f (hf.invOfMemRange b) = b
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b :=
  f.injective.left_inv_of_invOfMemRange b

@[simp]
/-
**Function.Embedding.right_inv_of_invOfMemRange** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.Embedding`。
形式化陈述：right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_s
elf a⟩ = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.right_inv_of_invOfMemRange`：right_inv_of_invOfMemRang
e (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.injective.right_inv_of_invOfMemRange a
/-
**Function.Embedding.invFun_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embeddi
ng`。
形式化陈述：invFun_restrict [Nonempty α] : (Set.range f).domRestrict (invFun f) = f.in
vOfMemRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Function.Embedding.left_inv_of_invOfMemRange`：left_inv_of_invOfMemRange 
: f (f.invOfMemRange b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_restrict [Nonempty α] : (Set.range f).domRestrict (invFun f) = f.invOfMemRange := by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]
/-
**Function.Embedding.invOfMemRange_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Embedding`。
形式化陈述：invOfMemRange_surjective : Function.Surjective f.invOfMemRange
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.right_inv_of_invOfMemRange`：right_inv_of_invOfMemRang
e (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOfMemRange_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

end Embedding

end Function

end Inv

open Finset

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α → Prop) [DecidablePred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
/-
**Fintype.chooseX** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：chooseX (hp : exists! a : α, p a) : { a // p a }
参数：hp : exists! a : α, p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fintype `α` and a predicate `p`, associate to a proof that there is a un
ique element of
`α` satisfying `p` this unique element, as an element of the corresponding subty
pe.
-/
def chooseX (hp : ∃! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ (by simpa), Finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
/-
**Fintype.choose** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：choose (hp : exists! a, p a) : α
参数：hp : exists! a, p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fintype `α` and a predicate `p`, associate to a proof that there is a un
ique element of
`α` satisfying `p` this unique element, as an element of `α`.
-/
def choose (hp : ∃! a, p a) : α :=
  chooseX p hp
/-
**Fintype.choose_spec** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：choose_spec (hp : exists! a, p a) : p (choose p hp)
参数：hp : exists! a, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
  (chooseX p hp).property
/-
**Fintype.choose_subtype_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：choose_subtype_eq {α : Type*} (p : α -> Prop) [Fintype { a : α // p a }] [
DecidableEq α] (x : { a : α // p a }) (h : exists! a : { a // p a }, (a : α) = x
参数：p : α -> Prop；x : { a : α // p a }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Fintype.choose_spec`：choose_spec (hp : exists! a, p a) : p (choose p hp)
-/
theorem choose_subtype_eq {α : Type*} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α]
    (x : { a : α // p a })
    (h : ∃! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by simpa [Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

end Choose

section BijectionInverse

variable [Fintype α] [DecidableEq β] {f : α → β}

/-- `bijInv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `Function.invFun`. -/
/-
**Fintype.bijInv** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：bijInv (f_bij : Bijective f) (b : β) : α
参数：f_bij : Bijective f；b : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.existsUnique`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Bijective f → ∀ (b : β), ∃! a, f a = b

--- 原说明 ---
`bijInv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `Function.invFun`.
-/
def bijInv (f_bij : Bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b) (f_bij.existsUnique b)
/-
**Fintype.leftInverse_bijInv** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f
参数：f_bij : Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Fintype.choose_spec`：choose_spec (hp : exists! a, p a) : p (choose p hp)
· 使用定理 `Function.Bijective.existsUnique`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Bijective f → ∀ (b : β), ∃! a, f a = b
-/
theorem leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)
/-
**Fintype.rightInverse_bijInv** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f
参数：f_bij : Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.choose_spec`：choose_spec (hp : exists! a, p a) : p (choose p hp)
· 使用定理 `Function.Bijective.existsUnique`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Bijective f → ∀ (b : β), ∃! a, f a = b
-/
theorem rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _
/-
**Fintype.bijective_bijInv** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij)
参数：f_bij : Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `Fintype.rightInverse_bijInv`：rightInverse_bijInv (f_bij : Bijective f) :
 RightInverse (bijInv f_bij) f
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Fintype.leftInverse_bijInv`：leftInverse_bijInv (f_bij : Bijective f) : L
eftInverse (bijInv f_bij) f
-/
theorem bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩

end BijectionInverse

end Fintype

