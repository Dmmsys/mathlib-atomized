/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
module

public import Batteries.Tactic.GeneralizeProofs
public import Mathlib.Data.Part
public import Mathlib.Data.Rel

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → Part β`.

## Definitions

* `PFun α β`: Type of partial functions from `α` to `β`. Defined as `α → Part β` and denoted
  `α →. β`.
* `PFun.Dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `PFun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `Dom`.
* `PFun.asSubtype`: Returns a partial function as a function from its `Dom`.
* `PFun.toSubtype`: Restricts the codomain of a function to a subtype.
* `PFun.evalOpt`: Returns a partial function with a decidable `Dom` as a function `a → Option β`.
* `PFun.lift`: Turns a function into a partial function.
* `PFun.id`: The identity as a partial function.
* `PFun.comp`: Composition of partial functions.
* `PFun.restrict`: Restriction of a partial function to a smaller `Dom`.
* `PFun.res`: Turns a function into a partial function with a prescribed domain.
* `PFun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `PFun.fixInduction`: A recursion principle for `PFun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `Rel` definitions to `PFun`:
* `PFun.image`: Image of a set under a partial function.
* `PFun.ran`: Range of a partial function.
* `PFun.preimage`: Preimage of a set under a partial function.
* `PFun.core`: Core of a set under a partial function.
* `PFun.graph`: Graph of a partial function `a →. β` as a `Set (α × β)`.
* `PFun.graph'`: Graph of a partial function `a →. β` as a `Rel α β`.

### `PFun α` as a monad

Monad operations:
* `PFun.pure`: The monad `pure` function, the constant `x` function.
* `PFun.bind`: The monad `bind` function, pointwise `Part.bind`
* `PFun.map`: The monad `map` function, pointwise `Part.map`.
-/

@[expose] public section

open Function

/-- `PFun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → Part β`. -/
/-
**PFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PFun (α β : Type*)
参数：α β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PFun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → Part β`.
-/
def PFun (α β : Type*) :=
  α → Part β

/-- `α →. β` is notation for the type `PFun α β` of partial functions from `α` to `β`. -/
infixr:25 " →. " => PFun

namespace PFun

variable {α β γ δ ε ι : Type*}

/-
**PFun.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `PFun`。
形式化陈述：inhabited : Inhabited (α ->. β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (α →. β) :=
  ⟨fun _ => Part.none⟩

/-- The domain of a partial function -/
/-
**PFun.Dom** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：Dom (f : α ->. β) : Set α
参数：f : α ->. β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain of a partial function
-/
def Dom (f : α →. β) : Set α :=
  {a | (f a).Dom}

@[simp]
/-
**PFun.mem_dom** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_dom (f : α ->. β) (x : α) : x in Dom f ↔ exists y, y in f x
参数：f : α ->. β；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_dom (f : α →. β) (x : α) : x ∈ Dom f ↔ ∃ y, y ∈ f x := by simp [Dom, Part.dom_iff_mem]

@[simp]
/-
**PFun.dom_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_mk (p : α -> Prop) (f : forall a, p a -> β) : (PFun.Dom fun x => ⟨p x,
 f x⟩) = { x | p x }
参数：p : α -> Prop；f : forall a, p a -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_mk (p : α → Prop) (f : ∀ a, p a → β) : (PFun.Dom fun x => ⟨p x, f x⟩) = { x | p x } :=
  rfl
/-
**PFun.dom_eq** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_eq (f : α ->. β) : Dom f = { x | exists y, y in f x }
参数：f : α ->. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PFun.mem_dom`：mem_dom (f : α ->. β) (x : α) : x in Dom f ↔ exists y, y i
n f x
-/
theorem dom_eq (f : α →. β) : Dom f = { x | ∃ y, y ∈ f x } :=
  Set.ext (mem_dom f)

/-- Evaluate a partial function -/
/-
**PFun.fn** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：fn (f : α ->. β) (a : α) : a in Dom f -> β
参数：f : α ->. β；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a partial function
-/
def fn (f : α →. β) (a : α) : a ∈ Dom f → β :=
  (f a).get

@[simp]
/-
**PFun.fn_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：fn_apply (f : α ->. β) (a : α) : f.fn a = (f a).get
参数：f : α ->. β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fn_apply (f : α →. β) (a : α) : f.fn a = (f a).get :=
  rfl

/-- Evaluate a partial function to return an `Option` -/
/-
**PFun.evalOpt** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：evalOpt (f : α ->. β) [D : DecidablePred (· in Dom f)] (x : α) : Option β
参数：f : α ->. β；· in Dom f；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a partial function to return an `Option`
-/
def evalOpt (f : α →. β) [D : DecidablePred (· ∈ Dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)

/-- Partial function extensionality -/
/-
**PFun.ext'** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：ext' {f g : α ->. β} (H1 : forall a, a in Dom f ↔ a in Dom g) (H2 : forall
 a p q, f.fn a p = g.fn a q) : f = g
参数：H1 : forall a, a in Dom f ↔ a in Dom g；H2 : forall a p q, f.fn a p = g.fn a q
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.ext'`：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h
₂, o.get h₁ = p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od =…

--- 原说明 ---
Partial function extensionality
-/
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ Dom f ↔ a ∈ Dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) :
    f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)

@[ext]
/-
**PFun.ext** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f = g
参数：H : forall a b, b in f a ↔ b in g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
-/
theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun a => Part.ext (H a)

/-- Turns a partial function into a function out of its domain. -/
/-
**PFun.asSubtype** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：asSubtype (f : α ->. β) (s : f.Dom) : β
参数：f : α ->. β；s : f.Dom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a partial function into a function out of its domain.
-/
def asSubtype (f : α →. β) (s : f.Dom) : β :=
  f.fn s s.2

/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : Subtype p → β)`. -/
/-
**PFun.equivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：equivSubtype : (α ->. β) ≃ Σ p : α -> Prop, Subtype p -> β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : Subtype p → β)`.
-/
def equivSubtype : (α →. β) ≃ Σ p : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun _ =>
    funext fun _ => Part.eta _, fun ⟨p, f⟩ => by dsimp; congr⟩
/-
**PFun.asSubtype_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：asSubtype_eq_of_mem {f : α ->. β} {x : α} {y : β} (fxy : y in f x) (domx :
 x in f.Dom) : f.asSubtype ⟨x, domx⟩ = y
参数：fxy : y in f x；domx : x in f.Dom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `Part.get_mem`：get_mem {o : Part α} (h) : get o h in o
-/
theorem asSubtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy

/-- Turn a total function into a partial function. -/
@[coe]
/-
**PFun.lift** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → α →. β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a total function into a partial function.
-/
protected def lift (f : α → β) : α →. β := fun a => Part.some (f a)
/-
**PFun.coe** 是 Mathlib 中的一个实例，位于命名空间 `PFun`。
形式化陈述：coe : Coe (α -> β) (α ->. β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coe : Coe (α → β) (α →. β) :=
  ⟨PFun.lift⟩

@[simp]
/-
**PFun.coe_val** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：coe_val (f : α -> β) (a : α) : (f : α ->. β) a = Part.some (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl

@[simp]
/-
**PFun.dom_coe** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_coe (f : α -> β) : (f : α ->. β).Dom = Set.univ
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_coe (f : α → β) : (f : α →. β).Dom = Set.univ :=
  rfl
/-
**PFun.lift_injective** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：lift_injective : Injective (PFun.lift : (α -> β) -> α ->. β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.some_injective`：some_injective : Injective (@Part.some α)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem lift_injective : Injective (PFun.lift : (α → β) → α →. β) := fun _ _ h =>
  funext fun a => Part.some_injective <| congr_fun h a

/-- Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
`f`. -/
/-
**PFun.graph** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：graph (f : α ->. β) : Set (α × β)
参数：f : α ->. β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in t
he domain of
`f`.
-/
def graph (f : α →. β) : Set (α × β) :=
  { p | p.2 ∈ f p.1 }

/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
/-
**PFun.graph'** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：graph' (f : α ->. β) : SetRel α β
参数：f : α ->. β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph of a partial function as a relation. `x` and `y` are related iff `f x` is 
defined and
"equals" `y`.
-/
def graph' (f : α →. β) : SetRel α β := {(x, y) : α × β | y ∈ f x}

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
/-
**PFun.ran** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：ran (f : α ->. β) : Set β
参数：f : α ->. β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`.
-/
def ran (f : α →. β) : Set β :=
  { b | ∃ a, b ∈ f a }

/-- Restrict a partial function to a smaller domain. -/
/-
**PFun.restrict** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：restrict (f : α ->. β) {p : Set α} (H : p subseteq f.Dom) : α ->. β
参数：f : α ->. β；H : p subseteq f.Dom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a partial function to a smaller domain.
-/
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x =>
  (f x).restrict (x ∈ p) (@H x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PFun.mem_restrict** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_restrict {f : α ->. β} {s : Set α} (h : s subseteq f.Dom) (a : α) (b :
 β) : b in f.restrict h a ↔ a in s ∧ b in f a
参数：h : s subseteq f.Dom；a : α；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.Dom) (a : α) (b : β) :
    b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a := by simp [restrict]

/-- Turns a function into a partial function with a prescribed domain. -/
/-
**PFun.res** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：res (f : α -> β) (s : Set α) : α ->. β
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
Turns a function into a partial function with a prescribed domain.
-/
def res (f : α → β) (s : Set α) : α →. β :=
  (PFun.lift f).restrict s.subset_univ

set_option backward.isDefEq.respectTransparency false in
/-
**PFun.mem_res** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_res (f : α -> β) (s : Set α) (a : α) (b : β) : b in res f s a ↔ a in s
 ∧ f a = b
参数：f : α -> β；s : Set α；a : α；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := by
  simp [res, @eq_comm _ b]
/-
**PFun.res_univ** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：res_univ (f : α -> β) : PFun.res f Set.univ = f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem res_univ (f : α → β) : PFun.res f Set.univ = f :=
  rfl
/-
**PFun.dom_iff_graph** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_iff_graph (f : α ->. β) (x : α) : x in f.Dom ↔ exists y, (x, y) in f.g
raph
参数：f : α ->. β；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.dom_iff_mem`：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
-/
theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.Dom ↔ ∃ y, (x, y) ∈ f.graph :=
  Part.dom_iff_mem
/-
**PFun.lift_graph** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：lift_graph {f : α -> β} {a b} : (a, b) in (f : α ->. β).graph ↔ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
  show (∃ _ : True, f a = b) ↔ f a = b by simp

/-- The monad `pure` function, the total constant `x` function -/
/-
**PFun.pure** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → β → α →. β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad `pure` function, the total constant `x` function
-/
protected def pure (x : β) : α →. β := fun _ => Part.some x

/-- The monad `bind` function, pointwise `Part.bind` -/
/-
**PFun.bind** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：bind (f : α ->. β) (g : β -> α ->. γ) : α ->. γ
参数：f : α ->. β；g : β -> α ->. γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad `bind` function, pointwise `Part.bind`
-/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ := fun a => (f a).bind fun b => g b a

@[simp]
/-
**PFun.bind_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：bind_apply (f : α ->. β) (g : β -> α ->. γ) (a : α) : f.bind g a = (f a).b
ind fun b => g b a
参数：f : α ->. β；g : β -> α ->. γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_apply (f : α →. β) (g : β → α →. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl

/-- The monad `map` function, pointwise `Part.map` -/
/-
**PFun.map** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：map (f : β -> γ) (g : α ->. β) : α ->. γ
参数：f : β -> γ；g : α ->. β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad `map` function, pointwise `Part.map`
-/
def map (f : β → γ) (g : α →. β) : α →. γ := fun a => (g a).map f
/-
**PFun.monad** 是 Mathlib 中的一个实例，位于命名空间 `PFun`。
形式化陈述：monad : Monad (PFun α) where pure
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monad : Monad (PFun α) where
  pure := PFun.pure
  bind := PFun.bind
  map := PFun.map
/-
**PFun.lawfulMonad** 是 Mathlib 中的一个实例，位于命名空间 `PFun`。
形式化陈述：lawfulMonad : LawfulMonad (PFun α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulMonad.mk'`：∀ (m : Type u → Type v) [inst : Monad m],   (∀ {α : Typ
e u} (x : m α), id <$> x = x) →     (∀ {α β : Type u} (x : α) (f : α → m β), pur
e x >…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.bind_assoc`：bind_assoc {γ} (f : Part α) (g : α -> Part β) (k : β ->
 Part γ) : (f.bind g).bind k = f.bind fun x => (g x).bind k
· 使用定理 `Part.bind_some_eq_map`：bind_some_eq_map (f : α -> β) (x : Part α) : x.bi
nd (fun y => some (f y)) = map f x
-/
instance lawfulMonad : LawfulMonad (PFun α) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => funext fun _ => Part.bind_some_eq_map _ _)
  (id_map := fun f => by funext a; dsimp [Functor.map, PFun.map]; cases f a; rfl)
  (pure_bind := fun x f => funext fun _ => Part.bind_some _ (f x))
  (bind_assoc := fun f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a)
/-
**PFun.pure_defined** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：pure_defined (p : Set α) (x : β) : p subseteq (@PFun.pure α _ x).Dom
参数：p : Set α；x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem pure_defined (p : Set α) (x : β) : p ⊆ (@PFun.pure α _ x).Dom :=
  p.subset_univ
/-
**PFun.bind_defined** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：bind_defined {α β γ} (p : Set α) {f : α ->. β} {g : β -> α ->. γ} (H1 : p 
subseteq f.Dom) (H2 : forall x, p subseteq (g x).Dom) : p subseteq (f >>= g).Dom
参数：p : Set α；H1 : p subseteq f.Dom；H2 : forall x, p subseteq (g x).Dom。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.Dom)
    (H2 : ∀ x, p ⊆ (g x).Dom) : p ⊆ (f >>= g).Dom := fun a ha =>
  (⟨H1 ha, H2 _ ha⟩ : a ∈ (f >>= g).Dom)

/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
/-
**PFun.fix** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：fix (f : α ->. β oplus α) : α ->. β
参数：f : α ->. β oplus α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
First return map. Transforms a partial function `f : α →. β ⊕ α` into the partia
l function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`,
 if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β
 ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is un
defined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.f
ix a` will return
`f.fix (f a)`).
-/
def fix (f : α →. β ⊕ α) : α →. β := fun a =>
  Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a) fun h =>
    WellFounded.fixF
      (fun a IH =>
        Part.assert (f a).Dom fun hf =>
          match e : (f a).get hf with
          | Sum.inl b => Part.some b
          | Sum.inr a' => IH a' ⟨hf, e⟩)
      a h
/-
**PFun.dom_of_mem_fix** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_of_mem_fix {f : α ->. β oplus α} {a : α} {b : β} (h : b in f.fix a) : 
(f a).Dom
参数：h : b in f.fix a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.mem_assert_iff`：mem_assert_iff {p : Prop} {f : p -> Part α} {a} : a
 in assert p f ↔ exists h : p, a in f h
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WellFounded.fixF_eq`：∀ {α : Sort u} {r : α → α → Prop} {C : α → Sort v} 
(F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α)   (acx : Acc r x), WellFou
nded.fixF…
-/
theorem dom_of_mem_fix {f : α →. β ⊕ α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom := by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fixF_eq] at h₂; exact h₂.fst.fst
/-
**PFun.mem_fix_iff** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_fix_iff {f : α ->. β oplus α} {a : α} {b : β} : b in f.fix a ↔ Sum.inl
 b in f a ∨ exists a', Sum.inr a' in f a ∧ b in f.fix a'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.mem_assert_iff`：mem_assert_iff {p : Prop} {f : p -> Part α} {a} : a
 in assert p f ↔ exists h : p, a in f h
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WellFounded.fixF_eq`：∀ {α : Sort u} {r : α → α → Prop} {C : α → Sort v} 
(F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α)   (acx : Acc r x), WellFou
nded.fixF…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.mem_assert`：∀ {α : Type u_1} {p : Prop} {f : p → Part α} {a : α} (h
 : p), a ∈ f h → a ∈ Part.assert p f
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_fix_iff {f : α →. β ⊕ α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fixF_eq] at h₂
    simp only [Part.mem_assert_iff] at h₂
    obtain ⟨h₂, h₃⟩ := h₂
    split at h₃
    next e => simp only [Part.mem_some_iff] at h₃; subst b; exact Or.inl ⟨h₂, e⟩
    next e => exact Or.inr ⟨_, ⟨_, e⟩, Part.mem_assert _ h₃⟩,
   fun h => by
    simp only [fix, Part.mem_assert_iff]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
      · rw [WellFounded.fixF_eq]
        -- Porting note: used to be simp [h₁, h₂]
        apply Part.mem_assert h₁
        split
        next e =>
          injection h₂.symm.trans e with h; simp [h]
        next e =>
          injection h₂.symm.trans e
    · simp only [fix, Part.mem_assert_iff] at h₃
      obtain ⟨h₃, h₄⟩ := h₃
      refine ⟨⟨_, fun y h' => ?_⟩, ?_⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
      · obtain ⟨h₁, h₂⟩ := h
        grind [WellFounded.fixF_eq]⟩

/-- If advancing one step from `a` leads to `b : β`, then `f.fix a = b` -/
/-
**PFun.fix_stop** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：fix_stop {f : α ->. β oplus α} {b : β} {a : α} (hb : Sum.inl b in f a) : b
 in f.fix a
参数：hb : Sum.inl b in f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.mem_fix_iff`：mem_fix_iff {f : α ->. β oplus α} {a : α} {b : β} : b 
in f.fix a ↔ Sum.inl b in f a ∨ exists a', Sum.inr a' in f a ∧ b in f.fix a'

--- 原说明 ---
If advancing one step from `a` leads to `b : β`, then `f.fix a = b`
-/
theorem fix_stop {f : α →. β ⊕ α} {b : β} {a : α} (hb : Sum.inl b ∈ f a) : b ∈ f.fix a := by
  rw [PFun.mem_fix_iff]
  exact Or.inl hb

/-- If advancing one step from `a` on `f` leads to `a' : α`, then `f.fix a = f.fix a'` -/
/-
**PFun.fix_fwd_eq** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：fix_fwd_eq {f : α ->. β oplus α} {a a' : α} (ha' : Sum.inr a' in f a) : f.
fix a = f.fix a'
参数：ha' : Sum.inr a' in f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PFun.mem_fix_iff`：mem_fix_iff {f : α ->. β oplus α} {a : α} {b : β} : b 
in f.fix a ↔ Sum.inl b in f a ∨ exists a', Sum.inr a' in f a ∧ b in f.fix a'
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If advancing one step from `a` on `f` leads to `a' : α`, then `f.fix a = f.fix a
'`
-/
theorem fix_fwd_eq {f : α →. β ⊕ α} {a a' : α} (ha' : Sum.inr a' ∈ f a) : f.fix a = f.fix a' := by
  ext b; constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
  · intro h
    rw [PFun.mem_fix_iff]
    exact Or.inr ⟨a', ha', h⟩
/-
**PFun.fix_fwd** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：fix_fwd {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b in f.fix a) (ha' 
: Sum.inr a' in f a) : b in f.fix a'
参数：hb : b in f.fix a；ha' : Sum.inr a' in f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFun.fix_fwd_eq`：fix_fwd_eq {f : α ->. β oplus α} {a a' : α} (ha' : Sum.
inr a' in f a) : f.fix a = f.fix a'
-/
theorem fix_fwd {f : α →. β ⊕ α} {b : β} {a a' : α} (hb : b ∈ f.fix a) (ha' : Sum.inr a' ∈ f a) :
    b ∈ f.fix a' := by rwa [← fix_fwd_eq ha']

/-- A recursion principle for `PFun.fix`. -/
@[elab_as_elim]
/-
**PFun.fixInduction** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：fixInduction {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : b
 in f.fix a) (H : forall a', b in f.fix a' -> (forall a'', Sum.inr a'' in f a' -
> C a'') -> C a') : C a
参数：h : b in f.fix a；H : forall a', b in f.fix a' -> (forall a'', Sum.inr a'' in 
f a' -> C a'') -> C a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursion principle for `PFun.fix`.
-/
def fixInduction {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') : C a := by
  have h₂ := (Part.mem_assert_iff.1 h).snd
  generalize_proofs at h₂
  clear h
  induction ‹Acc (Sum.inr · ∈ f ·) a› with | intro a ha IH => _
  have h : b ∈ f.fix a := Part.mem_assert_iff.2 ⟨⟨a, ha⟩, h₂⟩
  exact H a h fun a' fa' => IH a' fa' (Part.mem_assert_iff.1 (fix_fwd h fa')).snd
/-
**PFun.fixInduction_spec** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：fixInduction_spec {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (
h : b in f.fix a) (H : forall a', b in f.fix a' -> (forall a'', Sum.inr a'' in f
 a' -> C a'') -> C a') : @fixInduction _ _ C _ _ _ h H = H a h fun _ h' => fixIn
duction (fix_fwd h h') H
参数：h : b in f.fix a；H : forall a', b in f.fix a' -> (forall a'', Sum.inr a'' in 
f a' -> C a'') -> C a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.fix_fwd`：fix_fwd {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b i
n f.fix a) (ha' : Sum.inr a' in f a) : b in f.fix a'
-/
theorem fixInduction_spec {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') :
    @fixInduction _ _ C _ _ _ h H = H a h fun _ h' => fixInduction (fix_fwd h h') H := by
  unfold fixInduction
  generalize_proofs
  induction ‹Acc _ _›
  rfl

/-- Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate `P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
@[elab_as_elim]
/-
**PFun.fixInduction'** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：fixInduction' {C : α -> Sort*} {f : α ->. β oplus α} {b : β} {a : α} (h : 
b in f.fix a) (hbase : forall a_final : α, Sum.inl b in f a_final -> C a_final) 
(hind : forall a₀ a₁ : α, b in f.fix a₁ -> Sum.inr a₁ in f a₀ -> C a₁ -> C a₀) :
 C a
参数：h : b in f.fix a；hbase : forall a_final : α, Sum.inl b in f a_final -> C a_fi
nal；hind : forall a₀ a₁ : α, b in f.fix a₁ -> Sum.inr a₁ in f a₀ -> C a₁ -> C a₀
。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.dom_of_mem_fix`：dom_of_mem_fix {f : α ->. β oplus α} {a : α} {b : β
} (h : b in f.fix a) : (f a).Dom
· 使用定理 `PFun.fix_fwd`：fix_fwd {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b i
n f.fix a) (ha' : Sum.inr a' in f a) : b in f.fix a'

--- 原说明 ---
Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate 
`P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
def fixInduction' {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α}
    (h : b ∈ f.fix a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) : C a := by
  refine fixInduction h fun a' h ih => ?_
  rcases e : (f a').get (dom_of_mem_fix h) with b' | a'' <;> replace e : _ ∈ f a' := ⟨_, e⟩
  · apply hbase
    convert! e
    exact Part.mem_unique h (fix_stop e)
  · exact hind _ _ (fix_fwd h e) e (ih _ e)
/-
**PFun.fixInduction'_stop** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {C : α → Sort u_7} {f : α →. β ⊕ α} {b : β
} {a : α} (h : b ∈ f.fix a)   (fa : Sum.inl b ∈ f a) (hbase : (a_final : α) → Su
m.inl b ∈ f a_final → C a_final)   (hind : (a₀ a₁ : α) → b ∈ f.fix a₁ → Sum.inr 
a₁ ∈ f a₀ → C a₁ → C a₀), PFun.fixInduction' h hbase hind = hbase a fa
参数：h : b ∈ f.fix a；fa : Sum.inl b ∈ f a；hbase : (a_final : α) → Sum.inl b ∈ f a_
final → C a_final；hind : (a₀ a₁ : α) → b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ →
 C a₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.dom_of_mem_fix`：dom_of_mem_fix {f : α ->. β oplus α} {a : α} {b : β
} (h : b in f.fix a) : (f a).Dom
· 使用定理 `PFun.fix_fwd`：fix_fwd {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b i
n f.fix a) (ha' : Sum.inr a' in f a) : b in f.fix a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.fixInduction_spec`：fixInduction_spec {C : α -> Sort*} {f : α ->. β 
oplus α} {b : β} {a : α} (h : b in f.fix a) (H : forall a', b in f.fix a' -> (fo
rall a'', Su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Part.get_eq_of_mem`：get_eq_of_mem {o : Part α} {a} (h : a in o) (h') : g
et o h' = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fixInduction'_stop {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a : α} (h : b ∈ f.fix a)
    (fa : Sum.inl b ∈ f a) (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hbase a fa := by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e ↦
      Sum.casesOn x ?_ ?_ (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = hbase a fa) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp
/-
**PFun.fixInduction'_fwd** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {C : α → Sort u_7} {f : α →. β ⊕ α} {b : β
} {a a' : α} (h : b ∈ f.fix a)   (h' : b ∈ f.fix a') (fa : Sum.inr a' ∈ f a) (hb
ase : (a_final : α) → Sum.inl b ∈ f a_final → C a_final)   (hind : (a₀ a₁ : α) →
 b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀),   PFun.fixInduction' h hbase h
ind = hind a a' h' fa (PFun.fixInduction' h' hbase hind)
参数：h : b ∈ f.fix a；h' : b ∈ f.fix a'；fa : Sum.inr a' ∈ f a；hbase : (a_final : α)
 → Sum.inl b ∈ f a_final → C a_final；hind : (a₀ a₁ : α) → b ∈ f.fix a₁ → Sum.inr
 a₁ ∈ f a₀ → C a₁ → C a₀；PFun.fixInduction' h' hbase hind。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.dom_of_mem_fix`：dom_of_mem_fix {f : α ->. β oplus α} {a : α} {b : β
} (h : b in f.fix a) : (f a).Dom
· 使用定理 `PFun.fix_fwd`：fix_fwd {f : α ->. β oplus α} {b : β} {a a' : α} (hb : b i
n f.fix a) (ha' : Sum.inr a' in f a) : b in f.fix a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.fixInduction_spec`：fixInduction_spec {C : α -> Sort*} {f : α ->. β 
oplus α} {b : β} {a : α} (h : b in f.fix a) (H : forall a', b in f.fix a' -> (fo
rall a'', Su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Part.get_eq_of_mem`：get_eq_of_mem {o : Part α} {a} (h : a in o) (h') : g
et o h' = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fixInduction'_fwd {C : α → Sort*} {f : α →. β ⊕ α} {b : β} {a a' : α} (h : b ∈ f.fix a)
    (h' : b ∈ f.fix a') (fa : Sum.inr a' ∈ f a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) :
    @fixInduction' _ _ C _ _ _ h hbase hind = hind a a' h' fa (fixInduction' h' hbase hind) := by
  unfold fixInduction'
  rw [fixInduction_spec]
  -- Porting note: the explicit motive required because `simp` does not apply `Part.get_eq_of_mem`
  refine Eq.rec (motive := fun x e =>
      Sum.casesOn (motive := fun y => (f a).get (dom_of_mem_fix h) = y → C a) x ?_ ?_
      (Eq.trans (Part.get_eq_of_mem fa (dom_of_mem_fix h)) e) = _) ?_
    (Part.get_eq_of_mem fa (dom_of_mem_fix h)).symm
  simp

variable (f : α →. β)

/-- Image of a set under a partial function. -/
/-
**PFun.image** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：image (s : Set α) : Set β
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image of a set under a partial function.
-/
def image (s : Set α) : Set β :=
  f.graph'.image s
/-
**PFun.image_def** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：image_def (s : Set α) : f.image s = { y | exists x in s, y in f x }
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_def (s : Set α) : f.image s = { y | ∃ x ∈ s, y ∈ f x } :=
  rfl
/-
**PFun.mem_image** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_image (y : β) (s : Set α) : y in f.image s ↔ exists x in s, y in f x
参数：y : β；s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_image (y : β) (s : Set α) : y ∈ f.image s ↔ ∃ x ∈ s, y ∈ f x :=
  Iff.rfl
/-
**PFun.image_mono** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：image_mono {s t : Set α} (h : s subseteq t) : f.image s subseteq f.image t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.image_mono`：image_mono : Monotone R.image
-/
theorem image_mono {s t : Set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
  SetRel.image_mono h
/-
**PFun.image_inter** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：image_inter (s t : Set α) : f.image (s inter t) subseteq f.image s inter f
.image t
参数：s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.image_inter_subset`：image_inter_subset : image R (s₁ inter s₂) su
bseteq image R s₁ inter image R s₂
-/
theorem image_inter (s t : Set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
  SetRel.image_inter_subset _
/-
**PFun.image_union** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：image_union (s t : Set α) : f.image (s union t) = f.image s union f.image 
t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.image_union`：image_union : image R (s₁ union s₂) = image R s₁ uni
on image R s₂
-/
theorem image_union (s t : Set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
  SetRel.image_union _ s t

/-- Preimage of a set under a partial function. -/
/-
**PFun.preimage** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：preimage (s : Set β) : Set α
参数：s : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of a set under a partial function.
-/
def preimage (s : Set β) : Set α := f.graph'.preimage s
/-
**PFun.Preimage_def** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：Preimage_def (s : Set β) : f.preimage s = { x | exists y in s, y in f x }
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Preimage_def (s : Set β) : f.preimage s = { x | ∃ y ∈ s, y ∈ f x } :=
  rfl

@[simp, grind =]
/-
**PFun.mem_preimage** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_preimage (s : Set β) (x : α) : x in f.preimage s ↔ exists y in s, y in
 f x
参数：s : Set β；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.preimage s ↔ ∃ y ∈ s, y ∈ f x :=
  Iff.rfl
/-
**PFun.preimage_subset_dom** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_subset_dom (s : Set β) : f.preimage s subseteq f.Dom
参数：s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.dom_iff_mem`：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
-/
theorem preimage_subset_dom (s : Set β) : f.preimage s ⊆ f.Dom := fun _ ⟨y, _, fxy⟩ =>
  Part.dom_iff_mem.mpr ⟨y, fxy⟩
/-
**PFun.preimage_mono** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_mono {s t : Set β} (h : s subseteq t) : f.preimage s subseteq f.p
reimage t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.preimage_mono`：preimage_mono : Monotone R.preimage
-/
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
  SetRel.preimage_mono h
/-
**PFun.preimage_inter** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_inter (s t : Set β) : f.preimage (s inter t) subseteq f.preimage 
s inter f.preimage t
参数：s t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.preimage_inter_subset`：preimage_inter_subset : preimage R (t₁ int
er t₂) subseteq preimage R t₁ inter preimage R t₂
-/
theorem preimage_inter (s t : Set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
  SetRel.preimage_inter_subset _
/-
**PFun.preimage_union** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_union (s t : Set β) : f.preimage (s union t) = f.preimage s union
 f.preimage t
参数：s t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.preimage_union`：preimage_union : preimage R (t₁ union t₂) = preim
age R t₁ union preimage R t₂
-/
theorem preimage_union (s t : Set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
  SetRel.preimage_union _ s t
/-
**PFun.preimage_univ** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_univ : f.preimage Set.univ = f.Dom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_univ : f.preimage Set.univ = f.Dom := by ext; simp [mem_preimage, mem_dom]
/-
**PFun.coe_preimage** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：coe_preimage (f : α -> β) (s : Set β) : (f : α ->. β).preimage s = f ⁻¹' s
参数：f : α -> β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_preimage (f : α → β) (s : Set β) : (f : α →. β).preimage s = f ⁻¹' s := by ext; simp

/-- Core of a set `s : Set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
/-
**PFun.core** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：core (s : Set β) : Set α
参数：s : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Core of a set `s : Set β` with respect to a partial function `f : α →. β`. Set o
f all `a : α`
such that `f a ∈ s`, if `f a` is defined.
-/
def core (s : Set β) : Set α :=
  f.graph'.core s
/-
**PFun.core_def** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：core_def (s : Set β) : f.core s = { x | forall y, y in f x -> y in s }
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem core_def (s : Set β) : f.core s = { x | ∀ y, y ∈ f x → y ∈ s } :=
  rfl

@[simp]
/-
**PFun.mem_core** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_core (x : α) (s : Set β) : x in f.core s ↔ forall y, y in f x -> y in 
s
参数：x : α；s : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_core (x : α) (s : Set β) : x ∈ f.core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl
/-
**PFun.compl_dom_subset_core** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：compl_dom_subset_core (s : Set β) : f.Domᶜ subseteq f.core s
参数：s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PFun.mem_dom`：mem_dom (f : α ->. β) (x : α) : x in Dom f ↔ exists y, y i
n f x
-/
theorem compl_dom_subset_core (s : Set β) : f.Domᶜ ⊆ f.core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx
/-
**PFun.core_mono** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：core_mono {s t : Set β} (h : s subseteq t) : f.core s subseteq f.core t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.core_mono`：core_mono : Monotone R.core
-/
theorem core_mono {s t : Set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
  SetRel.core_mono h
/-
**PFun.core_inter** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：core_inter (s t : Set β) : f.core (s inter t) = f.core s inter f.core t
参数：s t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.core_inter`：core_inter : R.core (t₁ inter t₂) = R.core t₁ inter R
.core t₂
-/
theorem core_inter (s t : Set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
  SetRel.core_inter _ s t
/-
**PFun.mem_core_res** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_core_res (f : α -> β) (s : Set α) (t : Set β) (x : α) : x in (res f s)
.core t ↔ x in s -> f x in t
参数：f : α -> β；s : Set α；t : Set β；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) :
    x ∈ (res f s).core t ↔ x ∈ s → f x ∈ t := by simp [mem_core, mem_res]
/-
**PFun.core_res** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：core_res (f : α -> β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ unio
n f ⁻¹' t
参数：f : α -> β；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.mem_core_res`：mem_core_res (f : α -> β) (s : Set α) (t : Set β) (x 
: α) : x in (res f s).core t ↔ x in s -> f x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).core t = sᶜ ∪ f ⁻¹' t := by
  ext x
  rw [mem_core_res]
  by_cases h : x ∈ s <;> simp [h]
/-
**PFun.core_restrict** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：core_restrict (f : α -> β) (s : Set β) : (f : α ->. β).core s = s.preimage
 f
参数：f : α -> β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).core s = s.preimage f := by
  ext x; simp [core_def]
/-
**PFun.preimage_subset_core** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_subset_core (f : α ->. β) (s : Set β) : f.preimage s subseteq f.c
ore s
参数：f : α ->. β；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
theorem preimage_subset_core (f : α →. β) (s : Set β) : f.preimage s ⊆ f.core s :=
  fun _ ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys
/-
**PFun.preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_eq (f : α ->. β) (s : Set β) : f.preimage s = f.core s inter f.Do
m
参数：f : α ->. β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `PFun.preimage_subset_core`：preimage_subset_core (f : α ->. β) (s : Set β
) : f.preimage s subseteq f.core s
· 使用定理 `PFun.preimage_subset_dom`：preimage_subset_dom (s : Set β) : f.preimage s
 subseteq f.Dom
· 使用定理 `Part.get_mem`：get_mem {o : Part α} (h) : get o h in o
-/
theorem preimage_eq (f : α →. β) (s : Set β) : f.preimage s = f.core s ∩ f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y ∈ s := xcore (Part.get_mem _)
    show x ∈ f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩
/-
**PFun.core_eq** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：core_eq (f : α ->. β) (s : Set β) : f.core s = f.preimage s union f.Domᶜ
参数：f : α ->. β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.preimage_eq`：preimage_eq (f : α ->. β) (s : Set β) : f.preimage s =
 f.core s inter f.Dom
· 使用定理 `Set.inter_union_distrib_right`：inter_union_distrib_right (s t u : Set α)
 : s inter t union u = (s union u) inter (t union u)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `PFun.compl_dom_subset_core`：compl_dom_subset_core (s : Set β) : f.Domᶜ s
ubseteq f.core s
-/
theorem core_eq (f : α →. β) (s : Set β) : f.core s = f.preimage s ∪ f.Domᶜ := by
  rw [preimage_eq, Set.inter_union_distrib_right, Set.union_comm (Dom f), Set.compl_union_self,
    Set.inter_univ, Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]
/-
**PFun.preimage_asSubtype** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_asSubtype (f : α ->. β) (s : Set β) : f.asSubtype ⁻¹' s = Subtype
.val ⁻¹' f.preimage s
参数：f : α ->. β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Part.get_mem`：get_mem {o : Part α} (h) : get o h in o
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
theorem preimage_asSubtype (f : α →. β) (s : Set β) :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.preimage s := by
  ext x
  simp only [Set.mem_preimage, PFun.asSubtype, PFun.mem_preimage]
  show f.fn x.val _ ∈ s ↔ ∃ y ∈ s, y ∈ f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property ∈ f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys

/-- Turns a function into a partial function to a subtype. -/
/-
**PFun.toSubtype** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：toSubtype (p : β -> Prop) (f : α -> β) : α ->. Subtype p
参数：p : β -> Prop；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a function into a partial function to a subtype.
-/
def toSubtype (p : β → Prop) (f : α → β) : α →. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩

@[simp]
/-
**PFun.dom_toSubtype** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_toSubtype (p : β -> Prop) (f : α -> β) : (toSubtype p f).Dom = { a | p
 (f a) }
参数：p : β -> Prop；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_toSubtype (p : β → Prop) (f : α → β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl

@[simp]
/-
**PFun.toSubtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：toSubtype_apply (p : β -> Prop) (f : α -> β) (a : α) : toSubtype p f a = ⟨
p (f a), Subtype.mk _⟩
参数：p : β -> Prop；f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubtype_apply (p : β → Prop) (f : α → β) (a : α) :
    toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl
/-
**PFun.dom_toSubtype_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_toSubtype_apply_iff {p : β -> Prop} {f : α -> β} {a : α} : (toSubtype 
p f a).Dom ↔ p (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dom_toSubtype_apply_iff {p : β → Prop} {f : α → β} {a : α} :
    (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl
/-
**PFun.mem_toSubtype_iff** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_toSubtype_iff {p : β -> Prop} {f : α -> β} {a : α} {b : Subtype p} : b
 in toSubtype p f a ↔ ↑b = f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.toSubtype_apply`：toSubtype_apply (p : β -> Prop) (f : α -> β) (a : 
α) : toSubtype p f a = ⟨p (f a), Subtype.mk _⟩
· 使用定理 `Part.mem_mk_iff`：mem_mk_iff {p : Prop} {o : p -> α} {a : α} : a in Part.
mk p o ↔ exists h, o h = a
· 使用定理 `exists_subtype_mk_eq_iff`：∀ {α : Sort u_1} {p : α → Prop} {a : Subtype p
} {b : α}, (∃ (h : p b), ⟨b, h⟩ = a) ↔ b = ↑a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubtype_iff {p : β → Prop} {f : α → β} {a : α} {b : Subtype p} :
    b ∈ toSubtype p f a ↔ ↑b = f a := by
  rw [toSubtype_apply, Part.mem_mk_iff, exists_subtype_mk_eq_iff, eq_comm]

/-- The identity as a partial function -/
/-
**PFun.id** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：(α : Type u_7) → α →. α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a partial function
-/
protected def id (α : Type*) : α →. α :=
  Part.some

@[simp, norm_cast]
/-
**PFun.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：coe_id (α : Type*) : ((id : α -> α) : α ->. α) = PFun.id α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id (α : Type*) : ((id : α → α) : α →. α) = PFun.id α :=
  rfl

@[simp]
/-
**PFun.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：id_apply (a : α) : PFun.id α a = Part.some a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : PFun.id α a = Part.some a :=
  rfl

/-- Composition of partial functions as a partial function. -/
/-
**PFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：comp (f : β ->. γ) (g : α ->. β) : α ->. γ
参数：f : β ->. γ；g : α ->. β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of partial functions as a partial function.
-/
def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f

@[simp, grind =]
/-
**PFun.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：comp_apply (f : β ->. γ) (g : α ->. β) (a : α) : f.comp g a = (g a).bind f
参数：f : β ->. γ；g : α ->. β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PFun.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：id_comp (f : α ->. β) : (PFun.id β).comp f = f
参数：f : α ->. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem id_comp (f : α →. β) : (PFun.id β).comp f = f :=
  ext fun _ _ => by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PFun.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：comp_id (f : α ->. β) : f.comp (PFun.id α) = f
参数：f : α ->. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_id (f : α →. β) : f.comp (PFun.id α) = f :=
  ext fun _ _ => by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PFun.dom_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_comp (f : β ->. γ) (g : α ->. β) : (f.comp g).Dom = g.preimage f.Dom
参数：f : β ->. γ；g : α ->. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem dom_comp (f : β →. γ) (g : α →. β) : (f.comp g).Dom = g.preimage f.Dom := by
  ext
  simp
  grind

@[simp]
/-
**PFun.preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：preimage_comp (f : β ->. γ) (g : α ->. β) (s : Set γ) : (f.comp g).preimag
e s = g.preimage (f.preimage s)
参数：f : β ->. γ；g : α ->. β；s : Set γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_comp (f : β →. γ) (g : α →. β) (s : Set γ) :
    (f.comp g).preimage s = g.preimage (f.preimage s) := by
  grind

@[simp]
/-
**PFun.Part.bind_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun.Part`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : β →. γ) (g : α →. β) (
a : Part α),   a.bind (f.comp g) = (a.bind g).bind f
参数：f : β →. γ；g : α →. β；a : Part α；f.comp g；a.bind g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
-/
theorem Part.bind_comp (f : β →. γ) (g : α →. β) (a : Part α) :
    a.bind (f.comp g) = (a.bind g).bind f := by
  ext
  grind

@[simp]
/-
**PFun.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：comp_assoc (f : γ ->. δ) (g : β ->. γ) (h : α ->. β) : (f.comp g).comp h =
 f.comp (g.comp h)
参数：f : γ ->. δ；g : β ->. γ；h : α ->. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFun.Part.bind_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f :
 β →. γ) (g : α →. β) (a : Part α),   a.bind (f.comp g) = (a.bind g).bind f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_assoc (f : γ →. δ) (g : β →. γ) (h : α →. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by simp only [comp_apply, Part.bind_comp]

set_option backward.isDefEq.respectTransparency false in
-- This can't be `simp`
/-
**PFun.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：coe_comp (g : β -> γ) (f : α -> β) : ((g ∘ f : α -> γ) : α ->. γ) = (g : β
 ->. γ).comp f
参数：g : β -> γ；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_comp (g : β → γ) (f : α → β) : ((g ∘ f : α → γ) : α →. γ) = (g : β →. γ).comp f :=
  ext fun _ _ => by simp only [coe_val, comp_apply, Function.comp, Part.bind_some]

/-- Product of partial functions. -/
/-
**PFun.prodLift** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：prodLift (f : α ->. β) (g : α ->. γ) : α ->. β × γ
参数：f : α ->. β；g : α ->. γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of partial functions.
-/
def prodLift (f : α →. β) (g : α →. γ) : α →. β × γ := fun x =>
  ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩

@[simp]
/-
**PFun.dom_prodLift** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_prodLift (f : α ->. β) (g : α ->. γ) : (f.prodLift g).Dom = { x | (f x
).Dom ∧ (g x).Dom }
参数：f : α ->. β；g : α ->. γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_prodLift (f : α →. β) (g : α →. γ) :
    (f.prodLift g).Dom = { x | (f x).Dom ∧ (g x).Dom } :=
  rfl
/-
**PFun.get_prodLift** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：get_prodLift (f : α ->. β) (g : α ->. γ) (x : α) (h) : (f.prodLift g x).ge
t h = ((f x).get h.1, (g x).get h.2)
参数：f : α ->. β；g : α ->. γ；x : α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_prodLift (f : α →. β) (g : α →. γ) (x : α) (h) :
    (f.prodLift g x).get h = ((f x).get h.1, (g x).get h.2) :=
  rfl

@[simp]
/-
**PFun.prodLift_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：prodLift_apply (f : α ->. β) (g : α ->. γ) (x : α) : f.prodLift g x = ⟨(f 
x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩
参数：f : α ->. β；g : α ->. γ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodLift_apply (f : α →. β) (g : α →. γ) (x : α) :
    f.prodLift g x = ⟨(f x).Dom ∧ (g x).Dom, fun h => ((f x).get h.1, (g x).get h.2)⟩ :=
  rfl
/-
**PFun.mem_prodLift** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_prodLift {f : α ->. β} {g : α ->. γ} {x : α} {y : β × γ} : y in f.prod
Lift g x ↔ y.1 in f x ∧ y.2 in g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_prodLift {f : α →. β} {g : α →. γ} {x : α} {y : β × γ} :
    y ∈ f.prodLift g x ↔ y.1 ∈ f x ∧ y.2 ∈ g x := by
  trans ∃ hp hq, (f x).get hp = y.1 ∧ (g x).get hq = y.2
  · simp only [prodLift, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

/-- Product of partial functions. -/
/-
**PFun.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `PFun`。
形式化陈述：prodMap (f : α ->. γ) (g : β ->. δ) : α × β ->. γ × δ
参数：f : α ->. γ；g : β ->. δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of partial functions.
-/
def prodMap (f : α →. γ) (g : β →. δ) : α × β →. γ × δ := fun x =>
  ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩

@[simp]
/-
**PFun.dom_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：dom_prodMap (f : α ->. γ) (g : β ->. δ) : (f.prodMap g).Dom = { x | (f x.1
).Dom ∧ (g x.2).Dom }
参数：f : α ->. γ；g : β ->. δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_prodMap (f : α →. γ) (g : β →. δ) :
    (f.prodMap g).Dom = { x | (f x.1).Dom ∧ (g x.2).Dom } :=
  rfl
/-
**PFun.get_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：get_prodMap (f : α ->. γ) (g : β ->. δ) (x : α × β) (h) : (f.prodMap g x).
get h = ((f x.1).get h.1, (g x.2).get h.2)
参数：f : α ->. γ；g : β ->. δ；x : α × β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_prodMap (f : α →. γ) (g : β →. δ) (x : α × β) (h) :
    (f.prodMap g x).get h = ((f x.1).get h.1, (g x.2).get h.2) :=
  rfl

@[simp]
/-
**PFun.prodMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：prodMap_apply (f : α ->. γ) (g : β ->. δ) (x : α × β) : f.prodMap g x = ⟨(
f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩
参数：f : α ->. γ；g : β ->. δ；x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_apply (f : α →. γ) (g : β →. δ) (x : α × β) :
    f.prodMap g x = ⟨(f x.1).Dom ∧ (g x.2).Dom, fun h => ((f x.1).get h.1, (g x.2).get h.2)⟩ :=
  rfl
/-
**PFun.mem_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：mem_prodMap {f : α ->. γ} {g : β ->. δ} {x : α × β} {y : γ × δ} : y in f.p
rodMap g x ↔ y.1 in f x.1 ∧ y.2 in g x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_prodMap {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
    y ∈ f.prodMap g x ↔ y.1 ∈ f x.1 ∧ y.2 ∈ g x.2 := by
  trans ∃ hp hq, (f x.1).get hp = y.1 ∧ (g x.2).get hq = y.2
  · simp only [prodMap, Part.mem_mk_iff, And.exists, Prod.ext_iff]
  · simp only [exists_and_left, exists_and_right, Membership.mem, Part.Mem]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PFun.prodLift_fst_comp_snd_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：prodLift_fst_comp_snd_comp (f : α ->. γ) (g : β ->. δ) : prodLift (f.comp 
((Prod.fst : α × β -> α) : α × β ->. α)) (g.comp ((Prod.snd : α × β -> β) : α × 
β ->. β)) = prodMap f g
参数：f : α ->. γ；g : β ->. δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.get.congr_simp`：∀ {α : Type u} (self self_1 : Part α) (e_self : sel
f = self_1) (a : self.Dom), self.get a = self_1.get ⋯
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prodLift_fst_comp_snd_comp (f : α →. γ) (g : β →. δ) :
    prodLift (f.comp ((Prod.fst : α × β → α) : α × β →. α))
        (g.comp ((Prod.snd : α × β → β) : α × β →. β)) =
      prodMap f g := by
  aesop

@[simp]
/-
**PFun.prodMap_id_id** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：prodMap_id_id : (PFun.id α).prodMap (PFun.id β) = PFun.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodMap_id_id : (PFun.id α).prodMap (PFun.id β) = PFun.id _ := by
  aesop

@[simp]
/-
**PFun.prodMap_comp_comp** 是 Mathlib 中的一个定理，位于命名空间 `PFun`。
形式化陈述：prodMap_comp_comp (f₁ : α ->. β) (f₂ : β ->. γ) (g₁ : δ ->. ε) (g₂ : ε ->.
 ι) : (f₂.comp f₁).prodMap (g₂.comp g₁) = (f₂.prodMap g₂).comp (f₁.prodMap g₁)
参数：f₁ : α ->. β；f₂ : β ->. γ；g₁ : δ ->. ε；g₂ : ε ->. ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PFun.ext`：ext {f g : α ->. β} (H : forall a b, b in f a ↔ b in g a) : f 
= g
-/
theorem prodMap_comp_comp (f₁ : α →. β) (f₂ : β →. γ) (g₁ : δ →. ε) (g₂ : ε →. ι) :
    (f₂.comp f₁).prodMap (g₂.comp g₁) = (f₂.prodMap g₂).comp (f₁.prodMap g₁) :=
  -- `aesop` can prove this but takes over a second, so we do it manually
  ext <| fun ⟨_, _⟩ ⟨_, _⟩ ↦
  ⟨fun ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩ ↦ ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩,
   fun ⟨⟨⟨h1l1, h1r1⟩, ⟨h1l2, h1r2⟩⟩, h2⟩ ↦ ⟨⟨⟨h1l1, h1l2⟩, ⟨h1r1, h1r2⟩⟩, h2⟩⟩

end PFun

