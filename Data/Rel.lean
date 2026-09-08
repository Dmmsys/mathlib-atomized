/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Order.SetNotation

/-!
# Relations as sets of pairs

This file provides API to regard relations between `α` and `β`  as sets of pairs `Set (α × β)`.

This is in particular useful in the study of uniform spaces, which are topological spaces equipped
with a *uniformity*, namely a filter of pairs `α × α` whose elements can be viewed as "proximity"
relations.

## Main declarations

* `SetRel α β`: Type of relations between `α` and `β`.
* `SetRel.inv`: Turn `R : SetRel α β` into `R.inv : SetRel β α` by swapping the arguments.
* `SetRel.dom`: Domain of a relation. `a ∈ R.dom` iff there exists `b` such that `a ~[R] b`.
* `SetRel.cod`: Codomain of a relation. `b ∈ R.cod` iff there exists `a` such that `a ~[R] b`.
* `SetRel.id`: The identity relation `SetRel α α`.
* `SetRel.comp`: SetRel composition. Note that the arguments order follows the category theory
  convention, namely `(R ○ S) a c ↔ ∃ b, a ~[R] b ∧ b ~[S] c`.
* `SetRel.image`: Image of a set under a relation. `b ∈ image R s` iff there exists `a ∈ s`
  such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.image = Set.image f`.
* `SetRel.preimage`: Preimage of a set under a relation. `a ∈ preimage R t` iff there exists
  `b ∈ t` such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.preimage = Set.preimage f`.
* `SetRel.core`: Core of a set. For `t : Set β`, `a ∈ R.core t` iff all `b` related to `a` are in
  `t`.
* `SetRel.restrictDomain`: Domain-restriction of a relation to a subtype.
* `Function.graph`: Graph of a function as a relation.

## Implementation notes

There is tension throughout the library between considering relations between `α` and `β` simply as
`α → β → Prop`, or as a bundled object `SetRel α β` with dedicated operations and API.

The former approach is used almost everywhere as it is very lightweight and has arguably native
support from core Lean features, but it cracks at the seams whenever one starts talking about
operations on relations. For example:
* composition of relations `R : α → β → Prop`, `S : β → γ → Prop` is
  `Relation.Comp R S := fun a c ↦ ∃ b, R a b ∧ S b c`
* map of a relation `R : α → β → Prop` under `f : α → γ`, `g : β → δ` is
  `Relation.Map R f g := fun c d ↦ ∃ a b, r a b ∧ f a = c ∧ g b = d`.

The latter approach is embodied by `SetRel α β`, with the dedicated notation `○` for composition.
(Note that `○` is _not_ the same as function composition `∘`.)

Previously, `SetRel` suffered from the leakage of its definition as
```
def SetRel (α β : Type*) := α → β → Prop
```
The fact that `SetRel` wasn't an `abbrev` confuses automation.
But simply making it an `abbrev` would have killed the point of having a separate less see-through
type to perform relation operations on. So we instead redefined it as
```
abbrev SetRel (α β : Type*) := Set (α × β)
```
This extra level of indirection guides automation correctly and prevents (some kinds of) leakage.

Simultaneously, uniform spaces need a theory of relations on a type `α` as elements of
`Set (α × α)`, and the new definition of `SetRel` fulfills this role quite well.
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction.

We represent them as sets due to how relations are used in the context of uniform spaces. -/
/-
**SetRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SetRel (α β : Type*)
参数：α β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation on `α` and `β`, aka a set-valued function, aka a partial multifunctio
n.

We represent them as sets due to how relations are used in the context of unifor
m spaces.
-/
abbrev SetRel (α β : Type*) := Set (α × β)

namespace SetRel
variable {R R₁ R₂ : SetRel α β} {S : SetRel β γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {a a₁ a₂ : α} {b : β} {c : γ}

/-- Notation for apply a relation `R : SetRel α β` to `a : α`, `b : β`,
scoped to the `SetRel` namespace.

Since `SetRel α β := Set (α × β)`, `a ~[R] b` is simply notation for `(a, b) ∈ R`, but this should
be considered an implementation detail. -/
scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) ∈ R

variable (R) in
/-- The inverse relation : `R.inv x y ↔ R y x`. Note that this is *not* a groupoid inverse. -/
/-
**SetRel.inv** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：inv (R : SetRel α β) : SetRel β α
参数：R : SetRel α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse relation : `R.inv x y ↔ R y x`. Note that this is *not* a groupoid i
nverse.
-/
def inv (R : SetRel α β) : SetRel β α := Prod.swap ⁻¹' R
/-
**SetRel.mem_inv** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {a : α} {b : β}, (b, a) ∈
 R.inv ↔ (a, b) ∈ R
参数：b, a；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_inv : b ~[R.inv] a ↔ a ~[R] b := .rfl
/-
**SetRel.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.inv.inv = R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_inv : R.inv.inv = R := rfl
/-
**SetRel.inv_mono** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β}, R₁ ⊆ R₂ → R₁.inv ⊆ R
₂.inv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma inv_mono (h : R₁ ⊆ R₂) : R₁.inv ⊆ R₂.inv := fun (_a, _b) hab ↦ h hab
/-
**SetRel.inv_empty** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, ∅.inv = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_empty : (∅ : SetRel α β).inv = ∅ := rfl
/-
**SetRel.inv_univ** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, SetRel.inv Set.univ = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_univ : inv (.univ : SetRel α β) = .univ := rfl

variable (R) in
/-- Domain of a relation. -/
/-
**SetRel.dom** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：dom : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Domain of a relation.
-/
def dom : Set α := {a | ∃ b, a ~[R] b}

variable (R) in
/-- Codomain of a relation, aka range. -/
/-
**SetRel.cod** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：cod : Set β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Codomain of a relation, aka range.
-/
def cod : Set β := {b | ∃ a, a ~[R] b}
/-
**SetRel.mem_dom** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {a : α}, a ∈ R.dom ↔ ∃ b,
 (a, b) ∈ R
参数：a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_dom : a ∈ R.dom ↔ ∃ b, a ~[R] b := .rfl
/-
**SetRel.mem_cod** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {b : β}, b ∈ R.cod ↔ ∃ a,
 (a, b) ∈ R
参数：a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_cod : b ∈ R.cod ↔ ∃ a, a ~[R] b := .rfl
/-
**SetRel.dom_mono** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β}, R₁ ⊆ R₂ → R₁.dom ⊆ R
₂.dom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma dom_mono (h : R₁ ≤ R₂) : R₁.dom ⊆ R₂.dom := fun _a ⟨b, hab⟩ ↦ ⟨b, h hab⟩
/-
**SetRel.cod_mono** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β}, R₁ ⊆ R₂ → R₁.cod ⊆ R
₂.cod
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma cod_mono (h : R₁ ≤ R₂) : R₁.cod ⊆ R₂.cod := fun _b ⟨a, hab⟩ ↦ ⟨a, h hab⟩
/-
**SetRel.dom_empty** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, ∅.dom = ∅
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
@[simp] lemma dom_empty : (∅ : SetRel α β).dom = ∅ := by aesop
/-
**SetRel.cod_empty** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, ∅.cod = ∅
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
@[simp] lemma cod_empty : (∅ : SetRel α β).cod = ∅ := by aesop
/-
**SetRel.dom_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.dom = ∅ ↔ R = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SetRel.dom_empty`：∀ {α : Type u_1} {β : Type u_2}, ∅.dom = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma dom_eq_empty_iff : R.dom = ∅ ↔ R = (∅ : SetRel α β) :=
  ⟨fun h ↦ Set.eq_empty_iff_forall_notMem.mpr <| by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ dom_empty)⟩
/-
**SetRel.cod_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.cod = ∅ ↔ R = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SetRel.cod_empty`：∀ {α : Type u_1} {β : Type u_2}, ∅.cod = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma cod_eq_empty_iff : R.cod = ∅ ↔ R = (∅ : SetRel α β) :=
  ⟨fun h ↦ Set.eq_empty_iff_forall_notMem.mpr <| by simp_all [Set.eq_empty_iff_forall_notMem],
   (· ▸ cod_empty)⟩
/-
**SetRel.dom_univ** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Nonempty β], SetRel.dom Set.univ = Set.un
iv
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
@[simp] lemma dom_univ [Nonempty β] : dom (.univ : SetRel α β) = .univ := by aesop
/-
**SetRel.cod_univ** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [Nonempty α], SetRel.cod Set.univ = Set.un
iv
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
@[simp] lemma cod_univ [Nonempty α] : cod (.univ : SetRel α β) = .univ := by aesop
/-
**SetRel.cod_inv** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.inv.cod = R.dom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma cod_inv : R.inv.cod = R.dom := rfl
/-
**SetRel.dom_inv** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.inv.dom = R.cod
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma dom_inv : R.inv.dom = R.cod := rfl

/-- The identity relation. -/
/-
**SetRel.id** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity relation.
-/
protected def id : SetRel α α := {(a₁, a₂) | a₁ = a₂}
/-
**SetRel.mem_id** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {a₁ a₂ : α}, (a₁, a₂) ∈ SetRel.id ↔ a₁ = a₂
参数：a₁, a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_id : a₁ ~[SetRel.id] a₂ ↔ a₁ = a₂ := .rfl

-- Not simp because `SetRel.inv_eq_self` already proves it
/-
**SetRel.inv_id** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：inv_id : (.id : SetRel α α).inv = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_id : (.id : SetRel α α).inv = .id := by aesop

/-- Composition of relation.

Note that this follows the `CategoryTheory` order of arguments. -/
/-
**SetRel.comp** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：comp (R : SetRel α β) (S : SetRel β γ) : SetRel α γ
参数：R : SetRel α β；S : SetRel β γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of relation.

Note that this follows the `CategoryTheory` order of arguments.
-/
def comp (R : SetRel α β) (S : SetRel β γ) : SetRel α γ := {(a, c) | ∃ b, a ~[R] b ∧ b ~[S] c}

@[inherit_doc] scoped infixl:62 " ○ " => comp
/-
**SetRel.mem_comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {R : SetRel α β} {S : SetRe
l β γ} {a : α} {c : γ},   (a, c) ∈ R.comp S ↔ ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S
参数：a, c；a, b；b, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_comp : a ~[R ○ S] c ↔ ∃ b, a ~[R] b ∧ b ~[S] c := .rfl
/-
**SetRel.prodMk_mem_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c) : a ~[R ○ S] c
参数：hab : a ~[R] b；hbc : b ~[S] c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c) : a ~[R ○ S] c := ⟨b, hab, hbc⟩
/-
**SetRel.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_assoc (R : SetRel α β) (S : SetRel β γ) (t : SetRel γ δ) : (R ○ S) ○ 
t = R ○ (S ○ t)
参数：R : SetRel α β；S : SetRel β γ；t : SetRel γ δ。
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
lemma comp_assoc (R : SetRel α β) (S : SetRel β γ) (t : SetRel γ δ) :
    (R ○ S) ○ t = R ○ (S ○ t) := by aesop
/-
**SetRel.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β), R.comp SetRel.id = R
参数：R : SetRel α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma comp_id (R : SetRel α β) : R ○ .id = R := by aesop
/-
**SetRel.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β), SetRel.id.comp R = R
参数：R : SetRel α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma id_comp (R : SetRel α β) : .id ○ R = R := by aesop
/-
**SetRel.inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (R : SetRel α β) (S : SetRe
l β γ), (R.comp S).inv = S.inv.comp R.inv
参数：R : SetRel α β；S : SetRel β γ；R.comp S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma inv_comp (R : SetRel α β) (S : SetRel β γ) : (R ○ S).inv = S.inv ○ R.inv := by aesop
/-
**SetRel.comp_empty** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (R : SetRel α β), R.comp ∅ 
= ∅
参数：R : SetRel α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma comp_empty (R : SetRel α β) : R ○ (∅ : SetRel β γ) = ∅ := by aesop
/-
**SetRel.empty_comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (S : SetRel β γ), ∅.comp S 
= ∅
参数：S : SetRel β γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma empty_comp (S : SetRel β γ) : (∅ : SetRel α β) ○ S = ∅ := by aesop
/-
**SetRel.comp_univ** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (R : SetRel α β), R.comp Se
t.univ = {(a, _c) | a ∈ R.dom}
参数：R : SetRel α β；a, _c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma comp_univ (R : SetRel α β) :
    R ○ (.univ : SetRel β γ) = {(a, _c) : α × γ | a ∈ R.dom} := by
  aesop
/-
**SetRel.univ_comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (S : SetRel β γ), SetRel.co
mp Set.univ S = {(_b, c) | c ∈ S.cod}
参数：S : SetRel β γ；_b, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma univ_comp (S : SetRel β γ) :
    (.univ : SetRel α β) ○ S = {(_b, c) : α × γ | c ∈ S.cod} := by
  aesop
/-
**SetRel.comp_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_iUnion (R : SetRel α β) (S : ι -> SetRel β γ) : R ○ ⋃ i, S i = ⋃ i, R
 ○ S i
参数：R : SetRel α β；S : ι -> SetRel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma comp_iUnion (R : SetRel α β) (S : ι → SetRel β γ) : R ○ ⋃ i, S i = ⋃ i, R ○ S i := by aesop
/-
**SetRel.iUnion_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：iUnion_comp (R : ι -> SetRel α β) (S : SetRel β γ) : (⋃ i, R i) ○ S = ⋃ i,
 R i ○ S
参数：R : ι -> SetRel α β；S : SetRel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma iUnion_comp (R : ι → SetRel α β) (S : SetRel β γ) : (⋃ i, R i) ○ S = ⋃ i, R i ○ S := by aesop
/-
**SetRel.comp_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_sUnion (R : SetRel α β) (𝒮 : Set (SetRel β γ)) : R ○ ⋃₀ 𝒮 = ⋃ S in 𝒮,
 R ○ S
参数：R : SetRel α β；𝒮 : Set (SetRel β γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma comp_sUnion (R : SetRel α β) (𝒮 : Set (SetRel β γ)) : R ○ ⋃₀ 𝒮 = ⋃ S ∈ 𝒮, R ○ S := by aesop
/-
**SetRel.sUnion_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：sUnion_comp (ℛ : Set (SetRel α β)) (S : SetRel β γ) : ⋃₀ ℛ ○ S = ⋃ R in ℛ,
 R ○ S
参数：ℛ : Set (SetRel α β)；S : SetRel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma sUnion_comp (ℛ : Set (SetRel α β)) (S : SetRel β γ) : ⋃₀ ℛ ○ S = ⋃ R ∈ ℛ, R ○ S := by aesop

@[gcongr]
/-
**SetRel.comp_subset_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ subseteq R₂) (hS : S₁ subse
teq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
参数：hR : R₁ subseteq R₂；hS : S₁ subseteq S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
-/
lemma comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ ⊆ R₂) (hS : S₁ ⊆ S₂) : R₁ ○ S₁ ⊆ R₂ ○ S₂ :=
  fun _ ↦ .imp fun _ ↦ .imp (@hR _) (@hS _)

@[gcongr]
/-
**SetRel.comp_subset_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_subset_comp_left {S : SetRel β γ} (hR : R₁ subseteq R₂) : R₁ ○ S subs
eteq R₂ ○ S
参数：hR : R₁ subseteq R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma comp_subset_comp_left {S : SetRel β γ} (hR : R₁ ⊆ R₂) : R₁ ○ S ⊆ R₂ ○ S :=
  comp_subset_comp hR .rfl

@[gcongr]
/-
**SetRel.comp_subset_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_subset_comp_right {S₁ S₂ : SetRel β γ} (hS : S₁ subseteq S₂) : R ○ S₁
 subseteq R ○ S₂
参数：hS : S₁ subseteq S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma comp_subset_comp_right {S₁ S₂ : SetRel β γ} (hS : S₁ ⊆ S₂) : R ○ S₁ ⊆ R ○ S₂ :=
  comp_subset_comp .rfl hS
/-
**SetRel._root_.Monotone.relComp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Monotone.relComp {ι : Type*} [Preorder ι] {f : ι → SetRel α β}
    {g : ι → SetRel β γ} (hf : Monotone f) (hg : Monotone g) : Monotone fun x ↦ f x ○ g x :=
  fun _i _j hij ⟨_a, _c⟩ ⟨b, hab, hbc⟩ ↦ ⟨b, hf hij hab, hg hij hbc⟩
/-
**SetRel.prod_comp_prod_of_inter_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：prod_comp_prod_of_inter_nonempty (ht : (t₁ inter t₂).Nonempty) (s : Set α)
 (u : Set γ) : s ×ˢ t₁ ○ t₂ ×ˢ u = s ×ˢ u
参数：ht : (t₁ inter t₂).Nonempty；s : Set α；u : Set γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma prod_comp_prod_of_inter_nonempty (ht : (t₁ ∩ t₂).Nonempty) (s : Set α) (u : Set γ) :
    s ×ˢ t₁ ○ t₂ ×ˢ u = s ×ˢ u := by aesop
/-
**SetRel.prod_comp_prod_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：prod_comp_prod_of_disjoint (ht : Disjoint t₁ t₂) (s : Set α) (u : Set γ) :
 s ×ˢ t₁ ○ t₂ ×ˢ u = ∅
参数：ht : Disjoint t₁ t₂；s : Set α；u : Set γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
-/
lemma prod_comp_prod_of_disjoint (ht : Disjoint t₁ t₂) (s : Set α) (u : Set γ) :
    s ×ˢ t₁ ○ t₂ ×ˢ u = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_z, ⟨_, hzs⟩, hzu, _⟩ ↦ Set.disjoint_left.1 ht hzs hzu
/-
**SetRel.prod_comp_prod** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：prod_comp_prod (s : Set α) (t₁ t₂ : Set β) (u : Set γ) [Decidable (Disjoin
t t₁ t₂)] : s ×ˢ t₁ ○ t₂ ×ˢ u = if Disjoint t₁ t₂ then ∅ else s ×ˢ u
参数：s : Set α；t₁ t₂ : Set β；u : Set γ；Disjoint t₁ t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `SetRel.prod_comp_prod_of_disjoint`：prod_comp_prod_of_disjoint (ht : Disj
oint t₁ t₂) (s : Set α) (u : Set γ) : s ×ˢ t₁ ○ t₂ ×ˢ u = ∅
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `SetRel.prod_comp_prod_of_inter_nonempty`：prod_comp_prod_of_inter_nonempt
y (ht : (t₁ inter t₂).Nonempty) (s : Set α) (u : Set γ) : s ×ˢ t₁ ○ t₂ ×ˢ u = s 
×ˢ u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
-/
lemma prod_comp_prod (s : Set α) (t₁ t₂ : Set β) (u : Set γ) [Decidable (Disjoint t₁ t₂)] :
    s ×ˢ t₁ ○ t₂ ×ˢ u = if Disjoint t₁ t₂ then ∅ else s ×ˢ u := by
  split_ifs with hst
  · exact prod_comp_prod_of_disjoint hst ..
  · rw [prod_comp_prod_of_inter_nonempty <| Set.not_disjoint_iff_nonempty_inter.1 hst]

variable (R s) in
/-- Image of a set under a relation. -/
/-
**SetRel.image** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：image : Set β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image of a set under a relation.
-/
def image : Set β := {b | ∃ a ∈ s, a ~[R] b}

variable (R t) in
/-- Preimage of a set `t` under a relation `R`. Same as the image of `t` under `R.inv`. -/
/-
**SetRel.preimage** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：preimage : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of a set `t` under a relation `R`. Same as the image of `t` under `R.in
v`.
-/
def preimage : Set α := {a | ∃ b ∈ t, a ~[R] b}
/-
**SetRel.mem_image** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {s : Set α} {b : β}, b ∈ 
R.image s ↔ ∃ a ∈ s, (a, b) ∈ R
参数：a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_image : b ∈ image R s ↔ ∃ a ∈ s, a ~[R] b := .rfl
/-
**SetRel.mem_preimage** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {t : Set β} {a : α}, a ∈ 
R.preimage t ↔ ∃ b ∈ t, (a, b) ∈ R
参数：a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_preimage : a ∈ preimage R t ↔ ∃ b ∈ t, a ~[R] b := .rfl
/-
**SetRel.image_subset_image** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {s₁ s₂ : Set α}, s₁ ⊆ s₂ 
→ R.image s₁ ⊆ R.image s₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma image_subset_image (hs : s₁ ⊆ s₂) : image R s₁ ⊆ image R s₂ :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, hs ha, hab⟩
/-
**SetRel.image_subset_image_left** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β} {s : Set α}, R₁ ⊆ R₂ 
→ R₁.image s ⊆ R₂.image s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma image_subset_image_left (hR : R₁ ⊆ R₂) : image R₁ s ⊆ image R₂ s :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, ha, hR hab⟩
/-
**SetRel.preimage_subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ 
→ R.preimage t₁ ⊆ R.preimage t₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma preimage_subset_preimage (ht : t₁ ⊆ t₂) : preimage R t₁ ⊆ preimage R t₂ :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, ht ha, hab⟩
/-
**SetRel.preimage_subset_preimage_left** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β} {t : Set β}, R₁ ⊆ R₂ 
→ R₁.preimage t ⊆ R₂.preimage t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma preimage_subset_preimage_left (hR : R₁ ⊆ R₂) : preimage R₁ t ⊆ preimage R₂ t :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, ha, hR hab⟩

variable (R t) in
/-
**SetRel.image_inv** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β) (t : Set β), R.inv.image 
t = R.preimage t
参数：R : SetRel α β；t : Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma image_inv : R.inv.image t = preimage R t := rfl

variable (R s) in
/-
**SetRel.preimage_inv** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β) (s : Set α), R.inv.preima
ge s = R.image s
参数：R : SetRel α β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_inv : R.inv.preimage s = image R s := rfl
/-
**SetRel.image_mono** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_mono : Monotone R.image
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.image_subset_image`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α
 β} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → R.image s₁ ⊆ R.image s₂
-/
lemma image_mono : Monotone R.image := fun _ _ ↦ image_subset_image
/-
**SetRel.preimage_mono** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_mono : Monotone R.preimage
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.preimage_subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {R : Se
tRel α β} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → R.preimage t₁ ⊆ R.preimage t₂
-/
lemma preimage_mono : Monotone R.preimage := fun _ _ ↦ preimage_subset_preimage
/-
**SetRel.image_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.image ∅ = ∅
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
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma image_empty_right : image R ∅ = ∅ := by aesop
/-
**SetRel.preimage_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.preimage ∅ = ∅
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
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_empty_right : preimage R ∅ = ∅ := by aesop
/-
**SetRel.image_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.image Set.univ = R.cod
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
@[simp] lemma image_univ_right : image R .univ = R.cod := by aesop
/-
**SetRel.preimage_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.preimage Set.univ = R.
dom
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
@[simp] lemma preimage_univ_right : preimage R .univ = R.dom := by aesop

variable (R) in
/-
**SetRel.image_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_inter_subset : image R (s₁ inter s₂) subseteq image R s₁ inter image
 R s₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用引理 `SetRel.image_mono`：image_mono : Monotone R.image
-/
lemma image_inter_subset : image R (s₁ ∩ s₂) ⊆ image R s₁ ∩ image R s₂ := image_mono.map_inf_le ..

variable (R) in
/-
**SetRel.preimage_inter_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_inter_subset : preimage R (t₁ inter t₂) subseteq preimage R t₁ in
ter preimage R t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用引理 `SetRel.preimage_mono`：preimage_mono : Monotone R.preimage
-/
lemma preimage_inter_subset : preimage R (t₁ ∩ t₂) ⊆ preimage R t₁ ∩ preimage R t₂ :=
  preimage_mono.map_inf_le ..

variable (R s₁ s₂) in
/-
**SetRel.image_union** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_union : image R (s₁ union s₂) = image R s₁ union image R s₂
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma image_union : image R (s₁ ∪ s₂) = image R s₁ ∪ image R s₂ := by aesop

variable (R) in
/-
**SetRel.image_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_iUnion (s : ι -> Set α) : image R (⋃ i, s i) = ⋃ i, image R (s i)
参数：s : ι -> Set α。
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
lemma image_iUnion (s : ι → Set α) : image R (⋃ i, s i) = ⋃ i, image R (s i) := by aesop

variable (R) in
/-
**SetRel.image_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_sUnion (S : Set (Set α)) : image R (⋃₀ S) = ⋃ s in S, image R s
参数：S : Set (Set α)。
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma image_sUnion (S : Set (Set α)) : image R (⋃₀ S) = ⋃ s ∈ S, image R s := by aesop

variable (R t₁ t₂) in
/-
**SetRel.preimage_union** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_union : preimage R (t₁ union t₂) = preimage R t₁ union preimage R
 t₂
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma preimage_union : preimage R (t₁ ∪ t₂) = preimage R t₁ ∪ preimage R t₂ := by aesop

variable (R) in
/-
**SetRel.preimage_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_iUnion (t : ι -> Set β) : preimage R (⋃ i, t i) = ⋃ i, preimage R
 (t i)
参数：t : ι -> Set β。
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
lemma preimage_iUnion (t : ι → Set β) : preimage R (⋃ i, t i) = ⋃ i, preimage R (t i) := by aesop

variable (R) in
/-
**SetRel.preimage_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_sUnion (T : Set (Set β)) : preimage R (⋃₀ T) = ⋃ t in T, preimage
 R t
参数：T : Set (Set β)。
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma preimage_sUnion (T : Set (Set β)) : preimage R (⋃₀ T) = ⋃ t ∈ T, preimage R t := by aesop

variable (s) in
/-
**SetRel.image_id** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (s : Set α), SetRel.id.image s = s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma image_id : image .id s = s := by aesop

variable (s) in
/-
**SetRel.preimage_id** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (s : Set α), SetRel.id.preimage s = s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma preimage_id : preimage .id s = s := by aesop

variable (R S s) in
/-
**SetRel.image_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_comp : image (R ○ S) s = image S (image R s)
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
lemma image_comp : image (R ○ S) s = image S (image R s) := by aesop

variable (R S u) in
/-
**SetRel.preimage_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_comp : preimage (R ○ S) u = preimage R (preimage S u)
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
lemma preimage_comp : preimage (R ○ S) u = preimage R (preimage S u) := by aesop

variable (s) in
/-
**SetRel.image_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (s : Set α), ∅.image s = ∅
参数：s : Set α。
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
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma image_empty_left : image (∅ : SetRel α β) s = ∅ := by aesop

variable (t) in
/-
**SetRel.preimage_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (t : Set β), ∅.preimage t = ∅
参数：t : Set β。
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
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_empty_left : preimage (∅ : SetRel α β) t = ∅ := by aesop
/-
**SetRel.image_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonempty → SetRel.image Set
.univ s = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
@[simp] lemma image_univ_left (hs : s.Nonempty) : image (.univ : SetRel α β) s = .univ := by aesop
/-
**SetRel.preimage_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {t : Set β}, t.Nonempty → SetRel.preimage 
Set.univ t = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
@[simp] lemma preimage_univ_left (ht : t.Nonempty) : preimage (.univ : SetRel α β) t = .univ := by
  aesop
/-
**SetRel.image_eq_cod_of_dom_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_eq_cod_of_dom_subset (h : R.dom subseteq s) : R.image s = R.cod
参数：h : R.dom subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma image_eq_cod_of_dom_subset (h : R.dom ⊆ s) : R.image s = R.cod := by aesop
/-
**SetRel.preimage_eq_dom_of_cod_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_eq_dom_of_cod_subset (h : R.cod subseteq t) : R.preimage t = R.do
m
参数：h : R.cod subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma preimage_eq_dom_of_cod_subset (h : R.cod ⊆ t) : R.preimage t = R.dom := by aesop

variable (R s) in
/-
**SetRel.image_inter_dom** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β) (s : Set α), R.image (s ∩
 R.dom) = R.image s
参数：R : SetRel α β；s : Set α；s ∩ R.dom。
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] lemma image_inter_dom : image R (s ∩ R.dom) = image R s := by aesop

variable (R t) in
/-
**SetRel.preimage_inter_cod** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β) (t : Set β), R.preimage (
t ∩ R.cod) = R.preimage t
参数：R : SetRel α β；t : Set β；t ∩ R.cod。
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] lemma preimage_inter_cod : preimage R (t ∩ R.cod) = preimage R t := by aesop
/-
**SetRel.inter_dom_subset_preimage_image** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：inter_dom_subset_preimage_image : s inter R.dom subseteq R.preimage (image
 R s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma inter_dom_subset_preimage_image : s ∩ R.dom ⊆ R.preimage (image R s) := by
  aesop (add simp [Set.subset_def])
/-
**SetRel.inter_cod_subset_image_preimage** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：inter_cod_subset_image_preimage : t inter R.cod subseteq image R (R.preima
ge t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma inter_cod_subset_image_preimage : t ∩ R.cod ⊆ image R (R.preimage t) := by
  aesop (add simp [Set.subset_def])
/-
**SetRel.image_eq_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_eq_biUnion : R.image s = ⋃ x in s, {y | x ~[R] y}
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_eq_biUnion : R.image s = ⋃ x ∈ s, {y | x ~[R] y} := by aesop
/-
**SetRel.preimage_eq_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_eq_biUnion : R.preimage t = ⋃ y in t, {x | x ~[R] y}
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_eq_biUnion : R.preimage t = ⋃ y ∈ t, {x | x ~[R] y} := by aesop

variable (R t) in
/-- Core of a set `S : Set β` w.R.t `R : SetRel α β` is the set of `x : α` that are related *only*
to elements of `S`. Other generalization of `Function.preimage`. -/
/-
**SetRel.core** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：core : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Core of a set `S : Set β` w.R.t `R : SetRel α β` is the set of `x : α` that are 
related *only*
to elements of `S`. Other generalization of `Function.preimage`.
-/
def core : Set α := {a | ∀ ⦃b⦄, a ~[R] b → b ∈ t}
/-
**SetRel.mem_core** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β} {t : Set β} {a : α}, a ∈ 
R.core t ↔ ∀ ⦃b : β⦄, (a, b) ∈ R → b ∈ t
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_core : a ∈ R.core t ↔ ∀ ⦃b⦄, a ~[R] b → b ∈ t := .rfl

@[gcongr]
/-
**SetRel.core_subset_core** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：core_subset_core (ht : t₁ subseteq t₂) : R.core t₁ subseteq R.core t₂
参数：ht : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma core_subset_core (ht : t₁ ⊆ t₂) : R.core t₁ ⊆ R.core t₂ := fun _a ha _b hab ↦ ht <| ha hab
/-
**SetRel.core_mono** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：core_mono : Monotone R.core
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.core_subset_core`：core_subset_core (ht : t₁ subseteq t₂) : R.core
 t₁ subseteq R.core t₂
-/
lemma core_mono : Monotone R.core := fun _ _ ↦ core_subset_core

variable (R t₁ t₂) in
/-
**SetRel.core_inter** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：core_inter : R.core (t₁ inter t₂) = R.core t₁ inter R.core t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma core_inter : R.core (t₁ ∩ t₂) = R.core t₁ ∩ R.core t₂ := by aesop
/-
**SetRel.core_union_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：core_union_subset : R.core t₁ union R.core t₂ subseteq R.core (t₁ union t₂
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用引理 `SetRel.core_mono`：core_mono : Monotone R.core
-/
lemma core_union_subset : R.core t₁ ∪ R.core t₂ ⊆ R.core (t₁ ∪ t₂) := core_mono.le_map_sup ..
/-
**SetRel.core_univ** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β}, R.core Set.univ = Set.un
iv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma core_univ : R.core Set.univ = Set.univ := by aesop

variable (t) in
/-
**SetRel.core_id** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {β : Type u_2} (t : Set β), SetRel.id.core t = t
参数：t : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma core_id : core .id t = t := by aesop

variable (R S u) in
/-
**SetRel.core_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：core_comp : core (R ○ S) u = core R (core S u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma core_comp : core (R ○ S) u = core R (core S u) := by aesop
/-
**SetRel.image_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_subset_iff : image R s subseteq t ↔ s subseteq core R t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma image_subset_iff : image R s ⊆ t ↔ s ⊆ core R t := by aesop (add simp [Set.subset_def])
/-
**SetRel.image_core_gc** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：image_core_gc : GaloisConnection R.image R.core
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.image_subset_iff`：image_subset_iff : image R s subseteq t ↔ s sub
seteq core R t
-/
lemma image_core_gc : GaloisConnection R.image R.core := fun _ _ ↦ image_subset_iff

variable (R s) in
/-- Restrict the domain of a relation to a subtype. -/
/-
**SetRel.restrictDomain** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：restrictDomain : SetRel s β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the domain of a relation to a subtype.
-/
def restrictDomain : SetRel s β := {(a, b) | ↑a ~[R] b}

variable {R R₁ R₂ : SetRel α α} {S : SetRel β β} {a b c : α}

/-! ### Reflexive relations -/

variable (R) in
/-- A relation `R` is reflexive if `a ~[R] a`. -/
/-
**SetRel.IsRefl** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `R` is reflexive if `a ~[R] a`.
-/
protected abbrev IsRefl : Prop := Std.Refl (· ~[R] ·)

variable (R) in
/-
**SetRel.refl** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) [R.IsRefl] (a : α), (a, a) ∈ R
参数：R : SetRel α α；a : α；a, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
-/
protected lemma refl [R.IsRefl] (a : α) : a ~[R] a := refl_of (· ~[R] ·) a

variable (R) in
/-
**SetRel.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a) ∈ R
参数：R : SetRel α α；a, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.refl`：∀ {α : Type u_1} (R : SetRel α α) [R.IsRefl] (a : α), (a, a
) ∈ R
-/
protected lemma rfl [R.IsRefl] : a ~[R] a := R.refl a
/-
**SetRel.id_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：id_subset [R.IsRefl] : .id subseteq R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
lemma id_subset [R.IsRefl] : .id ⊆ R := by rintro ⟨_, _⟩ rfl; exact R.rfl
/-
**SetRel.id_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：id_subset_iff : .id subseteq R ↔ R.IsRefl where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.id_subset`：id_subset [R.IsRefl] : .id subseteq R
-/
lemma id_subset_iff : .id ⊆ R ↔ R.IsRefl where
  mp h := ⟨fun _ ↦ h rfl⟩
  mpr _ := id_subset
/-
**SetRel.isRefl_univ** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isRefl_univ : SetRel.IsRefl (.univ : SetRel α α) where refl _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance isRefl_univ : SetRel.IsRefl (.univ : SetRel α α) where
  refl _ := trivial
/-
**SetRel.isRefl_inter** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isRefl_inter [R₁.IsRefl] [R₂.IsRefl] : (R₁ inter R₂).IsRefl where refl _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
instance isRefl_inter [R₁.IsRefl] [R₂.IsRefl] : (R₁ ∩ R₂).IsRefl where
  refl _ := ⟨R₁.rfl, R₂.rfl⟩
/-
**SetRel.IsRefl.comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsRefl`。
形式化陈述：∀ {α : Type u_1} {R₁ R₂ : SetRel α α} [R₁.IsRefl] [R₂.IsRefl], (R₁.comp R₂
).IsRefl
参数：R₁.comp R₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
instance IsRefl.comp [R₁.IsRefl] [R₂.IsRefl] : (R₁.comp R₂).IsRefl where
  refl _ := ⟨_, R₁.rfl, R₂.rfl⟩
/-
**SetRel.IsRefl.sInter** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsRefl`。
形式化陈述：∀ {α : Type u_1} {ℛ : Set (SetRel α α)}, (∀ R ∈ ℛ, R.IsRefl) → SetRel.IsRe
fl (⋂₀ ℛ)
参数：SetRel α α；∀ R ∈ ℛ, R.IsRefl；⋂₀ ℛ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
-/
protected lemma IsRefl.sInter {ℛ : Set <| SetRel α α} (hℛ : ∀ R ∈ ℛ, R.IsRefl) :
    SetRel.IsRefl (⋂₀ ℛ) where
  refl _a R hR := (hℛ R hR).refl _
/-
**SetRel.isRefl_iInter** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isRefl_iInter {R : ι -> SetRel α α} [forall i, (R i).IsRefl] : SetRel.IsRe
fl (⋂ i, R i)
参数：R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsRefl.sInter`：∀ {α : Type u_1} {ℛ : Set (SetRel α α)}, (∀ R ∈ ℛ,
 R.IsRefl) → SetRel.IsRefl (⋂₀ ℛ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance isRefl_iInter {R : ι → SetRel α α} [∀ i, (R i).IsRefl] :
    SetRel.IsRefl (⋂ i, R i) := .sInter <| by simpa
/-
**SetRel.isRefl_preimage** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isRefl_preimage {f : β -> α} [R.IsRefl] : SetRel.IsRefl (Prod.map f f ⁻¹' 
R) where refl _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
instance isRefl_preimage {f : β → α} [R.IsRefl] : SetRel.IsRefl (Prod.map f f ⁻¹' R) where
  refl _ := R.rfl
/-
**SetRel.isRefl_mono** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：isRefl_mono [R₁.IsRefl] (hR : R₁ subseteq R₂) : R₂.IsRefl where refl _
参数：hR : R₁ subseteq R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
lemma isRefl_mono [R₁.IsRefl] (hR : R₁ ⊆ R₂) : R₂.IsRefl where refl _ := hR R₁.rfl
/-
**SetRel.left_subset_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：left_subset_comp {R : SetRel α β} [S.IsRefl] : R subseteq R ○ S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetRel.comp_id`：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β), R.comp
 SetRel.id = R
· 使用引理 `SetRel.comp_subset_comp_right`：comp_subset_comp_right {S₁ S₂ : SetRel β 
γ} (hS : S₁ subseteq S₂) : R ○ S₁ subseteq R ○ S₂
· 使用引理 `SetRel.id_subset`：id_subset [R.IsRefl] : .id subseteq R
-/
lemma left_subset_comp {R : SetRel α β} [S.IsRefl] : R ⊆ R ○ S := by
  simpa using comp_subset_comp_right id_subset
/-
**SetRel.right_subset_comp** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：right_subset_comp [R.IsRefl] {S : SetRel α β} : S subseteq R ○ S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetRel.id_comp`：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β), SetRel
.id.comp R = R
· 使用引理 `SetRel.comp_subset_comp_left`：comp_subset_comp_left {S : SetRel β γ} (hR
 : R₁ subseteq R₂) : R₁ ○ S subseteq R₂ ○ S
· 使用引理 `SetRel.id_subset`：id_subset [R.IsRefl] : .id subseteq R
-/
lemma right_subset_comp [R.IsRefl] {S : SetRel α β} : S ⊆ R ○ S := by
  simpa using comp_subset_comp_left id_subset
/-
**SetRel.subset_iterate_comp** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α α} [R.IsRefl] {S : SetRel α 
β} {n : ℕ}, S ⊆ (fun x => R.comp x)^[n] S
参数：fun x => R.comp x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subset_iterate_comp [R.IsRefl] {S : SetRel α β} : ∀ {n}, S ⊆ (R ○ ·)^[n] S
  | 0 => .rfl
  | _n + 1 => right_subset_comp.trans subset_iterate_comp
/-
**SetRel.self_subset_image** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：self_subset_image [R.IsRefl] (s : Set α) : s subseteq R.image s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
lemma self_subset_image [R.IsRefl] (s : Set α) : s ⊆ R.image s :=
  fun x hx => ⟨x, hx, R.rfl⟩
/-
**SetRel.self_subset_preimage** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：self_subset_preimage [R.IsRefl] (s : Set α) : s subseteq R.preimage s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
lemma self_subset_preimage [R.IsRefl] (s : Set α) : s ⊆ R.preimage s :=
  fun x hx => ⟨x, hx, R.rfl⟩
/-
**SetRel.exists_eq_singleton_of_prod_subset_id** 是 Mathlib 中的一个引理，位于命名空间 `SetRel
`。
形式化陈述：exists_eq_singleton_of_prod_subset_id {s t : Set α} (hs : s.Nonempty) (ht 
: t.Nonempty) (hst : s ×ˢ t subseteq SetRel.id) : exists x, s = {x} ∧ t = {x}
参数：hs : s.Nonempty；ht : t.Nonempty；hst : s ×ˢ t subseteq SetRel.id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_eq_singleton_of_prod_subset_id {s t : Set α} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ×ˢ t ⊆ SetRel.id) : ∃ x, s = {x} ∧ t = {x} := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  simp only [Set.prod_subset_iff, mem_id] at hst
  obtain rfl := hst _ ha _ hb
  simp only [Set.eq_singleton_iff_unique_mem, and_assoc]
  exact ⟨a, ha, (hst · · _ hb), hb, (hst _ ha · · |>.symm)⟩

/-! ### Symmetric relations -/

variable (R) in
/-- A relation `R` is symmetric if `a ~[R] b ↔ b ~[R] a`. -/
/-
**SetRel.IsSymm** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `R` is symmetric if `a ~[R] b ↔ b ~[R] a`.
-/
protected abbrev IsSymm : Prop := Std.Symm (· ~[R] ·)

variable (R) in
/-
**SetRel.symm** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a, b) ∈ R → (b, a
) ∈ R
参数：R : SetRel α α；a, b；b, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
protected lemma symm [R.IsSymm] (hab : a ~[R] b) : b ~[R] a := symm_of (· ~[R] ·) hab

variable (R) in
/-
**SetRel.comm** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a, b) ∈ R ↔ (b, a
) ∈ R
参数：R : SetRel α α；a, b；b, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comm_of`：comm_of (r : α -> α -> Prop) [Std.Symm r] {a b : α} : r a b ↔ r
 b a
-/
protected lemma comm [R.IsSymm] : a ~[R] b ↔ b ~[R] a := comm_of (· ~[R] ·)

variable (R) in
/-
**SetRel.inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv = R
参数：R : SetRel α α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SetRel.comm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R ↔ (b, a) ∈ R
-/
@[simp] lemma inv_eq_self [R.IsSymm] : R.inv = R := by ext; exact R.comm
/-
**SetRel.inv_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：inv_eq_self_iff : R.inv = R ↔ R.IsSymm where mp hR
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
-/
lemma inv_eq_self_iff : R.inv = R ↔ R.IsSymm where
  mp hR := ⟨fun a b hab ↦ by rwa [← hR]⟩
  mpr _ := inv_eq_self _
/-
**SetRel.** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.IsSymm] : R.inv.IsSymm := by simpa
/-
**SetRel.isSymm_empty** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_empty : (∅ : SetRel α α).IsSymm where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance isSymm_empty : (∅ : SetRel α α).IsSymm where symm _ _ := by simp
/-
**SetRel.isSymm_univ** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_univ : SetRel.IsSymm (Set.univ : SetRel α α) where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance isSymm_univ : SetRel.IsSymm (Set.univ : SetRel α α) where symm _ _ := by simp
/-
**SetRel.isSymm_inter** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_inter [R₁.IsSymm] [R₂.IsSymm] : (R₁ inter R₂).IsSymm where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
-/
instance isSymm_inter [R₁.IsSymm] [R₂.IsSymm] : (R₁ ∩ R₂).IsSymm where
  symm _ _ := .imp R₁.symm R₂.symm
/-
**SetRel.IsSymm.sInter** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSymm`。
形式化陈述：∀ {α : Type u_1} {ℛ : Set (SetRel α α)}, (∀ R ∈ ℛ, R.IsSymm) → SetRel.IsSy
mm (⋂₀ ℛ)
参数：SetRel α α；∀ R ∈ ℛ, R.IsSymm；⋂₀ ℛ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
-/
protected lemma IsSymm.sInter {ℛ : Set <| SetRel α α} (hℛ : ∀ R ∈ ℛ, R.IsSymm) :
    SetRel.IsSymm (⋂₀ ℛ) where
  symm _a _b hab R hR := (hℛ R hR).symm _ _ <| hab R hR
/-
**SetRel.isSymm_iInter** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_iInter {R : ι -> SetRel α α} [forall i, (R i).IsSymm] : SetRel.IsSy
mm (⋂ i, R i)
参数：R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsSymm.sInter`：∀ {α : Type u_1} {ℛ : Set (SetRel α α)}, (∀ R ∈ ℛ,
 R.IsSymm) → SetRel.IsSymm (⋂₀ ℛ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance isSymm_iInter {R : ι → SetRel α α} [∀ i, (R i).IsSymm] :
    SetRel.IsSymm (⋂ i, R i) := .sInter <| by simpa
/-
**SetRel.isSymm_id** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_id : (SetRel.id : SetRel α α).IsSymm where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance isSymm_id : (SetRel.id : SetRel α α).IsSymm where symm _ _ := .symm
/-
**SetRel.isSymm_preimage** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_preimage {f : β -> α} [R.IsSymm] : SetRel.IsSymm (Prod.map f f ⁻¹' 
R) where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
-/
instance isSymm_preimage {f : β → α} [R.IsSymm] : SetRel.IsSymm (Prod.map f f ⁻¹' R) where
  symm _ _ := R.symm
/-
**SetRel.isSymm_image** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_image {f : α -> β} [R.IsSymm] : SetRel.IsSymm (Prod.map f f '' R) w
here symm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
-/
instance isSymm_image {f : α → β} [R.IsSymm] : SetRel.IsSymm (Prod.map f f '' R) where
  symm := by
    simp only [Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq, forall_exists_index,
      and_imp]
    rintro _ _ a₁ a₂ ha rfl rfl
    exact ⟨_, _, R.symm ha, rfl, rfl⟩
/-
**SetRel.isSymm_comp_inv** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_comp_inv : (R ○ R.inv).IsSymm where symm a c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isSymm_comp_inv : (R ○ R.inv).IsSymm where
  symm a c := by rintro ⟨b, hab, hbc⟩; exact ⟨b, hbc, hab⟩
/-
**SetRel.isSymm_inv_comp** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_inv_comp : (R.inv ○ R).IsSymm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isSymm_inv_comp : (R.inv ○ R).IsSymm := isSymm_comp_inv
/-
**SetRel.isSymm_comp_self** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_comp_self [R.IsSymm] : (R ○ R).IsSymm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
-/
instance isSymm_comp_self [R.IsSymm] : (R ○ R).IsSymm := by simpa using R.isSymm_comp_inv
/-
**SetRel.prod_subset_comm** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：prod_subset_comm [R.IsSymm] : s₁ ×ˢ s₂ subseteq R ↔ s₂ ×ˢ s₁ subseteq R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
· 使用定理 `SetRel.inv.eq_1`：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β), R.inv
 = Prod.swap ⁻¹' R
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.image_swap_prod`：image_swap_prod (s : Set α) (t : Set β) : Prod.swap
 '' s ×ˢ t = t ×ˢ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prod_subset_comm [R.IsSymm] : s₁ ×ˢ s₂ ⊆ R ↔ s₂ ×ˢ s₁ ⊆ R := by
  rw [← R.inv_eq_self, SetRel.inv, ← Set.image_subset_iff, Set.image_swap_prod, ← SetRel.inv,
    R.inv_eq_self]
/-
**SetRel.preimage_eq_image** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：preimage_eq_image [R.IsSymm] : R.preimage s = R.image s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetRel.preimage_inv`：∀ {α : Type u_1} {β : Type u_2} (R : SetRel α β) (s
 : Set α), R.inv.preimage s = R.image s
· 使用定理 `SetRel.inv_eq_self`：∀ {α : Type u_1} (R : SetRel α α) [R.IsSymm], R.inv 
= R
-/
lemma preimage_eq_image [R.IsSymm] : R.preimage s = R.image s := by
  rw [← preimage_inv, inv_eq_self]

variable (R) in
/-- The maximal symmetric relation contained in a given relation. -/
/-
**SetRel.symmetrize** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：symmetrize : SetRel α α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal symmetric relation contained in a given relation.
-/
def symmetrize : SetRel α α := R ∩ R.inv
/-
**SetRel.isSymm_symmetrize** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isSymm_symmetrize : R.symmetrize.IsSymm where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
instance isSymm_symmetrize : R.symmetrize.IsSymm where symm _ _ := .symm
/-
**SetRel.symmetrize_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：symmetrize_subset_self : R.symmetrize subseteq R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma symmetrize_subset_self : R.symmetrize ⊆ R := Set.inter_subset_left
/-
**SetRel.symmetrize_subset_inv** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：symmetrize_subset_inv : R.symmetrize subseteq R.inv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma symmetrize_subset_inv : R.symmetrize ⊆ R.inv := Set.inter_subset_right
/-
**SetRel.subset_symmetrize** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：subset_symmetrize {S : SetRel α α} : S subseteq R.symmetrize ↔ S subseteq 
R ∧ S subseteq R.inv
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
-/
lemma subset_symmetrize {S : SetRel α α} : S ⊆ R.symmetrize ↔ S ⊆ R ∧ S ⊆ R.inv :=
  Set.subset_inter_iff

@[gcongr]
/-
**SetRel.symmetrize_mono** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：symmetrize_mono (h : R₁ subseteq R₂) : R₁.symmetrize subseteq R₂.symmetriz
e
参数：h : R₁ subseteq R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
lemma symmetrize_mono (h : R₁ ⊆ R₂) : R₁.symmetrize ⊆ R₂.symmetrize :=
  Set.inter_subset_inter h <| Set.preimage_mono h

/-! ### Transitive relations -/

variable (R) in
/-- A relation `R` is transitive if `a ~[R] b` and `b ~[R] c` together imply `a ~[R] c`. -/
/-
**SetRel.IsTrans** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `R` is transitive if `a ~[R] b` and `b ~[R] c` together imply `a ~[R]
 c`.
-/
protected abbrev IsTrans : Prop := IsTrans α (· ~[R] ·)

variable (R) in
/-
**SetRel.trans** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans], (a, b) ∈ R → (b
, c) ∈ R → (a, c) ∈ R
参数：R : SetRel α α；a, b；b, c；a, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
-/
protected lemma trans [R.IsTrans] (hab : a ~[R] b) (hbc : b ~[R] c) : a ~[R] c :=
  trans_of (· ~[R] ·) hab hbc
/-
**SetRel.** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : α → α → Prop} [IsTrans α R] : SetRel.IsTrans {(a, b) | R a b} := ‹_›
/-
**SetRel.comp_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_subset_self [R.IsTrans] : R ○ R subseteq R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
-/
lemma comp_subset_self [R.IsTrans] : R ○ R ⊆ R := fun ⟨_, _⟩ ⟨_, hab, hbc⟩ ↦ R.trans hab hbc
/-
**SetRel.comp_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：comp_eq_self [R.IsRefl] [R.IsTrans] : R ○ R = R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `SetRel.comp_subset_self`：comp_subset_self [R.IsTrans] : R ○ R subseteq R
· 使用引理 `SetRel.left_subset_comp`：left_subset_comp {R : SetRel α β} [S.IsRefl] : 
R subseteq R ○ S
-/
lemma comp_eq_self [R.IsRefl] [R.IsTrans] : R ○ R = R :=
  subset_antisymm comp_subset_self left_subset_comp
/-
**SetRel.isTrans_iff_comp_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：isTrans_iff_comp_subset_self : R.IsTrans ↔ R ○ R subseteq R where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SetRel.comp_subset_self`：comp_subset_self [R.IsTrans] : R ○ R subseteq R
-/
lemma isTrans_iff_comp_subset_self : R.IsTrans ↔ R ○ R ⊆ R where
  mp _ := comp_subset_self
  mpr h := ⟨fun _ _ _ hx hy ↦ h ⟨_, hx, hy⟩⟩
/-
**SetRel.isTrans_empty** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_empty : (∅ : SetRel α α).IsTrans where trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isTrans_empty : (∅ : SetRel α α).IsTrans where trans _ _ _ := by simp
/-
**SetRel.isTrans_univ** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_univ : SetRel.IsTrans (Set.univ : SetRel α α) where trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance isTrans_univ : SetRel.IsTrans (Set.univ : SetRel α α) where trans _ _ _ := by simp
/-
**SetRel.isTrans_singleton** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_singleton (x : α × α) : SetRel.IsTrans {x} where trans _ _ _
参数：x : α × α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isTrans_singleton (x : α × α) : SetRel.IsTrans {x} where trans _ _ _ := by aesop
/-
**SetRel.isTrans_inter** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_inter [R₁.IsTrans] [R₂.IsTrans] : (R₁ inter R₂).IsTrans where tran
s _a _b _c hab hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance isTrans_inter [R₁.IsTrans] [R₂.IsTrans] : (R₁ ∩ R₂).IsTrans where
  trans _a _b _c hab hbc := ⟨R₁.trans hab.1 hbc.1, R₂.trans hab.2 hbc.2⟩
/-
**SetRel.IsTrans.sInter** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsTrans`。
形式化陈述：∀ {α : Type u_1} {ℛ : Set (SetRel α α)}, (∀ R ∈ ℛ, R.IsTrans) → SetRel.IsT
rans (⋂₀ ℛ)
参数：SetRel α α；∀ R ∈ ℛ, R.IsTrans；⋂₀ ℛ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
protected lemma IsTrans.sInter {ℛ : Set <| SetRel α α} (hℛ : ∀ R ∈ ℛ, R.IsTrans) :
    SetRel.IsTrans (⋂₀ ℛ) where
  trans _a _b _c hab hbc R hR := (hℛ R hR).trans _ _ _ (hab R hR) <| hbc R hR
/-
**SetRel.isTrans_iInter** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_iInter {R : ι -> SetRel α α} [forall i, (R i).IsTrans] : SetRel.Is
Trans (⋂ i, R i)
参数：R i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsTrans.sInter`：∀ {α : Type u_1} {ℛ : Set (SetRel α α)}, (∀ R ∈ ℛ
, R.IsTrans) → SetRel.IsTrans (⋂₀ ℛ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance isTrans_iInter {R : ι → SetRel α α} [∀ i, (R i).IsTrans] :
    SetRel.IsTrans (⋂ i, R i) := .sInter <| by simpa
/-
**SetRel.isTrans_id** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_id : (.id : SetRel α α).IsTrans where trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
instance isTrans_id : (.id : SetRel α α).IsTrans where trans _ _ _ := .trans
/-
**SetRel.isTrans_preimage** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_preimage {f : β -> α} [R.IsTrans] : SetRel.IsTrans (Prod.map f f ⁻
¹' R) where trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
-/
instance isTrans_preimage {f : β → α} [R.IsTrans] : SetRel.IsTrans (Prod.map f f ⁻¹' R) where
  trans _ _ _ := R.trans
/-
**SetRel.isTrans_symmetrize** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
形式化陈述：isTrans_symmetrize [R.IsTrans] : R.symmetrize.IsTrans where trans _a _b _c
 hab hbc
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance isTrans_symmetrize [R.IsTrans] : R.symmetrize.IsTrans where
  trans _a _b _c hab hbc := ⟨R.trans hab.1 hbc.1, R.trans hbc.2 hab.2⟩

variable (R) in
/-- A relation `R` is irreflexive if `¬ a ~[R] a`. -/
/-
**SetRel.IsIrrefl** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：{α : Type u_1} → SetRel α α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `R` is irreflexive if `¬ a ~[R] a`.
-/
protected abbrev IsIrrefl : Prop := Std.Irrefl (· ~[R] ·)

variable (R a) in
/-
**SetRel.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {α : Type u_1} (R : SetRel α α) (a : α) [R.IsIrrefl], (a, a) ∉ R
参数：R : SetRel α α；a : α；a, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
-/
protected lemma irrefl [R.IsIrrefl] : ¬ a ~[R] a := irrefl_of (· ~[R] ·) _
/-
**SetRel.** 是 Mathlib 中的一个实例，位于命名空间 `SetRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : α → α → Prop} [Std.Irrefl R] : SetRel.IsIrrefl {(a, b) | R a b} := ‹_›

variable (R) in
/-- A relation `R` on a type `α` is well-founded if all elements of `α` are accessible within `R`.
-/
/-
**SetRel.IsWellFounded** 是 Mathlib 中的一个缩写定义，位于命名空间 `SetRel`。
形式化陈述：IsWellFounded : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `R` on a type `α` is well-founded if all elements of `α` are accessib
le within `R`.
-/
abbrev IsWellFounded : Prop := WellFounded (· ~[R] ·)

variable (R S) in
/-- A relation homomorphism with respect to a given pair of relations `R` and `S` s is a function
`f : α → β` such that `a ~[R] b → f a ~[s] f b`. -/
/-
**SetRel.Hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SetRel`。
形式化陈述：Hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation homomorphism with respect to a given pair of relations `R` and `S` s 
is a function
`f : α → β` such that `a ~[R] b → f a ~[s] f b`.
-/
abbrev Hom := (· ~[R] ·) →r (· ~[S] ·)

end SetRel

open Set
open scoped SetRel

namespace Function
variable {f : α → β} {a : α} {b : β}

/-- The graph of a function as a relation. -/
/-
**Function.graph** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：graph (f : α -> β) : SetRel α β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph of a function as a relation.
-/
def graph (f : α → β) : SetRel α β := {(a, b) | f a = b}
/-
**Function.mem_graph** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α} {b : β}, (a, b) ∈ Func
tion.graph f ↔ f a = b
参数：a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_graph : a ~[f.graph] b ↔ f a = b := .rfl
/-
**Function.graph_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：graph_injective : Injective (graph : (α -> β) -> SetRel α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem graph_injective : Injective (graph : (α → β) → SetRel α β) := by
  aesop (add simp [Injective, Set.ext_iff])
/-
**Function.graph_inj** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β}, Function.graph f = Function
.graph g ↔ f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.graph_injective`：graph_injective : Injective (graph : (α -> β) 
-> SetRel α β)
-/
@[simp] lemma graph_inj {f g : α → β} : f.graph = g.graph ↔ f = g := graph_injective.eq_iff
/-
**Function.graph_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1}, Function.graph id = SetRel.id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma graph_id : graph (id : α → α) = .id := by aesop
/-
**Function.graph_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：graph_comp (f : β -> γ) (g : α -> β) : graph (f ∘ g) = graph g ○ graph f
参数：f : β -> γ；g : α -> β。
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
theorem graph_comp (f : β → γ) (g : α → β) : graph (f ∘ g) = graph g ○ graph f := by aesop

/-- The higher-arity graph of a function. Describes α-argument functions from β to β. -/
/-
**Function.tupleGraph** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：tupleGraph (f : (α -> β) -> β) : Set (Option α -> β)
参数：f : (α -> β) -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The higher-arity graph of a function. Describes α-argument functions from β to β
.
-/
def tupleGraph (f : (α → β) → β) : Set (Option α → β) :=
  { v | f (v ∘ some) = v none }

end Function

/-
**Equiv.graph_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.graph_inv (f : α ≃ β) : (f.symm : β -> α).graph = SetRel.inv (f : α 
-> β).graph
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem Equiv.graph_inv (f : α ≃ β) : (f.symm : β → α).graph = SetRel.inv (f : α → β).graph := by
  aesop
/-
**SetRel.exists_graph_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SetRel.exists_graph_eq_iff (R : SetRel α β) : (exists! f, Function.graph f
 = R) ↔ forall a, exists! b, a ~[R] b
参数：R : SetRel α β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma SetRel.exists_graph_eq_iff (R : SetRel α β) :
    (∃! f, Function.graph f = R) ↔ ∀ a, ∃! b, a ~[R] b := by
  constructor
  · rintro ⟨f, rfl, _⟩ x
    simp
  intro h
  choose f hf using fun x ↦ (h x).exists
  refine ⟨f, ?_, by aesop⟩
  ext ⟨a, b⟩
  constructor
  · aesop
  · exact (h _).unique (hf _)

namespace Set

/-
**Set.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq (f : α -> β) (s : Set α) : f '' s = (Function.graph f).image s
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.graph f).image s := by
  rfl
/-
**Set.preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq (f : α -> β) (s : Set β) : f ⁻¹' s = (Function.graph f).preima
ge s
参数：f : α -> β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).preimage s := by
  simp [Set.preimage, SetRel.preimage]
/-
**Set.preimage_eq_core** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_core (f : α -> β) (s : Set β) : f ⁻¹' s = (Function.graph f).c
ore s
参数：f : α -> β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).core s := by
  simp [Set.preimage, SetRel.core]

end Set

/-- A shorthand for `α → β → Prop`.

Consider using `SetRel` instead if you want extra API for relations. -/
/-
**Rel** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Rel (α β : Type*) : Type _
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `α → β → Prop`.

Consider using `SetRel` instead if you want extra API for relations.
-/
abbrev Rel (α β : Type*) : Type _ := α → β → Prop
