/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Equiv.Defs

/-!
# Partial values of a type

This file defines `Part α`, the partial values of a type.
`o : Part α` carries a proposition `o.Dom`, its domain, along with a function `get : o.Dom → α`, its
value. The rule is then that every partial value has a value but, to access it, you need to provide
a proof of the domain.
`Part α` behaves the same as `Option α` except that `o : Option α` is decidably `none` or `some a`
for some `a : α`, while the domain of `o : Part α` doesn't have to be decidable. That means you can
translate back and forth between a partial value with a decidable domain and an option, and
`Option α` and `Part α` are classically equivalent. In general, `Part α` is bigger than `Option α`.

## Main declarations
`Option`-like declarations:
* `Part.none`: The partial value whose domain is `False`.
* `Part.some a`: The partial value whose domain is `True` and whose value is `a`.
* `Part.ofOption`: Converts an `Option α` to a `Part α` by sending `none` to `none` and `some a` to
  `some a`.
* `Part.toOption`: Converts a `Part α` with a decidable domain to an `Option α`.
* `Part.equivOption`: Classical equivalence between `Part α` and `Option α`.

Monadic structure:
* `Part.bind`: `o.bind f` has value `(f (o.get _)).get _` (`f o` morally) and is defined when `o`
  and `f (o.get _)` are defined.
* `Part.map`: Maps the value and keeps the same domain.

Other:
* `Part.restrict`: `Part.restrict p o` replaces the domain of `o : Part α` by `p : Prop` so long as
  `p → o.Dom`.
* `Part.assert`: `assert p f` appends `p` to the domains of the values of a partial function.
* `Part.unwrap`: Gets the value of a partial value regardless of its domain. Unsound.

## Notation
For `a : α`, `o : Part α`, `a ∈ o` means that `o` is defined and equal to `a`. Formally, it means
`o.Dom` and `o.get _ = a`.
-/

@[expose] public section

assert_not_exists RelIso

open Function

/-- `Part α` is the type of "partial values" of type `α`. It
  is similar to `Option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
/-
**Part.** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part α` is the type of "partial values" of type `α`. It
  is similar to `Option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable.
-/
structure Part.{u} (α : Type u) : Type u where
  /-- The domain of a partial value -/
  Dom : Prop
  /-- Extract a value from a partial value given a proof of `Dom` -/
  get : Dom → α

namespace Part

variable {α : Type*} {β : Type*} {γ : Type*}

/-- Convert a `Part α` with a decidable domain to an option -/
/-
**Part.toOption** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：toOption (o : Part α) [Decidable o.Dom] : Option α
参数：o : Part α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `Part α` with a decidable domain to an option
-/
def toOption (o : Part α) [Decidable o.Dom] : Option α :=
  if h : Dom o then some (o.get h) else none
/-
**Part.toOption_isSome** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} (o : Part α) [inst : Decidable o.Dom], o.toOption.isSome 
= true ↔ o.Dom
参数：o : Part α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Bool.false_eq_true`：(false = true) = False
-/
@[simp] lemma toOption_isSome (o : Part α) [Decidable o.Dom] : o.toOption.isSome ↔ o.Dom := by
  by_cases h : o.Dom <;> simp [h, toOption]
/-
**Part.toOption_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} (o : Part α) [inst : Decidable o.Dom], o.toOption = none 
↔ ¬o.Dom
参数：o : Part α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma toOption_eq_none (o : Part α) [Decidable o.Dom] : o.toOption = none ↔ ¬o.Dom := by
  by_cases h : o.Dom <;> simp [h, toOption]

/-- `Part` extensionality -/
/-
**Part.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h₂, o.get h₁ =
 p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od = pd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`Part` extensionality
-/
theorem ext' : ∀ {o p : Part α}, (o.Dom ↔ p.Dom) → (∀ h₁ h₂, o.get h₁ = p.get h₂) → o = p
  | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by
    have t : od = pd := propext H1
    cases t; rw [show o = p from funext fun p => H2 p p]

/-- `Part` eta expansion -/
@[simp]
/-
**Part.eta** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eta : forall o : Part α, (⟨o.Dom, fun h => o.get h⟩ : Part α) = o | ⟨_, _⟩
 => rfl  /-- `a ∈ o` means that `o` is defined and equal to `a` -/ protected def
 Mem (o : Part α) (a : α) : Prop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part` eta expansion
-/
theorem eta : ∀ o : Part α, (⟨o.Dom, fun h => o.get h⟩ : Part α) = o
  | ⟨_, _⟩ => rfl

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
/-
**Part.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：{α : Type u_1} → Part α → α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a ∈ o` means that `o` is defined and equal to `a`
-/
protected def Mem (o : Part α) (a : α) : Prop :=
  ∃ h, o.get h = a
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Part α) :=
  ⟨Part.Mem⟩
/-
**Part.mem_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_eq (a : α) (o : Part α) : (a in o) = exists h, o.get h = a
参数：a : α；o : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_eq (a : α) (o : Part α) : (a ∈ o) = ∃ h, o.get h = a :=
  rfl
/-
**Part.dom_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dom_iff_mem : ∀ {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
  | ⟨_, f⟩ => ⟨fun h => ⟨f h, h, rfl⟩, fun ⟨_, h, rfl⟩ => h⟩
/-
**Part.get_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：get_mem {o : Part α} (h) : get o h in o
参数：h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_mem {o : Part α} (h) : get o h ∈ o :=
  ⟨_, rfl⟩

@[simp]
/-
**Part.mem_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_mk_iff {p : Prop} {o : p -> α} {a : α} : a in Part.mk p o ↔ exists h, 
o h = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff {p : Prop} {o : p → α} {a : α} : a ∈ Part.mk p o ↔ ∃ h, o h = a :=
  Iff.rfl

/-- `Part` extensionality -/
@[ext]
/-
**Part.ext** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
参数：H : forall a, a in o ↔ a in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext'`：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h
₂, o.get h₁ = p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od =…
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯

--- 原说明 ---
`Part` extensionality
-/
theorem ext {o p : Part α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
  (ext' ⟨fun h => ((H _).1 ⟨h, rfl⟩).fst, fun h => ((H _).2 ⟨h, rfl⟩).fst⟩) fun _ _ =>
    ((H _).2 ⟨_, rfl⟩).snd

/-- The `none` value in `Part` has a `False` domain and an empty function. -/
/-
**Part.none** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：none : Part α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `none` value in `Part` has a `False` domain and an empty function.
-/
def none : Part α :=
  ⟨False, False.rec⟩
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Part α) :=
  ⟨none⟩

@[simp]
/-
**Part.notMem_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：notMem_none (a : α) : a ∉ @none α
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem notMem_none (a : α) : a ∉ @none α := fun h => h.fst

/-- The `some a` value in `Part` has a `True` domain and the
  function returns `a`. -/
/-
**Part.some** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：some (a : α) : Part α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `some a` value in `Part` has a `True` domain and the
  function returns `a`.
-/
def some (a : α) : Part α :=
  ⟨True, fun _ => a⟩

@[simp]
/-
**Part.some_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_dom (a : α) : (some a).Dom
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem some_dom (a : α) : (some a).Dom :=
  trivial
/-
**Part.mem_unique** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o → a = b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_unique : ∀ {a b : α} {o : Part α}, a ∈ o → b ∈ o → a = b
  | _, _, ⟨_, _⟩, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl
/-
**Part.mem_right_unique** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {a : α} {o p : Part α}, a ∈ o → a ∈ p → o = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext'`：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h
₂, o.get h₁ = p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od =…
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_right_unique : ∀ {a : α} {o p : Part α}, a ∈ o → a ∈ p → o = p
  | _, _, _, ⟨ho, _⟩, ⟨hp, _⟩ => ext' (iff_of_true ho hp) (by simp [*])
/-
**Part.Mem.left_unique** 是 Mathlib 中的一个定理，位于命名空间 `Part.Mem`。
形式化陈述：∀ {α : Type u_1}, Relator.LeftUnique fun x1 x2 => x1 ∈ x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Part α → Prop) := fun _ _ _ =>
  mem_unique
/-
**Part.Mem.right_unique** 是 Mathlib 中的一个定理，位于命名空间 `Part.Mem`。
形式化陈述：∀ {α : Type u_1}, Relator.RightUnique fun x1 x2 => x1 ∈ x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_right_unique`：∀ {α : Type u_1} {a : α} {o p : Part α}, a ∈ o → 
a ∈ p → o = p
-/
theorem Mem.right_unique : Relator.RightUnique ((· ∈ ·) : α → Part α → Prop) := fun _ _ _ =>
  mem_right_unique
/-
**Part.get_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：get_eq_of_mem {o : Part α} {a} (h : a in o) (h') : get o h' = a
参数：h : a in o；h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
theorem get_eq_of_mem {o : Part α} {a} (h : a ∈ o) (h') : get o h' = a :=
  mem_unique ⟨_, rfl⟩ h
/-
**Part.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} (o : Part α), {a | a ∈ o}.Subsingleton
参数：o : Part α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
protected theorem subsingleton (o : Part α) : Set.Subsingleton { a | a ∈ o } := fun _ ha _ hb =>
  mem_unique ha hb

@[simp]
/-
**Part.get_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：get_some {a : α} (ha : (some a).Dom) : get (some a) ha = a
参数：ha : (some a).Dom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_some {a : α} (ha : (some a).Dom) : get (some a) ha = a :=
  rfl
/-
**Part.mem_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_some (a : α) : a in some a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_some (a : α) : a ∈ some a :=
  ⟨trivial, rfl⟩

@[simp]
/-
**Part.mem_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_some_iff {a b} : b in (some a : Part α) ↔ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trivial`：True
-/
theorem mem_some_iff {a b} : b ∈ (some a : Part α) ↔ b = a :=
  ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨trivial, e.symm⟩⟩
/-
**Part.eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_some`：mem_some (a : α) : a in some a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.ext'`：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h
₂, o.get h₁ = p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od =…
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
-/
theorem eq_some_iff {a : α} {o : Part α} : o = some a ↔ a ∈ o :=
  ⟨fun e => e.symm ▸ mem_some _, fun ⟨h, e⟩ => e ▸ ext' (iff_true_intro h) fun _ _ => rfl⟩
/-
**Part.eq_none_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.notMem_none`：notMem_none (a : α) : a ∉ @none α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
-/
theorem eq_none_iff {o : Part α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e => e.symm ▸ notMem_none, fun h => ext (by simpa)⟩
/-
**Part.eq_none_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_none_iff' {o : Part α} : o = none ↔ ¬o.Dom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_none_iff`：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem eq_none_iff' {o : Part α} : o = none ↔ ¬o.Dom :=
  ⟨fun e => e.symm ▸ id, fun h => eq_none_iff.2 fun _ h' => h h'.fst⟩

@[simp]
/-
**Part.not_none_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：not_none_dom : ¬(none : Part α).Dom
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_none_dom : ¬(none : Part α).Dom :=
  id

@[simp]
/-
**Part.some_ne_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_ne_none (x : α) : some x != none
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `true_ne_false`：¬True = False
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem some_ne_none (x : α) : some x ≠ none := by
  intro h
  exact true_ne_false (congr_arg Dom h)

@[simp]
/-
**Part.none_ne_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：none_ne_some (x : α) : none != some x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Part.some_ne_none`：some_ne_none (x : α) : some x != none
-/
theorem none_ne_some (x : α) : none ≠ some x :=
  (some_ne_none x).symm
/-
**Part.ne_none_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：ne_none_iff {o : Part α} : o != none ↔ exists x, o = some x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Part.eq_none_iff'`：eq_none_iff' {o : Part α} : o = none ↔ ¬o.Dom
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
· 使用定理 `Part.get_mem`：get_mem {o : Part α} (h) : get o h in o
· 使用定理 `Part.some_ne_none`：some_ne_none (x : α) : some x != none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_none_iff {o : Part α} : o ≠ none ↔ ∃ x, o = some x := by
  constructor
  · rw [Ne, eq_none_iff', not_not]
    exact fun h => ⟨o.get h, eq_some_iff.2 (get_mem h)⟩
  · rintro ⟨x, rfl⟩
    apply some_ne_none
/-
**Part.eq_none_or_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_none_or_eq_some (o : Part α) : o = none ∨ exists x, o = some x
参数：o : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.ne_none_iff`：ne_none_iff {o : Part α} : o != none ↔ exists x, o = s
ome x
-/
theorem eq_none_or_eq_some (o : Part α) : o = none ∨ ∃ x, o = some x :=
  or_iff_not_imp_left.2 ne_none_iff.1
/-
**Part.some_injective** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_injective : Injective (@Part.some α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Part.mk.inj`：∀ {α : Type u} {Dom : Prop} {get : Dom → α} {Dom_1 : Prop} 
{get_1 : Dom_1 → α},   { Dom := Dom, get := get } = { Dom := Dom_1, get := get_1
 …
· 使用定理 `trivial`：True
-/
theorem some_injective : Injective (@Part.some α) := fun _ _ h =>
  congr_fun (eq_of_heq (Part.mk.inj h).2) trivial

@[simp]
/-
**Part.some_inj** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_inj {a b : α} : Part.some a = some b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Part.some_injective`：some_injective : Injective (@Part.some α)
-/
theorem some_inj {a b : α} : Part.some a = some b ↔ a = b :=
  some_injective.eq_iff

@[simp]
/-
**Part.some_get** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_get {a : Part α} (ha : a.Dom) : Part.some (Part.get a ha) = a
参数：ha : a.Dom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
-/
theorem some_get {a : Part α} (ha : a.Dom) : Part.some (Part.get a ha) = a :=
  Eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)
/-
**Part.get_eq_iff_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：get_eq_iff_eq_some {a : Part α} {ha : a.Dom} {b : α} : a.get ha = b ↔ a = 
some b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.some_get`：some_get {a : Part α} (ha : a.Dom) : Part.some (Part.get 
a ha) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Part.get.congr_simp`：∀ {α : Type u} (self self_1 : Part α) (e_self : sel
f = self_1) (a : self.Dom), self.get a = self_1.get ⋯
-/
theorem get_eq_iff_eq_some {a : Part α} {ha : a.Dom} {b : α} : a.get ha = b ↔ a = some b :=
  ⟨fun h => by simp [h.symm], fun h => by simp [h]⟩
/-
**Part.get_eq_get_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：get_eq_get_of_eq (a : Part α) (ha : a.Dom) {b : Part α} (h : a = b) : a.ge
t ha = b.get (h ▸ ha)
参数：a : Part α；ha : a.Dom；h : a = b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_eq_get_of_eq (a : Part α) (ha : a.Dom) {b : Part α} (h : a = b) :
    a.get ha = b.get (h ▸ ha) := by
  congr
/-
**Part.get_eq_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：get_eq_iff_mem {o : Part α} {a : α} (h : o.Dom) : o.get h = a ↔ a in o
参数：h : o.Dom。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_eq_iff_mem {o : Part α} {a : α} (h : o.Dom) : o.get h = a ↔ a ∈ o :=
  ⟨fun H => ⟨h, H⟩, fun ⟨_, H⟩ => H⟩
/-
**Part.eq_get_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_get_iff_mem {o : Part α} {a : α} (h : o.Dom) : a = o.get h ↔ a in o
参数：h : o.Dom。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Part.get_eq_iff_mem`：get_eq_iff_mem {o : Part α} {a : α} (h : o.Dom) : o
.get h = a ↔ a in o
-/
theorem eq_get_iff_mem {o : Part α} {a : α} (h : o.Dom) : a = o.get h ↔ a ∈ o :=
  eq_comm.trans (get_eq_iff_mem h)
/-
**Part.eq_of_get_eq_get** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_of_get_eq_get {a b : Part α} (ha : a.Dom) (hb : b.Dom) (hab : a.get ha 
= b.get hb) : a = b
参数：ha : a.Dom；hb : b.Dom；hab : a.get ha = b.get hb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext'`：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h
₂, o.get h₁ = p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od =…
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
-/
theorem eq_of_get_eq_get {a b : Part α} (ha : a.Dom) (hb : b.Dom) (hab : a.get ha = b.get hb) :
    a = b :=
  ext' (iff_of_true ha hb) fun _ _ => hab
/-
**Part.eq_iff_of_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_iff_of_dom {a b : Part α} (ha : a.Dom) (hb : b.Dom) : a.get ha = b.get 
hb ↔ a = b
参数：ha : a.Dom；hb : b.Dom。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.eq_of_get_eq_get`：eq_of_get_eq_get {a b : Part α} (ha : a.Dom) (hb 
: b.Dom) (hab : a.get ha = b.get hb) : a = b
· 使用定理 `Part.get_eq_get_of_eq`：get_eq_get_of_eq (a : Part α) (ha : a.Dom) {b : P
art α} (h : a = b) : a.get ha = b.get (h ▸ ha)
-/
theorem eq_iff_of_dom {a b : Part α} (ha : a.Dom) (hb : b.Dom) : a.get ha = b.get hb ↔ a = b :=
  ⟨eq_of_get_eq_get ha hb, get_eq_get_of_eq a ha⟩
/-
**Part.eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_of_mem {a b : Part α} (ha : a.Dom) (hb : a.get ha in b) : a = b
参数：ha : a.Dom；hb : a.get ha in b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.dom_iff_mem`：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.eq_iff_of_dom`：eq_iff_of_dom {a b : Part α} (ha : a.Dom) (hb : b.Do
m) : a.get ha = b.get hb ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.eq_get_iff_mem`：eq_get_iff_mem {o : Part α} {a : α} (h : o.Dom) : a
 = o.get h ↔ a in o
-/
theorem eq_of_mem {a b : Part α} (ha : a.Dom) (hb : a.get ha ∈ b) : a = b := by
  have hb' : b.Dom := Part.dom_iff_mem.mpr ⟨a.get ha, hb⟩
  rwa [← eq_get_iff_mem hb', eq_iff_of_dom ha hb'] at hb

@[simp]
/-
**Part.none_toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：none_toOption [Decidable (@none α).Dom] : (none : Part α).toOption = Optio
n.none
参数：@none α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem none_toOption [Decidable (@none α).Dom] : (none : Part α).toOption = Option.none :=
  dif_neg id

@[simp]
/-
**Part.some_toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_toOption (a : α) [Decidable (some a).Dom] : (some a).toOption = Optio
n.some a
参数：a : α；some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `trivial`：True
-/
theorem some_toOption (a : α) [Decidable (some a).Dom] : (some a).toOption = Option.some a :=
  dif_pos trivial
/-
**Part.noneDecidable** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
形式化陈述：noneDecidable : Decidable (@none α).Dom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance noneDecidable : Decidable (@none α).Dom :=
  instDecidableFalse
/-
**Part.someDecidable** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
形式化陈述：someDecidable (a : α) : Decidable (some a).Dom
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance someDecidable (a : α) : Decidable (some a).Dom :=
  instDecidableTrue

/-- Retrieves the value of `a : Part α` if it exists, and return the provided default value
otherwise. -/
/-
**Part.getOrElse** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：getOrElse (a : Part α) [Decidable a.Dom] (d : α)
参数：a : Part α；d : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Retrieves the value of `a : Part α` if it exists, and return the provided defaul
t value
otherwise.
-/
def getOrElse (a : Part α) [Decidable a.Dom] (d : α) :=
  if ha : a.Dom then a.get ha else d
/-
**Part.getOrElse_of_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：getOrElse_of_dom (a : Part α) (h : a.Dom) [Decidable a.Dom] (d : α) : getO
rElse a d = a.get h
参数：a : Part α；h : a.Dom；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem getOrElse_of_dom (a : Part α) (h : a.Dom) [Decidable a.Dom] (d : α) :
    getOrElse a d = a.get h :=
  dif_pos h
/-
**Part.getOrElse_of_not_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：getOrElse_of_not_dom (a : Part α) (h : ¬a.Dom) [Decidable a.Dom] (d : α) :
 getOrElse a d = d
参数：a : Part α；h : ¬a.Dom；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem getOrElse_of_not_dom (a : Part α) (h : ¬a.Dom) [Decidable a.Dom] (d : α) :
    getOrElse a d = d :=
  dif_neg h

@[simp]
/-
**Part.getOrElse_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：getOrElse_none (d : α) [Decidable (none : Part α).Dom] : getOrElse none d 
= d
参数：d : α；none : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.getOrElse_of_not_dom`：getOrElse_of_not_dom (a : Part α) (h : ¬a.Dom
) [Decidable a.Dom] (d : α) : getOrElse a d = d
· 使用定理 `Part.not_none_dom`：not_none_dom : ¬(none : Part α).Dom
-/
theorem getOrElse_none (d : α) [Decidable (none : Part α).Dom] : getOrElse none d = d :=
  none.getOrElse_of_not_dom not_none_dom d

@[simp]
/-
**Part.getOrElse_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：getOrElse_some (a : α) (d : α) [Decidable (some a).Dom] : getOrElse (some 
a) d = a
参数：a : α；d : α；some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.getOrElse_of_dom`：getOrElse_of_dom (a : Part α) (h : a.Dom) [Decida
ble a.Dom] (d : α) : getOrElse a d = a.get h
· 使用定理 `Part.some_dom`：some_dom (a : α) : (some a).Dom
-/
theorem getOrElse_some (a : α) (d : α) [Decidable (some a).Dom] : getOrElse (some a) d = a :=
  (some a).getOrElse_of_dom (some_dom a) d

-- `simp`-normal form is `toOption_eq_some_iff`.
/-
**Part.mem_toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_toOption {o : Part α} [Decidable o.Dom] {a : α} : a in toOption o ↔ a 
in o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem mem_toOption {o : Part α} [Decidable o.Dom] {a : α} : a ∈ toOption o ↔ a ∈ o := by
  unfold toOption
  by_cases h : o.Dom
  · simpa [h] using ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  · simp only [h, ↓reduceDIte, Option.mem_def, reduceCtorEq, false_iff]
    exact mt Exists.fst h

@[simp]
/-
**Part.toOption_eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：toOption_eq_some_iff {o : Part α} [Decidable o.Dom] {a : α} : toOption o =
 Option.some a ↔ a in o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
· 使用定理 `Part.mem_toOption`：mem_toOption {o : Part α} [Decidable o.Dom] {a : α} :
 a in toOption o ↔ a in o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toOption_eq_some_iff {o : Part α} [Decidable o.Dom] {a : α} :
    toOption o = Option.some a ↔ a ∈ o := by
  rw [← Option.mem_def, mem_toOption]
/-
**Part.Dom.toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part.Dom`。
形式化陈述：∀ {α : Type u_1} {o : Part α} [inst : Decidable o.Dom] (h : o.Dom), o.toOp
tion = some (o.get h)
参数：h : o.Dom；o.get h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
protected theorem Dom.toOption {o : Part α} [Decidable o.Dom] (h : o.Dom) : o.toOption = o.get h :=
  dif_pos h
/-
**Part.toOption_eq_none_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：toOption_eq_none_iff {a : Part α} [Decidable a.Dom] : a.toOption = Option.
none ↔ ¬a.Dom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.dite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {
b : α} {A : P → α},   (∀ (h : P), A h ≠ b) → ((dite P A fun x => b) = b ↔ ¬P)
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
-/
theorem toOption_eq_none_iff {a : Part α} [Decidable a.Dom] : a.toOption = Option.none ↔ ¬a.Dom :=
  Ne.dite_eq_right_iff fun _ => Option.some_ne_none _

@[simp]
/-
**Part.elim_toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：elim_toOption {α β : Type*} (a : Part α) [Decidable a.Dom] (b : β) (f : α 
-> β) : a.toOption.elim b f = if h : a.Dom then f (a.get h) else b
参数：a : Part α；b : β；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Part.Dom.toOption`：∀ {α : Type u_1} {o : Part α} [inst : Decidable o.Dom
] (h : o.Dom), o.toOption = some (o.get h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.toOption_eq_none_iff`：toOption_eq_none_iff {a : Part α} [Decidable 
a.Dom] : a.toOption = Option.none ↔ ¬a.Dom
-/
theorem elim_toOption {α β : Type*} (a : Part α) [Decidable a.Dom] (b : β) (f : α → β) :
    a.toOption.elim b f = if h : a.Dom then f (a.get h) else b := by
  split_ifs with h
  · rw [h.toOption]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    rfl

/-- Converts an `Option α` into a `Part α`. -/
@[coe]
/-
**Part.ofOption** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：{α : Type u_1} → Option α → Part α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts an `Option α` into a `Part α`.
-/
def ofOption : Option α → Part α
  | Option.none => none
  | Option.some a => some a

@[simp]
/-
**Part.mem_ofOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {a : α} {o : Option α}, a ∈ ↑o ↔ a ∈ o
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
· 使用定理 `trivial`：True
· 使用定理 `Option.some.inj`：∀ {α : Type u} {val val_1 : α}, some val = some val_1 →
 val = val_1
-/
theorem mem_ofOption {a : α} : ∀ {o : Option α}, a ∈ ofOption o ↔ a ∈ o
  | Option.none => ⟨fun h => h.fst.elim, fun h => Option.noConfusion rfl (heq_of_eq h)⟩
  | Option.some _ => ⟨fun h => congr_arg Option.some h.snd, fun h => ⟨trivial, Option.some.inj h⟩⟩

@[simp]
/-
**Part.ofOption_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_4} (o : Option α), (↑o).Dom ↔ o.isSome = true
参数：o : Option α；↑o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofOption_dom {α} : ∀ o : Option α, (ofOption o).Dom ↔ o.isSome
  | Option.none => by simp [ofOption, none]
  | Option.some a => by simp [ofOption]
/-
**Part.ofOption_eq_get** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：ofOption_eq_get {α} (o : Option α) : ofOption o = ⟨_, @Option.get _ o⟩
参数：o : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext'`：ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h
₂, o.get h₁ = p.get h₂) -> o = p | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by have t : od =…
· 使用定理 `Part.ofOption_dom`：∀ {α : Type u_4} (o : Option α), (↑o).Dom ↔ o.isSome 
= true
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ofOption_eq_get {α} (o : Option α) : ofOption o = ⟨_, @Option.get _ o⟩ :=
  Part.ext' (ofOption_dom o) fun h₁ h₂ => by
    cases o
    · simp at h₂
    · rfl
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Option α) (Part α) :=
  ⟨ofOption⟩
/-
**Part.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_coe {a : α} {o : Option α} : a in (o : Part α) ↔ a in o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_ofOption`：∀ {α : Type u_1} {a : α} {o : Option α}, a ∈ ↑o ↔ a ∈
 o
-/
theorem mem_coe {a : α} {o : Option α} : a ∈ (o : Part α) ↔ a ∈ o :=
  mem_ofOption

@[simp]
/-
**Part.coe_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：coe_none : (@Option.none α : Part α) = none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_none : (@Option.none α : Part α) = none :=
  rfl

@[simp]
/-
**Part.coe_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：coe_some (a : α) : (Option.some a : Part α) = some a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_some (a : α) : (Option.some a : Part α) = some a :=
  rfl

@[elab_as_elim]
/-
**Part.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {P : Part α → Prop} (a : Part α), P Part.none → (∀ (a : α
), P (Part.some a)) → P a
参数：a : Part α；∀ (a : α), P (Part.some a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Part.some_get`：some_get {a : Part α} (ha : a.Dom) : Part.some (Part.get 
a ha) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_none_iff'`：eq_none_iff' {o : Part α} : o = none ↔ ¬o.Dom
-/
protected theorem induction_on {P : Part α → Prop} (a : Part α) (hnone : P none)
    (hsome : ∀ a : α, P (some a)) : P a :=
  (Classical.em a.Dom).elim (fun h => Part.some_get h ▸ hsome _) fun h =>
    (eq_none_iff'.2 h).symm ▸ hnone
/-
**Part.ofOptionDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：{α : Type u_1} → (o : Option α) → Decidable (↑o).Dom
参数：o : Option α；↑o。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ofOptionDecidable : ∀ o : Option α, Decidable (ofOption o).Dom
  | Option.none => Part.noneDecidable
  | Option.some a => Part.someDecidable a

@[simp]
/-
**Part.to_ofOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：to_ofOption (o : Option α) : toOption (ofOption o) = o
参数：o : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem to_ofOption (o : Option α) : toOption (ofOption o) = o := by cases o <;> rfl

@[simp]
/-
**Part.of_toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：of_toOption (o : Part α) [Decidable o.Dom] : ofOption (toOption o) = o
参数：o : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Part.mem_ofOption`：∀ {α : Type u_1} {a : α} {o : Option α}, a ∈ ↑o ↔ a ∈
 o
· 使用定理 `Part.mem_toOption`：mem_toOption {o : Part α} [Decidable o.Dom] {a : α} :
 a in toOption o ↔ a in o
-/
theorem of_toOption (o : Part α) [Decidable o.Dom] : ofOption (toOption o) = o :=
  ext fun _ => mem_ofOption.trans mem_toOption

/-- `Part α` is (classically) equivalent to `Option α`. -/
/-
**Part.equivOption** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：equivOption : Part α ≃ Option α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part α` is (classically) equivalent to `Option α`.
-/
noncomputable def equivOption : Part α ≃ Option α :=
  haveI := Classical.dec
  ⟨fun o => toOption o, ofOption, fun o => of_toOption o, fun o =>
    Eq.trans (by dsimp; congr) (to_ofOption o)⟩

/-- We give `Part α` the order where everything is greater than `none`. -/
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We give `Part α` the order where everything is greater than `none`.
-/
instance : PartialOrder (Part
        α) where
  le x y := ∀ i, i ∈ x → i ∈ y
  le_refl _ _ := id
  le_trans _ _ _ f g _ := g _ ∘ f _
  le_antisymm _ _ f g := Part.ext fun _ => ⟨f _, g _⟩
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Part α) where
  bot := none
  bot_le := by rintro x _ ⟨⟨_⟩, _⟩
/-
**Part.le_total_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：le_total_of_le_of_le {x y : Part α} (z : Part α) (hx : x <= z) (hy : y <= 
z) : x <= y ∨ y <= x
参数：z : Part α；hx : x <= z；hy : y <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.eq_none_or_eq_some`：eq_none_or_eq_some (o : Part α) : o = none ∨ ex
ists x, o = some x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderBot.bot_le`：∀ {α : Type u} {inst : LE α} [self : OrderBot α] (a : α
), ⊥ ≤ a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
theorem le_total_of_le_of_le {x y : Part α} (z : Part α) (hx : x ≤ z) (hy : y ≤ z) :
    x ≤ y ∨ y ≤ x := by
  rcases Part.eq_none_or_eq_some x with (h | ⟨b, h₀⟩)
  · rw [h]
    left
    apply OrderBot.bot_le _
  right; intro b' h₁
  rw [Part.eq_some_iff] at h₀
  have hx := hx _ h₀; have hy := hy _ h₁
  have hx := Part.mem_unique hx hy; subst hx
  exact h₀

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
/-
**Part.assert** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：assert (p : Prop) (f : p -> Part α) : Part α
参数：p : Prop；f : p -> Part α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value.
-/
def assert (p : Prop) (f : p → Part α) : Part α :=
  ⟨∃ h : p, (f h).Dom, fun ha => (f ha.fst).get ha.snd⟩

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
/-
**Part.bind** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Part α → (α → Part β) → Part β
参数：α → Part β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined.
-/
protected def bind (f : Part α) (g : α → Part β) : Part β :=
  assert (Dom f) fun b => g (f.get b)

/-- The map operation for `Part` just maps the value and maintains the same domain. -/
@[simps]
/-
**Part.map** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：map (f : α -> β) (o : Part α) : Part β
参数：f : α -> β；o : Part α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map operation for `Part` just maps the value and maintains the same domain.
-/
def map (f : α → β) (o : Part α) : Part β :=
  ⟨o.Dom, f ∘ o.get⟩
/-
**Part.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {o : Part α} {a : α}, a ∈ o → 
f a ∈ Part.map f o
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_map (f : α → β) {o : Part α} : ∀ {a}, a ∈ o → f a ∈ map f o
  | _, ⟨_, rfl⟩ => ⟨_, rfl⟩

@[simp]
/-
**Part.mem_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_map_iff (f : α -> β) {o : Part α} {b} : b in map f o ↔ exists a in o, 
f a = b
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {o : Part α} {
a : α}, a ∈ o → f a ∈ Part.map f o
-/
theorem mem_map_iff (f : α → β) {o : Part α} {b} : b ∈ map f o ↔ ∃ a ∈ o, f a = b :=
  ⟨fun hb => match b, hb with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩, rfl⟩,
    fun ⟨_, h₁, h₂⟩ => h₂ ▸ mem_map f h₁⟩

@[simp]
/-
**Part.map_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：map_none (f : α -> β) : map f none = none
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_none_iff`：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem map_none (f : α → β) : map f none = none :=
  eq_none_iff.2 fun a => by simp

@[simp]
/-
**Part.map_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：map_some (f : α -> β) (a : α) : map f (some a) = some (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
· 使用定理 `Part.mem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {o : Part α} {
a : α}, a ∈ o → f a ∈ Part.map f o
· 使用定理 `Part.mem_some`：mem_some (a : α) : a in some a
-/
theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) :=
  eq_some_iff.2 <| mem_map f <| mem_some _
/-
**Part.mem_assert** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {p : Prop} {f : p → Part α} {a : α} (h : p), a ∈ f h → a 
∈ Part.assert p f
参数：h : p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_assert {p : Prop} {f : p → Part α} : ∀ {a} (h : p), a ∈ f h → a ∈ assert p f
  | _, x, ⟨h, rfl⟩ => ⟨⟨x, h⟩, rfl⟩

@[simp, grind =]
/-
**Part.mem_assert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_assert_iff {p : Prop} {f : p -> Part α} {a} : a in assert p f ↔ exists
 h : p, a in f h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_assert`：∀ {α : Type u_1} {p : Prop} {f : p → Part α} {a : α} (h
 : p), a ∈ f h → a ∈ Part.assert p f
-/
theorem mem_assert_iff {p : Prop} {f : p → Part α} {a} : a ∈ assert p f ↔ ∃ h : p, a ∈ f h :=
  ⟨fun ha => match a, ha with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩⟩,
    fun ⟨_, h⟩ => mem_assert _ h⟩
/-
**Part.assert_pos** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：assert_pos {p : Prop} {f : p -> Part α} (h : p) : assert p f = f h
参数：h : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem assert_pos {p : Prop} {f : p → Part α} (h : p) : assert p f = f h := by
  ext
  simp_all
/-
**Part.assert_neg** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：assert_neg {p : Prop} {f : p -> Part α} (h : ¬p) : assert p f = none
参数：h : ¬p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem assert_neg {p : Prop} {f : p → Part α} (h : ¬p) : assert p f = none := by
  ext
  simp_all
/-
**Part.mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Part α} {g : α → Part β} {a : α} {b :
 β}, a ∈ f → b ∈ g a → b ∈ f.bind g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_bind {f : Part α} {g : α → Part β} : ∀ {a b}, a ∈ f → b ∈ g a → b ∈ f.bind g
  | _, _, ⟨h, rfl⟩, ⟨h₂, rfl⟩ => ⟨⟨h, h₂⟩, rfl⟩

@[simp, grind =]
/-
**Part.mem_bind_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_bind_iff {f : Part α} {g : α -> Part β} {b} : b in f.bind g ↔ exists a
 in f, b in g a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.mem_bind`：∀ {α : Type u_1} {β : Type u_2} {f : Part α} {g : α → Par
t β} {a : α} {b : β}, a ∈ f → b ∈ g a → b ∈ f.bind g
-/
theorem mem_bind_iff {f : Part α} {g : α → Part β} {b} : b ∈ f.bind g ↔ ∃ a ∈ f, b ∈ g a :=
  ⟨fun hb => match b, hb with
    | _, ⟨⟨_, _⟩, rfl⟩ => ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    fun ⟨_, h₁, h₂⟩ => mem_bind h₁ h₂⟩

/-- `Part.bind` produces `some b` iff the input is `some a` and the continuation maps `a` to
`some b`. This is the `Part` analogue of `Option.bind_eq_some_iff`. -/
/-
**Part.bind_eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_eq_some_iff {b : β} {x : Part α} {f : α -> Part β} : x.bind f = some 
b ↔ exists a, x = some a ∧ f a = some b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Part.bind` produces `some b` iff the input is `some a` and the continuation map
s `a` to
`some b`. This is the `Part` analogue of `Option.bind_eq_some_iff`.
-/
theorem bind_eq_some_iff {b : β} {x : Part α} {f : α → Part β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  simp only [eq_some_iff, mem_bind_iff]
/-
**Part.Dom.bind** 是 Mathlib 中的一个定理，位于命名空间 `Part.Dom`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {o : Part α} (h : o.Dom) (f : α → Part β),
 o.bind f = f (o.get h)
参数：h : o.Dom；f : α → Part β；o.get h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.get_eq_of_mem`：get_eq_of_mem {o : Part α} {a} (h : a in o) (h') : g
et o h' = a
· 使用定理 `Part.get_mem`：get_mem {o : Part α} (h) : get o h in o
-/
protected theorem Dom.bind {o : Part α} (h : o.Dom) (f : α → Part β) : o.bind f = f (o.get h) := by
  ext b
  simp only [Part.mem_bind_iff]
  refine ⟨?_, fun hb => ⟨o.get h, Part.get_mem _, hb⟩⟩
  rintro ⟨a, ha, hb⟩
  rwa [Part.get_eq_of_mem ha]
/-
**Part.Dom.of_bind** 是 Mathlib 中的一个定理，位于命名空间 `Part.Dom`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → Part β} {a : Part α}, (a.bind f).
Dom → a.Dom
参数：a.bind f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Dom.of_bind {f : α → Part β} {a : Part α} (h : (a.bind f).Dom) : a.Dom :=
  h.1

@[simp]
/-
**Part.bind_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_none (f : α -> Part β) : none.bind f = none
参数：f : α -> Part β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_none_iff`：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem bind_none (f : α → Part β) : none.bind f = none :=
  eq_none_iff.2 fun a => by simp

@[simp]
/-
**Part.bind_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_some (a : α) (f : α -> Part β) : (some a).bind f = f a
参数：a : α；f : α -> Part β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_some (a : α) (f : α → Part β) : (some a).bind f = f a :=
  ext <| by simp
/-
**Part.bind_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_of_mem {o : Part α} {a : α} (h : a in o) (f : α -> Part β) : o.bind f
 = f a
参数：h : a in o；f : α -> Part β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
-/
theorem bind_of_mem {o : Part α} {a : α} (h : a ∈ o) (f : α → Part β) : o.bind f = f a := by
  rw [eq_some_iff.2 h, bind_some]
/-
**Part.bind_some_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_some_eq_map (f : α -> β) (x : Part α) : x.bind (fun y => some (f y)) 
= map f x
参数：f : α -> β；x : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_some_eq_map (f : α → β) (x : Part α) : x.bind (fun y => some (f y)) = map f x :=
  ext <| by simp [eq_comm]
/-
**Part.bind_toOption** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_toOption (f : α -> Part β) (o : Part α) [Decidable o.Dom] [forall a, 
Decidable (f a).Dom] [Decidable (o.bind f).Dom] : (o.bind f).toOption = o.toOpti
on.elim Option.none fun a => (f a).toOption
参数：f : α -> Part β；o : Part α；f a；o.bind f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Part.Dom.toOption`：∀ {α : Type u_1} {o : Part α} [inst : Decidable o.Dom
] (h : o.Dom), o.toOption = some (o.get h)
· 使用定理 `Part.toOption.congr_simp`：∀ {α : Type u_1} (o o_1 : Part α),   o = o_1 →
 ∀ {inst : Decidable o.Dom} [inst_1 : Decidable o_1.Dom], o.toOption = o_1.toOpt
ion
· 使用定理 `Part.Dom.bind`：∀ {α : Type u_1} {β : Type u_2} {o : Part α} (h : o.Dom) 
(f : α → Part β), o.bind f = f (o.get h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.toOption_eq_none_iff`：toOption_eq_none_iff {a : Part α} [Decidable 
a.Dom] : a.toOption = Option.none ↔ ¬a.Dom
· 使用定理 `Part.Dom.of_bind`：∀ {α : Type u_1} {β : Type u_2} {f : α → Part β} {a : 
Part α}, (a.bind f).Dom → a.Dom
-/
theorem bind_toOption (f : α → Part β) (o : Part α) [Decidable o.Dom] [∀ a, Decidable (f a).Dom]
    [Decidable (o.bind f).Dom] :
    (o.bind f).toOption = o.toOption.elim Option.none fun a => (f a).toOption := by
  by_cases h : o.Dom
  · simp_rw [h.toOption, h.bind]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    exact Part.toOption_eq_none_iff.2 fun ho => h ho.of_bind
/-
**Part.bind_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_assoc {γ} (f : Part α) (g : α -> Part β) (k : β -> Part γ) : (f.bind 
g).bind k = f.bind fun x => (g x).bind k
参数：f : Part α；g : α -> Part β；k : β -> Part γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
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
theorem bind_assoc {γ} (f : Part α) (g : α → Part β) (k : β → Part γ) :
    (f.bind g).bind k = f.bind fun x => (g x).bind k :=
  ext fun a => by
    simp only [mem_bind_iff]
    exact ⟨fun ⟨_, ⟨_, h₁, h₂⟩, h₃⟩ => ⟨_, h₁, _, h₂, h₃⟩,
           fun ⟨_, h₁, _, h₂, h₃⟩ => ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp]
/-
**Part.bind_map** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f x).bind g = x.bin
d fun y => g (f y)
参数：f : α -> β；x；g : β -> Part γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.bind_some_eq_map`：bind_some_eq_map (f : α -> β) (x : Part α) : x.bi
nd (fun y => some (f y)) = map f x
· 使用定理 `Part.bind_assoc`：bind_assoc {γ} (f : Part α) (g : α -> Part β) (k : β ->
 Part γ) : (f.bind g).bind k = f.bind fun x => (g x).bind k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_map {γ} (f : α → β) (x) (g : β → Part γ) :
    (map f x).bind g = x.bind fun y => g (f y) := by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp]
/-
**Part.map_bind** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：map_bind {γ} (f : α -> Part β) (x : Part α) (g : β -> γ) : map g (x.bind f
) = x.bind fun y => map g (f y)
参数：f : α -> Part β；x : Part α；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.bind_some_eq_map`：bind_some_eq_map (f : α -> β) (x : Part α) : x.bi
nd (fun y => some (f y)) = map f x
· 使用定理 `Part.bind_assoc`：bind_assoc {γ} (f : Part α) (g : α -> Part β) (k : β ->
 Part γ) : (f.bind g).bind k = f.bind fun x => (g x).bind k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_bind {γ} (f : α → Part β) (x : Part α) (g : β → γ) :
    map g (x.bind f) = x.bind fun y => map g (f y) := by
  rw [← bind_some_eq_map, bind_assoc]; simp [bind_some_eq_map]
/-
**Part.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：map_map (g : β -> γ) (f : α -> β) (o : Part α) : map g (map f o) = map (g 
∘ f) o
参数：g : β -> γ；f : α -> β；o : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map (g : β → γ) (f : α → β) (o : Part α) : map g (map f o) = map (g ∘ f) o := by
  simp [map, Function.comp_assoc]
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad Part where
  pure := @some
  map := @map
  bind := @Part.bind
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad
      Part where
  bind_pure_comp := @bind_some_eq_map
  id_map f := by cases f; rfl
  pure_bind := @bind_some
  bind_assoc := @bind_assoc
  map_const := by simp [Functor.mapConst, Functor.map]
  --Porting TODO : In Lean3 these were automatic by a tactic
  seqLeft_eq x y := ext'
    (by simp [SeqLeft.seqLeft, Part.bind, assert, Seq.seq, (· <$> ·), and_comm])
    (fun _ _ => rfl)
  seqRight_eq x y := ext'
    (by simp [SeqRight.seqRight, Part.bind, assert, Seq.seq, (· <$> ·)])
    (fun _ _ => rfl)
  pure_seq x y := ext'
    (by simp [Seq.seq, Part.bind, assert, (· <$> ·), pure])
    (fun _ _ => rfl)
  bind_map x y := ext'
    (by simp [(· >>= ·), Part.bind, assert, Seq.seq, (· <$> ·)])
    (fun _ _ => rfl)
/-
**Part.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map f o = o
参数：H : forall x : α, f x = x；o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `LawfulMonad.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : Monad m
} [self : LawfulMonad m], LawfulApplicative m
· 使用定理 `Part.instLawfulMonad`：LawfulMonad Part
-/
theorem map_id' {f : α → α} (H : ∀ x : α, f x = x) (o) : map f o = o := by
  rw [show f = id from funext H]; exact id_map o

@[simp]
/-
**Part.bind_some_right** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_some_right (x : Part α) : x.bind some = x
参数：x : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.bind_some_eq_map`：bind_some_eq_map (f : α -> β) (x : Part α) : x.bi
nd (fun y => some (f y)) = map f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Part.map_id'`：map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map
 f o = o
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_some_right (x : Part α) : x.bind some = x := by
  rw [bind_some_eq_map]
  simp [map_id']

@[simp]
/-
**Part.pure_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：pure_eq_some (a : α) : pure a = some a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_eq_some (a : α) : pure a = some a :=
  rfl

@[simp]
/-
**Part.ret_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：ret_eq_some (a : α) : (return a : Part α) = some a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ret_eq_some (a : α) : (return a : Part α) = some a :=
  rfl

@[simp]
/-
**Part.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：map_eq_map {α β} (f : α -> β) (o : Part α) : f < > o = map f o
参数：f : α -> β；o : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq_map {α β} (f : α → β) (o : Part α) : f <$> o = map f o :=
  rfl

@[simp]
/-
**Part.bind_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_eq_bind {α β} (f : Part α) (g : α -> Part β) : f >>= g = f.bind g
参数：f : Part α；g : α -> Part β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_eq_bind {α β} (f : Part α) (g : α → Part β) : f >>= g = f.bind g :=
  rfl
/-
**Part.bind_le** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_le {α} (x : Part α) (f : α -> Part β) (y : Part β) : x >>= f <= y ↔ f
orall a, a in x -> f a <= y
参数：x : Part α；f : α -> Part β；y : Part β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem bind_le {α} (x : Part α) (f : α → Part β) (y : Part β) :
    x >>= f ≤ y ↔ ∀ a, a ∈ x → f a ≤ y := by
  constructor <;> intro h
  · intro a h' b
    have h := h b
    simp only [and_imp, bind_eq_bind, mem_bind_iff, exists_imp] at h
    apply h _ h'
  · intro b h'
    simp only [bind_eq_bind, mem_bind_iff] at h'
    rcases h' with ⟨a, h₀, h₁⟩
    apply h _ h₀ _ h₁

-- TODO: if `MonadFail` is defined, define the below instance.
-- instance : MonadFail Part :=
--   { Part.monad with fail := fun _ _ => none }

/-- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
/-
**Part.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：restrict (p : Prop) (o : Part α) (H : p -> o.Dom) : Part α
参数：p : Prop；o : Part α；H : p -> o.Dom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined.
-/
def restrict (p : Prop) (o : Part α) (H : p → o.Dom) : Part α :=
  ⟨p, fun h => o.get (H h)⟩

@[simp]
/-
**Part.mem_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_restrict (p : Prop) (o : Part α) (h : p -> o.Dom) (a : α) : a in restr
ict p o h ↔ p ∧ a in o
参数：p : Prop；o : Part α；h : p -> o.Dom；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_restrict (p : Prop) (o : Part α) (h : p → o.Dom) (a : α) :
    a ∈ restrict p o h ↔ p ∧ a ∈ o := by
  dsimp [restrict, mem_eq]; constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀, ⟨_, h₁⟩⟩
  rintro ⟨h₀, _, h₂⟩; exact ⟨h₀, h₂⟩

/-- `unwrap o` gets the value at `o`, ignoring the condition. This function is unsound. -/
/-
**Part.unwrap** 是 Mathlib 中的一个unsafe-def，位于命名空间 `Part`。
形式化陈述：{α : Type u_1} → Part α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`unwrap o` gets the value at `o`, ignoring the condition. This function is unsou
nd.
-/
unsafe def unwrap (o : Part α) : α :=
  o.get lcProof
/-
**Part.assert_defined** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：assert_defined {p : Prop} {f : p -> Part α} : forall h : p, (f h).Dom -> (
assert p f).Dom
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem assert_defined {p : Prop} {f : p → Part α} : ∀ h : p, (f h).Dom → (assert p f).Dom :=
  Exists.intro
/-
**Part.bind_defined** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_defined {f : Part α} {g : α -> Part β} : forall h : f.Dom, (g (f.get 
h)).Dom -> (f.bind g).Dom
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.assert_defined`：assert_defined {p : Prop} {f : p -> Part α} : foral
l h : p, (f h).Dom -> (assert p f).Dom
-/
theorem bind_defined {f : Part α} {g : α → Part β} :
    ∀ h : f.Dom, (g (f.get h)).Dom → (f.bind g).Dom :=
  assert_defined

@[simp]
/-
**Part.bind_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：bind_dom {f : Part α} {g : α -> Part β} : (f.bind g).Dom ↔ exists h : f.Do
m, (g (f.get h)).Dom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bind_dom {f : Part α} {g : α → Part β} : (f.bind g).Dom ↔ ∃ h : f.Dom, (g (f.get h)).Dom :=
  Iff.rfl

section Instances

/-!
We define several instances for constants and operations on `Part α` inherited from `α`.

This section could be moved to a separate file to avoid the import of
`Mathlib/Algebra/Notation/Defs.lean`.
-/

@[to_additive]
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define several instances for constants and operations on `Part α` inherited f
rom `α`.

This section could be moved to a separate file to avoid the import of
`Mathlib/Algebra/Notation/Defs.lean`.
-/
instance [One α] : One (Part α) where one := pure 1

@[to_additive]
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] : Mul (Part α) where mul a b := (· * ·) <$> a <*> b

@[to_additive]
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inv α] : Inv (Part α) where inv := map Inv.inv

@[to_additive]
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Div α] : Div (Part α) where div a b := (· / ·) <$> a <*> b
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mod α] : Mod (Part α) where mod a b := (· % ·) <$> a <*> b
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Append α] : Append (Part α) where append a b := (· ++ ·) <$> a <*> b
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inter α] : Inter (Part α) where inter a b := (· ∩ ·) <$> a <*> b
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Union α] : Union (Part α) where union a b := (· ∪ ·) <$> a <*> b
/-
**Part.** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SDiff α] : SDiff (Part α) where sdiff a b := (· \ ·) <$> a <*> b

section

@[to_additive]
/-
**Part.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mul_def [Mul α] (a b : Part α) : a * b = bind a fun y => map (y * ·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def [Mul α] (a b : Part α) : a * b = bind a fun y ↦ map (y * ·) b := rfl

@[to_additive]
/-
**Part.one_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：one_def [One α] : (1 : Part α) = some 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def [One α] : (1 : Part α) = some 1 := rfl

@[to_additive]
/-
**Part.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：inv_def [Inv α] (a : Part α) : a⁻¹ = Part.map (·⁻¹) a
参数：a : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def [Inv α] (a : Part α) : a⁻¹ = Part.map (·⁻¹) a := rfl

@[to_additive]
/-
**Part.div_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：div_def [Div α] (a b : Part α) : a / b = bind a fun y => map (y / ·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_def [Div α] (a b : Part α) : a / b = bind a fun y => map (y / ·) b := rfl
/-
**Part.mod_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mod_def [Mod α] (a b : Part α) : a % b = bind a fun y => map (y % ·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mod_def [Mod α] (a b : Part α) : a % b = bind a fun y => map (y % ·) b := rfl
/-
**Part.append_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：append_def [Append α] (a b : Part α) : a ++ b = bind a fun y => map (y ++ 
·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_def [Append α] (a b : Part α) : a ++ b = bind a fun y => map (y ++ ·) b := rfl
/-
**Part.inter_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：inter_def [Inter α] (a b : Part α) : a inter b = bind a fun y => map (y in
ter ·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_def [Inter α] (a b : Part α) : a ∩ b = bind a fun y => map (y ∩ ·) b := rfl
/-
**Part.union_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：union_def [Union α] (a b : Part α) : a union b = bind a fun y => map (y un
ion ·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_def [Union α] (a b : Part α) : a ∪ b = bind a fun y => map (y ∪ ·) b := rfl
/-
**Part.sdiff_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：sdiff_def [SDiff α] (a b : Part α) : a \ b = bind a fun y => map (y \ ·) b
参数：a b : Part α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_def [SDiff α] (a b : Part α) : a \ b = bind a fun y => map (y \ ·) b := rfl

end

@[to_additive]
/-
**Part.one_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：one_mem_one [One α] : (1 : α) in (1 : Part α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem one_mem_one [One α] : (1 : α) ∈ (1 : Part α) :=
  ⟨trivial, rfl⟩

@[to_additive]
/-
**Part.mul_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mul_mem_mul [Mul α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in 
b) : ma * mb in a * b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_mem_mul [Mul α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma * mb ∈ a * b := ⟨⟨ha.1, hb.1⟩, by simp only [← ha.2, ← hb.2]; rfl⟩

@[to_additive]
/-
**Part.left_dom_of_mul_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : a.Dom
参数：hab : Dom (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : a.Dom := hab.1

@[to_additive]
/-
**Part.right_dom_of_mul_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : b.Dom
参数：hab : Dom (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : b.Dom := hab.2

@[to_additive (attr := simp)]
/-
**Part.mul_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mul_get_eq [Mul α] (a b : Part α) (hab : Dom (a * b)) : (a * b).get hab = 
a.get (left_dom_of_mul_dom hab) * b.get (right_dom_of_mul_dom hab)
参数：a b : Part α；hab : Dom (a * b)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_get_eq [Mul α] (a b : Part α) (hab : Dom (a * b)) :
    (a * b).get hab = a.get (left_dom_of_mul_dom hab) * b.get (right_dom_of_mul_dom hab) := rfl

@[to_additive]
/-
**Part.some_mul_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_mul_some [Mul α] (a b : α) : some a * some b = some (a * b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_mul_some [Mul α] (a b : α) : some a * some b = some (a * b) := by simp [mul_def]

@[to_additive]
/-
**Part.inv_mem_inv** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：inv_mem_inv [Inv α] (a : Part α) (ma : α) (ha : ma in a) : ma⁻¹ in a⁻¹
参数：a : Part α；ma : α；ha : ma in a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mem_inv [Inv α] (a : Part α) (ma : α) (ha : ma ∈ a) : ma⁻¹ ∈ a⁻¹ := by
  simp [inv_def]; aesop

@[to_additive]
/-
**Part.inv_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：inv_some [Inv α] (a : α) : (some a)⁻¹ = some a⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_some [Inv α] (a : α) : (some a)⁻¹ = some a⁻¹ :=
  rfl

@[to_additive]
/-
**Part.div_mem_div** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：div_mem_div [Div α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in 
b) : ma / mb in a / b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem div_mem_div [Div α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma / mb ∈ a / b := by simp [div_def]; aesop

@[to_additive]
/-
**Part.left_dom_of_div_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : a.Dom
参数：hab : Dom (a / b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : a.Dom := hab.1

@[to_additive]
/-
**Part.right_dom_of_div_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : b.Dom
参数：hab : Dom (a / b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : b.Dom := hab.2

@[to_additive (attr := simp)]
/-
**Part.div_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：div_get_eq [Div α] (a b : Part α) (hab : Dom (a / b)) : (a / b).get hab = 
a.get (left_dom_of_div_dom hab) / b.get (right_dom_of_div_dom hab)
参数：a b : Part α；hab : Dom (a / b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.left_dom_of_div_dom`：left_dom_of_div_dom [Div α] {a b : Part α} (ha
b : Dom (a / b)) : a.Dom
· 使用定理 `Part.right_dom_of_div_dom`：right_dom_of_div_dom [Div α] {a b : Part α} (
hab : Dom (a / b)) : b.Dom
-/
theorem div_get_eq [Div α] (a b : Part α) (hab : Dom (a / b)) :
    (a / b).get hab = a.get (left_dom_of_div_dom hab) / b.get (right_dom_of_div_dom hab) := by
  simp [div_def]; aesop

@[to_additive]
/-
**Part.some_div_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_div_some [Div α] (a b : α) : some a / some b = some (a / b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_div_some [Div α] (a b : α) : some a / some b = some (a / b) := by simp [div_def]
/-
**Part.mod_mem_mod** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mod_mem_mod [Mod α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in 
b) : ma % mb in a % b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mod_mem_mod [Mod α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma % mb ∈ a % b := by simp [mod_def]; aesop
/-
**Part.left_dom_of_mod_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : a.Dom
参数：hab : Dom (a % b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : a.Dom := hab.1
/-
**Part.right_dom_of_mod_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : b.Dom
参数：hab : Dom (a % b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : b.Dom := hab.2

@[simp]
/-
**Part.mod_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mod_get_eq [Mod α] (a b : Part α) (hab : Dom (a % b)) : (a % b).get hab = 
a.get (left_dom_of_mod_dom hab) % b.get (right_dom_of_mod_dom hab)
参数：a b : Part α；hab : Dom (a % b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.left_dom_of_mod_dom`：left_dom_of_mod_dom [Mod α] {a b : Part α} (ha
b : Dom (a % b)) : a.Dom
· 使用定理 `Part.right_dom_of_mod_dom`：right_dom_of_mod_dom [Mod α] {a b : Part α} (
hab : Dom (a % b)) : b.Dom
-/
theorem mod_get_eq [Mod α] (a b : Part α) (hab : Dom (a % b)) :
    (a % b).get hab = a.get (left_dom_of_mod_dom hab) % b.get (right_dom_of_mod_dom hab) := by
  simp [mod_def]; aesop
/-
**Part.some_mod_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_mod_some [Mod α] (a b : α) : some a % some b = some (a % b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_mod_some [Mod α] (a b : α) : some a % some b = some (a % b) := by simp [mod_def]
/-
**Part.append_mem_append** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：append_mem_append [Append α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb
 : mb in b) : ma ++ mb in a ++ b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem append_mem_append [Append α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma ++ mb ∈ a ++ b := by simp [append_def]; aesop
/-
**Part.left_dom_of_append_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : a.
Dom
参数：hab : Dom (a ++ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : a.Dom := hab.1
/-
**Part.right_dom_of_append_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : b
.Dom
参数：hab : Dom (a ++ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : b.Dom := hab.2

@[simp]
/-
**Part.append_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：append_get_eq [Append α] (a b : Part α) (hab : Dom (a ++ b)) : (a ++ b).ge
t hab = a.get (left_dom_of_append_dom hab) ++ b.get (right_dom_of_append_dom hab
)
参数：a b : Part α；hab : Dom (a ++ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.left_dom_of_append_dom`：left_dom_of_append_dom [Append α] {a b : Pa
rt α} (hab : Dom (a ++ b)) : a.Dom
· 使用定理 `Part.right_dom_of_append_dom`：right_dom_of_append_dom [Append α] {a b : 
Part α} (hab : Dom (a ++ b)) : b.Dom
-/
theorem append_get_eq [Append α] (a b : Part α) (hab : Dom (a ++ b)) : (a ++ b).get hab =
    a.get (left_dom_of_append_dom hab) ++ b.get (right_dom_of_append_dom hab) := by
  simp [append_def]; aesop
/-
**Part.some_append_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_append_some [Append α] (a b : α) : some a ++ some b = some (a ++ b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_append_some [Append α] (a b : α) : some a ++ some b = some (a ++ b) := by
  simp [append_def]
/-
**Part.inter_mem_inter** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：inter_mem_inter [Inter α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : 
mb in b) : ma inter mb in a inter b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem inter_mem_inter [Inter α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma ∩ mb ∈ a ∩ b := by simp [inter_def]; aesop
/-
**Part.left_dom_of_inter_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a inter b)) : a
.Dom
参数：hab : Dom (a inter b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a ∩ b)) : a.Dom := hab.1
/-
**Part.right_dom_of_inter_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a inter b)) : 
b.Dom
参数：hab : Dom (a inter b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a ∩ b)) : b.Dom := hab.2

@[simp]
/-
**Part.inter_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：inter_get_eq [Inter α] (a b : Part α) (hab : Dom (a inter b)) : (a inter b
).get hab = a.get (left_dom_of_inter_dom hab) inter b.get (right_dom_of_inter_do
m hab)
参数：a b : Part α；hab : Dom (a inter b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.left_dom_of_inter_dom`：left_dom_of_inter_dom [Inter α] {a b : Part 
α} (hab : Dom (a inter b)) : a.Dom
· 使用定理 `Part.right_dom_of_inter_dom`：right_dom_of_inter_dom [Inter α] {a b : Par
t α} (hab : Dom (a inter b)) : b.Dom
-/
theorem inter_get_eq [Inter α] (a b : Part α) (hab : Dom (a ∩ b)) :
    (a ∩ b).get hab = a.get (left_dom_of_inter_dom hab) ∩ b.get (right_dom_of_inter_dom hab) := by
  simp [inter_def]; aesop
/-
**Part.some_inter_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_inter_some [Inter α] (a b : α) : some a inter some b = some (a inter 
b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_inter_some [Inter α] (a b : α) : some a ∩ some b = some (a ∩ b) := by
  simp [inter_def]
/-
**Part.union_mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：union_mem_union [Union α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : 
mb in b) : ma union mb in a union b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem union_mem_union [Union α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma ∪ mb ∈ a ∪ b := by simp [union_def]; aesop
/-
**Part.left_dom_of_union_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a union b)) : a
.Dom
参数：hab : Dom (a union b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a ∪ b)) : a.Dom := hab.1
/-
**Part.right_dom_of_union_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a union b)) : 
b.Dom
参数：hab : Dom (a union b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a ∪ b)) : b.Dom := hab.2

@[simp]
/-
**Part.union_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：union_get_eq [Union α] (a b : Part α) (hab : Dom (a union b)) : (a union b
).get hab = a.get (left_dom_of_union_dom hab) union b.get (right_dom_of_union_do
m hab)
参数：a b : Part α；hab : Dom (a union b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.left_dom_of_union_dom`：left_dom_of_union_dom [Union α] {a b : Part 
α} (hab : Dom (a union b)) : a.Dom
· 使用定理 `Part.right_dom_of_union_dom`：right_dom_of_union_dom [Union α] {a b : Par
t α} (hab : Dom (a union b)) : b.Dom
-/
theorem union_get_eq [Union α] (a b : Part α) (hab : Dom (a ∪ b)) :
    (a ∪ b).get hab = a.get (left_dom_of_union_dom hab) ∪ b.get (right_dom_of_union_dom hab) := by
  simp [union_def]; aesop
/-
**Part.some_union_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_union_some [Union α] (a b : α) : some a union some b = some (a union 
b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_union_some [Union α] (a b : α) : some a ∪ some b = some (a ∪ b) := by simp [union_def]
/-
**Part.sdiff_mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：sdiff_mem_sdiff [SDiff α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : 
mb in b) : ma \ mb in a \ b
参数：a b : Part α；ma mb : α；ha : ma in a；hb : mb in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem sdiff_mem_sdiff [SDiff α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma \ mb ∈ a \ b := by simp [sdiff_def]; aesop
/-
**Part.left_dom_of_sdiff_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：left_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : a.Dom
参数：hab : Dom (a \ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : a.Dom := hab.1
/-
**Part.right_dom_of_sdiff_dom** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：right_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : b.Do
m
参数：hab : Dom (a \ b)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : b.Dom := hab.2

@[simp]
/-
**Part.sdiff_get_eq** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：sdiff_get_eq [SDiff α] (a b : Part α) (hab : Dom (a \ b)) : (a \ b).get ha
b = a.get (left_dom_of_sdiff_dom hab) \ b.get (right_dom_of_sdiff_dom hab)
参数：a b : Part α；hab : Dom (a \ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Part.left_dom_of_sdiff_dom`：left_dom_of_sdiff_dom [SDiff α] {a b : Part 
α} (hab : Dom (a \ b)) : a.Dom
· 使用定理 `Part.right_dom_of_sdiff_dom`：right_dom_of_sdiff_dom [SDiff α] {a b : Par
t α} (hab : Dom (a \ b)) : b.Dom
-/
theorem sdiff_get_eq [SDiff α] (a b : Part α) (hab : Dom (a \ b)) :
    (a \ b).get hab = a.get (left_dom_of_sdiff_dom hab) \ b.get (right_dom_of_sdiff_dom hab) := by
  simp [sdiff_def]; aesop
/-
**Part.some_sdiff_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：some_sdiff_some [SDiff α] (a b : α) : some a \ some b = some (a \ b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_sdiff_some [SDiff α] (a b : α) : some a \ some b = some (a \ b) := by simp [sdiff_def]

end Instances

end Part

