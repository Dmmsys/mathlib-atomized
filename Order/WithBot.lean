/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Order.TypeTags
public import Mathlib.Data.Option.NAry
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Lift
public import Mathlib.Data.Option.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic

/-!
# `WithBot`, `WithTop`

Adding a `bot` or a `top` to an order.

## Main declarations

* `With<Top/Bot> α`: Equips `Option α` with the order on `α` plus `none` as the top/bottom element.

-/

@[expose] public section

variable {α β γ δ : Type*}

namespace WithBot

variable {a b : α}

@[to_dual]
/-
**WithBot.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：nontrivial [Nonempty α] : Nontrivial (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nontrivial [Nonempty α] : Nontrivial (WithBot α) :=
  inferInstanceAs <| Nontrivial (Option α)

@[to_dual]
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (WithBot α) :=
  inferInstanceAs <| Unique (Option α)

open Function

@[to_dual]
/-
**WithBot.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_injective : Injective ((↑) : α -> WithBot α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
theorem coe_injective : Injective ((↑) : α → WithBot α) :=
  Option.some_injective _

@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_inj : (a : WithBot α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
-/
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

@[to_dual]
/-
**WithBot.** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x :=
  Option.forall

@[to_dual]
/-
**WithBot.** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x :=
  Option.exists

@[to_dual]
/-
**WithBot.none_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：none_eq_bot : (none : WithBot α) = (⊥ : WithBot α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl

@[to_dual]
/-
**WithBot.some_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：some_eq_coe (a : α) : (Option.some a : WithBot α) = (↑a : WithBot α)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem some_eq_coe (a : α) : (Option.some a : WithBot α) = (↑a : WithBot α) :=
  rfl

@[to_dual (attr := simp)]
/-
**WithBot.bot_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：bot_ne_coe : ⊥ != (a : WithBot α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  nofun

@[to_dual (attr := simp)]
/-
**WithBot.coe_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_ne_bot : (a : WithBot α) != ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  nofun

/-- Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries. -/
@[to_dual
/-- Specialization of `Option.getD` to values in `WithTop α` that respects API boundaries. -/]
/-
**WithBot.unbotD** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：unbotD (d : α) (x : WithBot α) : α
参数：d : α；x : WithBot α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unbotD (d : α) (x : WithBot α) : α :=
  recBotCoe d id x

@[to_dual (attr := simp)]
/-
**WithBot.unbotD_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbotD_bot {α} (d : α) : unbotD d ⊥ = d
参数：d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unbotD_bot {α} (d : α) : unbotD d ⊥ = d :=
  rfl

@[to_dual (attr := simp)]
/-
**WithBot.unbotD_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbotD_coe {α} (d x : α) : unbotD d x = x
参数：d x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unbotD_coe {α} (d x : α) : unbotD d x = x :=
  rfl

@[to_dual]
/-
**WithBot.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_eq_coe : (a : WithBot α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_inj`：coe_inj : (a : WithBot α) = b ↔ a = b
-/
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b := coe_inj

@[to_dual]
/-
**WithBot.unbotD_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbotD_eq_iff {d y : α} {x : WithBot α} : unbotD d x = y ↔ x = y ∨ x = ⊥ ∧
 y = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem unbotD_eq_iff {d y : α} {x : WithBot α} : unbotD d x = y ↔ x = y ∨ x = ⊥ ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[to_dual (attr := simp)]
/-
**WithBot.unbotD_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbotD_eq_self_iff {d : α} {x : WithBot α} : unbotD d x = d ↔ x = d ∨ x = 
⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbotD_eq_self_iff {d : α} {x : WithBot α} : unbotD d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbotD_eq_iff]

@[to_dual]
/-
**WithBot.unbotD_eq_unbotD_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbotD_eq_unbotD_iff {d : α} {x y : WithBot α} : unbotD d x = unbotD d y ↔
 x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbotD_eq_unbotD_iff {d : α} {x y : WithBot α} :
    unbotD d x = unbotD d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
  induction y <;> simp [unbotD_eq_iff, or_comm]

/-- Lift a map `f : α → β` to `WithBot α → WithBot β`. Implemented using `Option.map`. -/
@[to_dual
/-- Lift a map `f : α → β` to `WithTop α → WithTop β`. Implemented using `Option.map`. -/]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f

@[to_dual (attr := simp)]
/-
**WithBot.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_bot (f : α -> β) : map f ⊥ = ⊥
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**WithBot.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_coe (f : α -> β) (a : α) : map f a = f a
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[to_dual (attr := simp)]
/-
**WithBot.map_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：map_eq_bot_iff {f : α -> β} {a : WithBot α} : map f a = ⊥ ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_eq_none_iff`：∀ {α : Type u_1} {x : Option α} {α_1 : Type u_2}
 {f : α → α_1}, Option.map f x = none ↔ x = none
-/
lemma map_eq_bot_iff {f : α → β} {a : WithBot α} :
    map f a = ⊥ ↔ a = ⊥ := Option.map_eq_none_iff

@[to_dual]
/-
**WithBot.map_eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_eq_some_iff {f : α -> β} {y : β} {v : WithBot α} : WithBot.map f v = .
some y ↔ exists x, v = .some x ∧ f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_eq_some_iff`：∀ {α : Type u_1} {b : α} {α_1 : Type u_2} {x : O
ption α_1} {f : α_1 → α},   Option.map f x = some b ↔ ∃ a, x = some a ∧ f a = b
-/
theorem map_eq_some_iff {f : α → β} {y : β} {v : WithBot α} :
    WithBot.map f v = .some y ↔ ∃ x, v = .some x ∧ f x = y := Option.map_eq_some_iff

@[to_dual]
/-
**WithBot.some_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：some_eq_map_iff {f : α -> β} {y : β} {v : WithBot α} : .some y = WithBot.m
ap f v ↔ exists x, v = .some x ∧ f x = y
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
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem some_eq_map_iff {f : α → β} {y : β} {v : WithBot α} :
    .some y = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = y := by
  cases v <;> simp [eq_comm]

@[to_dual (attr := simp)]
/-
**WithBot.map_id** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_id : map (id : α -> α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_id`：∀ {α : Type u_1}, Option.map id = id
-/
theorem map_id : map (id : α → α) = id :=
  Option.map_id

@[to_dual (attr := simp)]
/-
**WithBot.map_map** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_map (h : β -> γ) (g : α -> β) (a : WithBot α) : map h (map g a) = map 
(h ∘ g) a
参数：h : β -> γ；g : α -> β；a : WithBot α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
-/
theorem map_map (h : β → γ) (g : α → β) (a : WithBot α) : map h (map g a) = map (h ∘ g) a :=
  Option.map_map h g a

@[to_dual]
/-
**WithBot.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：comp_map (h : β -> γ) (g : α -> β) (x : WithBot α) : x.map (h ∘ g) = (x.ma
p g).map h
参数：h : β -> γ；g : α -> β；x : WithBot α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.map_map`：map_map (h : β -> γ) (g : α -> β) (a : WithBot α) : map
 h (map g a) = map (h ∘ g) a
-/
theorem comp_map (h : β → γ) (g : α → β) (x : WithBot α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[to_dual (attr := simp)]
/-
**WithBot.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_comp_map (f : α -> β) (g : β -> γ) : WithBot.map g ∘ WithBot.map f = W
ithBot.map (g ∘ f)
参数：f : α -> β；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_comp_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f :
 α → β) (g : β → γ), Option.map g ∘ Option.map f = Option.map (g ∘ f)
-/
theorem map_comp_map (f : α → β) (g : β → γ) :
    WithBot.map g ∘ WithBot.map f = WithBot.map (g ∘ f) :=
  Option.map_comp_map f g

@[to_dual]
/-
**WithBot.map_comm** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_comm {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ} (h : g₁ ∘
 f₁ = g₂ ∘ f₂) (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a)
参数：h : g₁ ∘ f₁ = g₂ ∘ f₂；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_comm`：map_comm {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ 
: γ -> δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) : (Option.map f₁ a).map g₁ = (Option.m
ap f₂…
-/
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

@[to_dual]
/-
**WithBot.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_injective {f : α -> β} (Hf : Injective f) : Injective (WithBot.map f)
参数：Hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_injective`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Funct
ion.Injective f → Function.Injective (Option.map f)
-/
theorem map_injective {f : α → β} (Hf : Injective f) : Injective (WithBot.map f) :=
  Option.map_injective Hf

/-- The image of a binary function `f : α → β → γ` as a function
`WithBot α → WithBot β → WithBot γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_dual
/-- The image of a binary function `f : α → β → γ` as a function
`WithTop α → WithTop β → WithTop γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map₂ : (α → β → γ) → WithBot α → WithBot β → WithBot γ := Option.map₂
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl

@[to_dual (attr := simp)]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f ⊥ b = ⊥ := rfl
@[to_dual (attr := simp)]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a ⊥ = ⊥ := by cases a <;> rfl

@[to_dual (attr := simp)]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[to_dual (attr := simp)]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by cases a <;> rfl

@[to_dual (attr := simp)]
/-
**WithBot.map** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：map (f : α -> β) : WithBot α -> WithBot β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithBot α} {b : WithBot β} :
    map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := Option.map₂_eq_none_iff

@[to_dual]
/-
**WithBot.ne_bot_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ne_bot_iff_exists {x : WithBot α} : x != ⊥ ↔ exists a : α, ↑a = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.ne_none_iff_exists`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ ∃
 x, some x = o
-/
lemma ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x := Option.ne_none_iff_exists

@[to_dual]
/-
**WithBot.eq_bot_iff_forall_ne** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：eq_bot_iff_forall_ne {x : WithBot α} : x = ⊥ ↔ forall a : α, ↑a != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.eq_none_iff_forall_some_ne`：∀ {α : Type u_1} {o : Option α}, o = 
none ↔ ∀ (a : α), some a ≠ o
-/
lemma eq_bot_iff_forall_ne {x : WithBot α} : x = ⊥ ↔ ∀ a : α, ↑a ≠ x :=
  Option.eq_none_iff_forall_some_ne

@[to_dual]
/-
**WithBot.forall_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：forall_ne_bot {p : WithBot α -> Prop} : (forall x != ⊥, p x) ↔ forall x : 
α, p x
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
theorem forall_ne_bot {p : WithBot α → Prop} : (∀ x ≠ ⊥, p x) ↔ ∀ x : α, p x := by
  simp [ne_bot_iff_exists]

@[to_dual]
/-
**WithBot.exists_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：exists_ne_bot {p : WithBot α -> Prop} : (exists x != ⊥, p x) ↔ exists x : 
α, p x
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
theorem exists_ne_bot {p : WithBot α → Prop} : (∃ x ≠ ⊥, p x) ↔ ∃ x : α, p x := by
  simp [ne_bot_iff_exists]

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
@[to_dual
/-- Deconstruct a `x : WithTop α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/]
/-
**WithBot.unbot** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → (x : WithBot α) → x ≠ ⊥ → α
参数：x : WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α | (x : α), _ => x

@[to_dual (attr := simp)]
/-
**WithBot.coe_unbot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.unbot hx) = x
参数：x : WithBot α；hx : x ≠ ⊥；x.unbot hx。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_unbot : ∀ (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl

@[to_dual (attr := simp)]
/-
**WithBot.unbot_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbot_coe (x : α) (h : (x : WithBot α) != ⊥
参数：x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl

@[to_dual]
/-
**WithBot.canLift** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：canLift : CanLift (WithBot α) α (↑) fun r => r != ⊥ where prf x h
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
-/
instance canLift : CanLift (WithBot α) α (↑) fun r => r ≠ ⊥ where
  prf x h := ⟨x.unbot h, coe_unbot _ _⟩

@[to_dual]
/-
**WithBot.instTop** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instTop [Top α] : Top (WithBot α) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTop [Top α] : Top (WithBot α) where
  top := (⊤ : α)

@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_top** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤ := rfl
@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_eq_top [Top α] {a : α} : (a : WithBot α) = ⊤ ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
-/
lemma coe_eq_top [Top α] {a : α} : (a : WithBot α) = ⊤ ↔ a = ⊤ := coe_eq_coe
@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.top_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：top_eq_coe [Top α] {a : α} : ⊤ = (a : WithBot α) ↔ ⊤ = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
-/
lemma top_eq_coe [Top α] {a : α} : ⊤ = (a : WithBot α) ↔ ⊤ = a := coe_eq_coe

@[to_dual]
/-
**WithBot.unbot_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbot_eq_iff {a : WithBot α} {b : α} (h : a != ⊥) : a.unbot h = b ↔ a = b
参数：h : a != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem unbot_eq_iff {a : WithBot α} {b : α} (h : a ≠ ⊥) :
    a.unbot h = b ↔ a = b := by
  induction a
  · simpa using h rfl
  · simp

@[to_dual]
/-
**WithBot.eq_unbot_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：eq_unbot_iff {a : α} {b : WithBot α} (h : b != ⊥) : a = b.unbot h ↔ a = b
参数：h : b != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_unbot_iff {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a = b.unbot h ↔ a = b := by
  induction b
  · simpa using h rfl
  · simp

@[to_dual]
/-
**WithBot.unbot_inj** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbot_inj {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥) : a.unbot ha = b.u
nbot hb ↔ a = b
参数：ha : a != ⊥；hb : b != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.unbot_eq_iff`：unbot_eq_iff {a : WithBot α} {b : α} (h : a != ⊥) 
: a.unbot h = b ↔ a = b
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem unbot_inj {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    a.unbot ha = b.unbot hb ↔ a = b := by
  rw [unbot_eq_iff, coe_unbot]

/-- The equivalence between the non-bottom elements of `WithBot α` and `α`. -/
@[to_dual (attr := simps)
/-- The equivalence between the non-top elements of `WithTop α` and `α`. -/]
/-
**WithBot._root_.Equiv.withBotSubtypeNe** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Equiv.withBotSubtypeNe : {y : WithBot α // y ≠ ⊥} ≃ α where
  toFun := fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Function that sends an element of `WithBot α` to `α`,
with an arbitrary default value for `⊥`. -/
@[to_dual
/-- Function that sends an element of `WithTop α` to `α`,
with an arbitrary default value for `⊤`. -/]
/-
**WithBot.unbotA** 是 Mathlib 中的一个缩写定义，位于命名空间 `WithBot`。
形式化陈述：unbotA [Nonempty α] : WithBot α -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev unbotA [Nonempty α] : WithBot α → α := unbotD (Classical.arbitrary α)

@[to_dual]
/-
**WithBot.unbotA_eq_unbot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotA_eq_unbot [Nonempty α] {a : WithBot α} (ha : a != ⊥) : unbotA a = un
bot a ha
参数：ha : a != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unbotA_eq_unbot [Nonempty α] {a : WithBot α} (ha : a ≠ ⊥) : unbotA a = unbot a ha := by
  cases a with
  | bot => contradiction
  | coe a => simp

end WithBot

namespace Equiv

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithBot e`. -/
@[to_dual (attr := simps apply)
/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithTop e`. -/]
/-
**Equiv.withBotCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：withBotCongr (e : α ≃ β) : WithBot α ≃ WithBot β where toFun
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def withBotCongr (e : α ≃ β) : WithBot α ≃ WithBot β where
  toFun := WithBot.map e
  invFun := WithBot.map e.symm
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

attribute [grind =] withBotCongr_apply withTopCongr_apply

@[to_dual (attr := simp)]
/-
**Equiv.withBotCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：withBotCongr_refl : withBotCongr (Equiv.refl α) = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `WithBot.map_id`：map_id : map (id : α -> α) = id
-/
theorem withBotCongr_refl : withBotCongr (Equiv.refl α) = Equiv.refl _ :=
  Equiv.ext <| congr_fun WithBot.map_id

@[to_dual (attr := simp, grind =)]
/-
**Equiv.withBotCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：withBotCongr_symm (e : α ≃ β) : withBotCongr e.symm = (withBotCongr e).sym
m
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem withBotCongr_symm (e : α ≃ β) : withBotCongr e.symm = (withBotCongr e).symm :=
  rfl

@[to_dual (attr := simp)]
/-
**Equiv.withBotCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：withBotCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : withBotCongr (e₁.trans e₂) 
= (withBotCongr e₁).trans (withBotCongr e₂)
参数：e₁ : α ≃ β；e₂ : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.withBotCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a
 : WithBot α), e.withBotCongr a = WithBot.map (⇑e) a
· 使用定理 `WithBot.map_map`：map_map (h : β -> γ) (g : α -> β) (a : WithBot α) : map
 h (map g a) = map (h ∘ g) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem withBotCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    withBotCongr (e₁.trans e₂) = (withBotCongr e₁).trans (withBotCongr e₂) := by
  ext x
  simp

end Equiv

-- TODO: do we really need to preserve the def-eq between `LE` on `WithBot` and `WithTop`
-- moving forward? See discussion here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Order.20dual.20tactic/near/562584912

section LE
variable [LE α]

/-- Auxiliary definition for the order on `WithBot`. -/
@[mk_iff le_def_aux]
/-
**WithBot.LE** 是 Mathlib 中的一个归纳类型，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → [LE α] → WithBot α → WithBot α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the order on `WithBot`.
-/
protected inductive WithBot.LE : WithBot α → WithBot α → Prop
  | protected bot_le (x : WithBot α) : WithBot.LE ⊥ x
  | protected coe_le_coe {a b : α} : a ≤ b → WithBot.LE a b

/-- The order on `WithBot α`, defined by `⊥ ≤ y` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `WithBot α`, defined by `⊥ ≤ y` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤
 b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since
 it
cannot be accidentally unfolded too far.
-/
instance (priority := 10) WithBot.instLE : LE (WithBot α) where le := WithBot.LE

/-- The order on `WithTop α`, defined by `x ≤ ⊤` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ b : α, y = ↑b → ∃ a : α, x = ↑a ∧ a ≤ b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[to_dual existing]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `WithTop α`, defined by `x ≤ ⊤` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ b : α, y = ↑b → ∃ a : α, x = ↑a ∧ a ≤
 b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since
 it
cannot be accidentally unfolded too far.
-/
instance (priority := 10) WithTop.instLE : LE (WithTop α) where le a b := WithBot.LE (α := αᵒᵈ) b a
/-
**WithBot.le_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithBot.le_def {x y : WithBot α} : x <= y ↔ x = ⊥ ∨ exists a b : α, a <= b
 ∧ x = a ∧ y = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.le_def_aux`：∀ {α : Type u_1} [inst : LE α] (a a_1 : WithBot α), 
a.LE a_1 ↔ a = ⊥ ∨ ∃ a_2 b, a_2 ≤ b ∧ a = ↑a_2 ∧ a_1 = ↑b
-/
lemma WithBot.le_def {x y : WithBot α} : x ≤ y ↔ x = ⊥ ∨ ∃ a b : α, a ≤ b ∧ x = a ∧ y = b :=
  le_def_aux ..

@[to_dual existing le_def]
/-
**WithTop.le_def'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithTop.le_def' {x y : WithTop α} : x <= y ↔ y = ⊤ ∨ exists b a : α, a <= 
b ∧ y = b ∧ x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_def`：WithBot.le_def {x y : WithBot α} : x <= y ↔ x = ⊥ ∨ exis
ts a b : α, a <= b ∧ x = a ∧ y = b
-/
lemma WithTop.le_def' {x y : WithTop α} : x ≤ y ↔ y = ⊤ ∨ ∃ b a : α, a ≤ b ∧ y = b ∧ x = a :=
  WithBot.le_def

@[to_dual le_def']
/-
**WithTop.le_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithTop.le_def {x y : WithTop α} : x <= y ↔ y = ⊤ ∨ exists a b : α, a <= b
 ∧ x = a ∧ y = b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma WithTop.le_def {x y : WithTop α} : x ≤ y ↔ y = ⊤ ∨ ∃ a b : α, a ≤ b ∧ x = a ∧ y = b := by
  grind [WithTop.le_def']

end LE

section LT
variable [LT α]

/-- Auxiliary definition for the order on `WithBot`. -/
@[mk_iff lt_def_aux]
/-
**WithBot.LT** 是 Mathlib 中的一个归纳类型，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → [LT α] → WithBot α → WithBot α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the order on `WithBot`.
-/
protected inductive WithBot.LT [LT α] : WithBot α → WithBot α → Prop
  | protected bot_lt (b : α) : WithBot.LT ⊥ b
  | protected coe_lt_coe {a b : α} : a < b → WithBot.LT a b

/-- The order on `WithBot α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b`,
see `lt_iff_exists`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `WithBot α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a <
 b`,
see `lt_iff_exists`. The definition as an inductive predicate is preferred since
 it
cannot be accidentally unfolded too far.
-/
instance (priority := 10) WithBot.instLT : LT (WithBot α) where lt := WithBot.LT

/-- The order on `WithTop α`, defined by `↑a < ⊤` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ a : α, x = ↑a ∧ ∀ b : α, y = ↑b → a < b`,
see `le_if_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[to_dual existing]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `WithTop α`, defined by `↑a < ⊤` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ a : α, x = ↑a ∧ ∀ b : α, y = ↑b → a <
 b`,
see `le_if_forall`. The definition as an inductive predicate is preferred since 
it
cannot be accidentally unfolded too far.
-/
instance (priority := 10) WithTop.instLT : LT (WithTop α) where lt a b := WithBot.LT (α := αᵒᵈ) b a
/-
**WithBot.lt_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithBot.lt_def {x y : WithBot α} : x < y ↔ (x = ⊥ ∧ exists b : α, y = b) ∨
 exists a b : α, a < b ∧ x = a ∧ y = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithBot.lt_def_aux`：∀ {α : Type u_1} [inst : LT α] (a a_1 : WithBot α), 
  a.LT a_1 ↔ (∃ b, a = ⊥ ∧ a_1 = ↑b) ∨ ∃ a_2 b, a_2 < b ∧ a = ↑a_2 ∧ a_1 = ↑b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma WithBot.lt_def {x y : WithBot α} :
    x < y ↔ (x = ⊥ ∧ ∃ b : α, y = b) ∨ ∃ a b : α, a < b ∧ x = a ∧ y = b :=
  (lt_def_aux ..).trans <| by simp

@[to_dual existing lt_def]
/-
**WithTop.lt_def'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithTop.lt_def' {x y : WithTop α} : x < y ↔ (y = ⊤ ∧ exists a : α, x = a) 
∨ exists b a : α, a < b ∧ y = b ∧ x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_def`：WithBot.lt_def {x y : WithBot α} : x < y ↔ (x = ⊥ ∧ exis
ts b : α, y = b) ∨ exists a b : α, a < b ∧ x = a ∧ y = b
-/
lemma WithTop.lt_def' {x y : WithTop α} :
    x < y ↔ (y = ⊤ ∧ ∃ a : α, x = a) ∨ ∃ b a : α, a < b ∧ y = b ∧ x = a :=
  WithBot.lt_def

@[to_dual lt_def']
/-
**WithTop.lt_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithTop.lt_def {x y : WithTop α} : x < y ↔ (exists a : α, x = ↑a) ∧ y = ⊤ 
∨ exists a b : α, a < b ∧ x = ↑a ∧ y = ↑b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma WithTop.lt_def {x y : WithTop α} :
    x < y ↔ (∃ a : α, x = ↑a) ∧ y = ⊤ ∨ ∃ a b : α, a < b ∧ x = ↑a ∧ y = ↑b := by
  grind [WithTop.lt_def']

end LT

namespace WithBot

variable {a b : α}

section LE

variable [LE α] {x y : WithBot α}

@[to_dual]
/-
**WithBot.le_iff_forall** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_iff_forall : x <= y ↔ forall a : α, x = ↑a -> exists b : α, y = ↑b ∧ a 
<= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma le_iff_forall : x ≤ y ↔ ∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b := by
  cases x <;> cases y <;> simp [le_def]

@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_le_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by simp [le_def]

@[to_dual not_top_le_coe]
/-
**WithBot.not_coe_le_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：not_coe_le_bot (a : α) : ¬(a : WithBot α) <= ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := by simp [le_def]

@[to_dual]
/-
**WithBot.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instOrderBot : OrderBot (WithBot α) where bot_le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot (WithBot α) where bot_le := by simp [le_def]

@[to_dual]
/-
**WithBot.instOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instOrderTop [OrderTop α] : OrderTop (WithBot α) where le_top x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderTop [OrderTop α] : OrderTop (WithBot α) where
  le_top x := by cases x <;> simp [le_def]

@[to_dual]
/-
**WithBot.instBoundedOrder** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → [inst : LE α] → [OrderTop α] → BoundedOrder (WithBot α)
参数：WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder [OrderTop α] : BoundedOrder (WithBot α) where

/-- There is a general version `le_bot_iff`, but this lemma does not require a `PartialOrder`. -/
@[to_dual (attr := simp) top_le_iff
/-- There is a general version `top_le_iff`, but this lemma does not require a `PartialOrder`. -/]
/-
**WithBot.le_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {x : WithBot α}, x ≤ ⊥ ↔ x = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem le_bot_iff : ∀ {x : WithBot α}, x ≤ ⊥ ↔ x = ⊥
  | (a : α) => by simp [not_coe_le_bot]
  | ⊥ => by simp

@[to_dual le_coe]
/-
**WithBot.coe_le** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : LE α] {o : Option α}, b ∈ o → (↑a ≤ o ↔
 a ≤ b)
参数：↑a ≤ o ↔ a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe

@[to_dual le_coe_iff]
/-
**WithBot.coe_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b
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
theorem coe_le_iff : a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b := by simp [le_iff_forall]
@[to_dual coe_le_iff]
/-
**WithBot.le_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：le_coe_iff : x <= b ↔ forall a : α, x = ↑a -> a <= b
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_coe_iff : x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b := by simp [le_iff_forall]

@[to_dual]
/-
**WithBot._root_.IsMax.withBot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α) :=
  fun x ↦ by cases x <;> simp; simpa using @h _

@[to_dual (attr := simp) untop_le_iff]
/-
**WithBot.le_unbot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_unbot_iff (hx : x != ⊥) : a <= unbot x hx ↔ a <= x
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_unbot_iff (hx : x ≠ ⊥) : a ≤ unbot x hx ↔ a ≤ x := by lift x to α using hx; simp
@[to_dual (attr := simp) le_untop_iff]
/-
**WithBot.unbot_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbot_le_iff (hx : x != ⊥) : unbot x hx <= a ↔ x <= a
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unbot_le_iff (hx : x ≠ ⊥) : unbot x hx ≤ a ↔ x ≤ a := by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
/-
**WithBot.unbot_le_unbot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbot_le_unbot_iff (hx : x != ⊥) (hy : y != ⊥) : x.unbot hx <= y.unbot hy 
↔ x <= y
参数：hx : x != ⊥；hy : y != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unbot_le_unbot_iff (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x.unbot hx ≤ y.unbot hy ↔ x ≤ y := by simp

@[to_dual]
alias ⟨_, unbot_mono⟩ := unbot_le_unbot_iff

@[to_dual untopD_le_iff]
/-
**WithBot.le_unbotD_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_unbotD_iff (hx : x != ⊥) : b <= x.unbotD a ↔ b <= x
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_unbotD_iff (hx : x ≠ ⊥) : b ≤ x.unbotD a ↔ b ≤ x := by lift x to α using hx; simp
@[to_dual le_untopD_iff]
/-
**WithBot.unbotD_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotD_le_iff (hx : x = ⊥ -> a <= b) : x.unbotD a <= b ↔ x <= b
参数：hx : x = ⊥ -> a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma unbotD_le_iff (hx : x = ⊥ → a ≤ b) : x.unbotD a ≤ b ↔ x ≤ b := by cases x <;> simp [hx]

@[to_dual]
/-
**WithBot.unbotD_mono** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotD_mono (hx : x != ⊥) (h : x <= y) : x.unbotD a <= y.unbotD a
参数：hx : x != ⊥；h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma unbotD_mono (hx : x ≠ ⊥) (h : x ≤ y) : x.unbotD a ≤ y.unbotD a := by
  lift x to α using hx
  cases y <;> simp_all

@[to_dual untopA_le_iff]
/-
**WithBot.le_unbotA_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_unbotA_iff [Nonempty α] (hx : x != ⊥) : a <= x.unbotA ↔ a <= x
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_unbotD_iff`：le_unbotD_iff (hx : x != ⊥) : b <= x.unbotD a ↔ b
 <= x
-/
lemma le_unbotA_iff [Nonempty α] (hx : x ≠ ⊥) : a ≤ x.unbotA ↔ a ≤ x := le_unbotD_iff hx
@[to_dual le_untopA_iff]
/-
**WithBot.unbotA_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotA_le_iff [Nonempty α] (hx : x != ⊥) : x.unbotA <= a ↔ x <= a
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unbotA_le_iff [Nonempty α] (hx : x ≠ ⊥) : x.unbotA ≤ a ↔ x ≤ a := by
  lift x to α using hx; simp

@[to_dual]
/-
**WithBot.unbotA_mono** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotA_mono [Nonempty α] (hy : x != ⊥) (h : x <= y) : x.unbotA <= y.unbotA
参数：hy : x != ⊥；h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.unbotD_mono`：unbotD_mono (hx : x != ⊥) (h : x <= y) : x.unbotD a
 <= y.unbotD a
-/
lemma unbotA_mono [Nonempty α] (hy : x ≠ ⊥) (h : x ≤ y) : x.unbotA ≤ y.unbotA := unbotD_mono hy h

end LE

section LT

variable [LT α] {x y : WithBot α}

@[to_dual]
/-
**WithBot.lt_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_iff_exists : x < y ↔ exists b : α, y = ↑b ∧ forall a : α, x = ↑a -> a <
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma lt_iff_exists : x < y ↔ ∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b := by
  cases x <;> cases y <;> simp [lt_def]

@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_lt_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_lt_coe : (a : WithBot α) < b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_lt_coe : (a : WithBot α) < b ↔ a < b := by simp [lt_def]
@[to_dual (attr := simp) coe_lt_top]
/-
**WithBot.bot_lt_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma bot_lt_coe (a : α) : ⊥ < (a : WithBot α) := by simp [lt_def]
@[to_dual (attr := simp) not_top_lt]
/-
**WithBot.not_lt_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] (a : WithBot α), ¬a < ⊥
参数：a : WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected lemma not_lt_bot (a : WithBot α) : ¬a < ⊥ := by simp [lt_def]

@[to_dual]
/-
**WithBot.lt_iff_exists_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_iff_exists_coe : x < y ↔ exists b : α, y = b ∧ x < b
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma lt_iff_exists_coe : x < y ↔ ∃ b : α, y = b ∧ x < b := by cases y <;> simp

@[to_dual coe_lt_iff]
/-
**WithBot.lt_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_coe_iff : x < b ↔ forall a : α, x = a -> a < b
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
lemma lt_coe_iff : x < b ↔ ∀ a : α, x = a → a < b := by simp [lt_iff_exists]

/-- A version of `bot_lt_iff_ne_bot` for `WithBot` that only requires `LT α`, not
`PartialOrder α`. -/
@[to_dual lt_top_iff_ne_top
/-- A version of `lt_top_iff_ne_top` for `WithTop` that only requires `LT α`, not
`PartialOrder α`. -/]
/-
**WithBot.bot_lt_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] {x : WithBot α}, ⊥ < x ↔ x ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected lemma bot_lt_iff_ne_bot : ⊥ < x ↔ x ≠ ⊥ := by cases x <;> simp

@[to_dual (attr := simp) untop_lt_iff]
/-
**WithBot.lt_unbot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_unbot_iff (hx : x != ⊥) : a < unbot x hx ↔ a < x
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_unbot_iff (hx : x ≠ ⊥) : a < unbot x hx ↔ a < x := by lift x to α using hx; simp
@[to_dual (attr := simp) lt_untop_iff]
/-
**WithBot.unbot_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbot_lt_iff (hx : x != ⊥) : unbot x hx < b ↔ x < b
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unbot_lt_iff (hx : x ≠ ⊥) : unbot x hx < b ↔ x < b := by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
/-
**WithBot.unbot_lt_unbot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbot_lt_unbot_iff (hx hy) : unbot x hx < unbot y hy ↔ x < y
参数：hx hy。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unbot_lt_unbot_iff (hx hy) : unbot x hx < unbot y hy ↔ x < y := by simp

@[to_dual untopD_lt_iff]
/-
**WithBot.lt_unbotD_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_unbotD_iff (hx : x != ⊥) : b < x.unbotD a ↔ b < x
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_unbotD_iff (hx : x ≠ ⊥) : b < x.unbotD a ↔ b < x := by lift x to α using hx; simp
@[to_dual lt_untopD_iff]
/-
**WithBot.unbotD_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotD_lt_iff (hx : x = ⊥ -> a < b) : x.unbotD a < b ↔ x < b
参数：hx : x = ⊥ -> a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma unbotD_lt_iff (hx : x = ⊥ → a < b) : x.unbotD a < b ↔ x < b := by cases x <;> simp [hx]

@[to_dual untopA_lt_iff]
/-
**WithBot.lt_unbotA_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_unbotA_iff [Nonempty α] (hx : x != ⊥) : a < x.unbotA ↔ a < x
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_unbotD_iff`：lt_unbotD_iff (hx : x != ⊥) : b < x.unbotD a ↔ b 
< x
-/
lemma lt_unbotA_iff [Nonempty α] (hx : x ≠ ⊥) : a < x.unbotA ↔ a < x := lt_unbotD_iff hx
@[to_dual lt_untopA_iff]
/-
**WithBot.unbotA_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotA_lt_iff [Nonempty α] (hx : x != ⊥) : x.unbotA < a ↔ x < a
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unbotA_lt_iff [Nonempty α] (hx : x ≠ ⊥) : x.unbotA < a ↔ x < a := by
  lift x to α using hx; simp

end LT

@[to_dual]
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Preorder (WithBot α) where
  lt_iff_le_not_ge x y := by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

section Preorder

variable [Preorder α] [Preorder β] {x y : WithBot α}

@[to_dual]
/-
**WithBot.coe_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_strictMono : StrictMono (fun (a : α) => (a : WithBot α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
theorem coe_strictMono : StrictMono (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_lt_coe.2

@[to_dual]
/-
**WithBot.coe_mono** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_mono : Monotone (fun (a : α) => (a : WithBot α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem coe_mono : Monotone (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_le_coe.2

@[to_dual]
/-
**WithBot.monotone_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：monotone_iff {f : WithBot α -> β} : Monotone f ↔ Monotone (fun a => f a : 
α -> β) ∧ forall x : α, f ⊥ <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `WithBot.coe_mono`：coe_mono : Monotone (fun (a : α) => (a : WithBot α))
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithBot.forall`：∀ {α : Type u_1} {p : WithBot α → Prop}, (∀ (x : WithBot
 α), p x) ↔ p ⊥ ∧ ∀ (x : α), p ↑x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `WithBot.not_coe_le_bot`：not_coe_le_bot (a : α) : ¬(a : WithBot α) <= ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem monotone_iff {f : WithBot α → β} :
    Monotone f ↔ Monotone (fun a ↦ f a : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h ↦ ⟨h.comp WithBot.coe_mono, fun _ ↦ h bot_le⟩, fun h ↦
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[to_dual (attr := simp)]
/-
**WithBot.monotone_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：monotone_map_iff {f : α -> β} : Monotone (WithBot.map f) ↔ Monotone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithBot.monotone_iff`：monotone_iff {f : WithBot α -> β} : Monotone f ↔ M
onotone (fun a => f a : α -> β) ∧ forall x : α, f ⊥ <= f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monotone_map_iff {f : α → β} : Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

@[to_dual]
alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

@[to_dual]
/-
**WithBot.strictMono_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：strictMono_iff {f : WithBot α -> β} : StrictMono f ↔ StrictMono (fun a => 
f a : α -> β) ∧ forall x : α, f ⊥ < f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `WithBot.coe_strictMono`：coe_strictMono : StrictMono (fun (a : α) => (a :
 WithBot α))
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithBot.forall`：∀ {α : Type u_1} {p : WithBot α → Prop}, (∀ (x : WithBot
 α), p x) ↔ p ⊥ ∧ ∀ (x : α), p ↑x
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
theorem strictMono_iff {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (fun a => f a : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[to_dual]
/-
**WithBot.strictAnti_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：strictAnti_iff {f : WithBot α -> β} : StrictAnti f ↔ StrictAnti (fun a => 
f a : α -> β) ∧ forall x : α, f x < f ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.strictMono_iff`：strictMono_iff {f : WithBot α -> β} : StrictMono
 f ↔ StrictMono (fun a => f a : α -> β) ∧ forall x : α, f ⊥ < f x
-/
theorem strictAnti_iff {f : WithBot α → β} :
    StrictAnti f ↔ StrictAnti (fun a ↦ f a : α → β) ∧ ∀ x : α, f x < f ⊥ :=
  strictMono_iff (β := βᵒᵈ)

@[to_dual (attr := simp)]
/-
**WithBot.strictMono_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：strictMono_map_iff {f : α -> β} : StrictMono (WithBot.map f) ↔ StrictMono 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithBot.strictMono_iff`：strictMono_iff {f : WithBot α -> β} : StrictMono
 f ↔ StrictMono (fun a => f a : α -> β) ∧ forall x : α, f ⊥ < f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem strictMono_map_iff {f : α → β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, bot_lt_coe]

@[to_dual]
alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

@[to_dual]
/-
**WithBot.map_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：map_le_iff (f : α -> β) (mono_iff : forall {a b}, f a <= f b ↔ a <= b) : x
.map f <= y.map f ↔ x <= y
参数：f : α -> β；mono_iff : forall {a b}, f a <= f b ↔ a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_le_iff (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    x.map f ≤ y.map f ↔ x ≤ y := by cases x <;> cases y <;> simp [mono_iff]

@[to_dual coe_untopD_le]
/-
**WithBot.le_coe_unbotD** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：le_coe_unbotD (x : WithBot α) (b : α) : x <= x.unbotD b
参数：x : WithBot α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_coe_unbotD (x : WithBot α) (b : α) : x ≤ x.unbotD b := by cases x <;> simp

@[to_dual (attr := simp) coe_top_lt]
/-
**WithBot.lt_coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥ := by cases x <;> simp

@[to_dual eq_top_iff_forall_gt]
/-
**WithBot.eq_bot_iff_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：eq_bot_iff_forall_lt : x = ⊥ ↔ forall b : α, x < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
lemma eq_bot_iff_forall_lt : x = ⊥ ↔ ∀ b : α, x < b := by
  cases x <;> simp; simpa using ⟨_, lt_irrefl _⟩

@[to_dual eq_top_iff_forall_ge]
/-
**WithBot.eq_bot_iff_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：eq_bot_iff_forall_le [NoBotOrder α] : x = ⊥ ↔ forall b : α, x <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.eq_bot_iff_forall_ne`：eq_bot_iff_forall_ne {x : WithBot α} : x =
 ⊥ ↔ forall a : α, ↑a != x
· 使用定理 `not_isBot`：not_isBot [NoBotOrder α] (a : α) : ¬IsBot a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
lemma eq_bot_iff_forall_le [NoBotOrder α] : x = ⊥ ↔ ∀ b : α, x ≤ b := by
  refine ⟨by simp +contextual, fun h ↦ (x.eq_bot_iff_forall_ne).2 fun y => ?_⟩
  rintro rfl
  exact not_isBot y fun z => coe_le_coe.1 (h z)

@[to_dual forall_le_coe_iff_le]
/-
**WithBot.forall_coe_le_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：forall_coe_le_iff_le [NoBotOrder α] : (forall a : α, a <= x -> a <= y) ↔ x
 <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `not_isBot`：not_isBot [NoBotOrder α] (a : α) : ¬IsBot a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
-/
lemma forall_coe_le_iff_le [NoBotOrder α] : (∀ a : α, a ≤ x → a ≤ y) ↔ x ≤ y := by
  obtain _ | a := x
  · simpa [WithBot.none_eq_bot, eq_bot_iff_forall_le] using! fun a ha ↦ (not_isBot _ ha).elim
  · exact ⟨fun h ↦ h _ le_rfl, fun hay b ↦ hay.trans'⟩

@[to_dual forall_coe_le_iff_le]
/-
**WithBot.forall_le_coe_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：forall_le_coe_iff_le [NoBotOrder α] : (forall a : α, y <= a -> x <= a) ↔ x
 <= y
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma forall_le_coe_iff_le [NoBotOrder α] : (∀ a : α, y ≤ a → x ≤ a) ↔ x ≤ y := by
  obtain _ | y := y
  · simp [WithBot.none_eq_bot, eq_bot_iff_forall_le]
  · exact ⟨fun h ↦ h _ le_rfl, fun hmn a ham ↦ hmn.trans ham⟩

@[to_dual (attr := simp) forall_lt_coe]
/-
**WithBot.forall_coe_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：forall_coe_lt {p : WithBot α -> Prop} : (forall x, (a : WithBot α) < x -> 
p x) ↔ forall b, a < b -> p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_coe_lt {p : WithBot α → Prop} :
    (∀ x, (a : WithBot α) < x → p x) ↔ ∀ b, a < b → p b := by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_lt_coe]
/-
**WithBot.exists_coe_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：exists_coe_lt {p : WithBot α -> Prop} : (exists x, (a : WithBot α) < x ∧ p
 x) ↔ exists b, a < b ∧ p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_coe_lt {p : WithBot α → Prop} :
    (∃ x, (a : WithBot α) < x ∧ p x) ↔ ∃ b, a < b ∧ p b := by
  simp [WithBot.exists]

@[to_dual (attr := simp) forall_le_coe]
/-
**WithBot.forall_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：forall_coe_le {p : WithBot α -> Prop} : (forall x, (a : WithBot α) <= x ->
 p x) ↔ forall b, a <= b -> p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_coe_le {p : WithBot α → Prop} :
    (∀ x, (a : WithBot α) ≤ x → p x) ↔ ∀ b, a ≤ b → p b := by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_le_coe]
/-
**WithBot.exists_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：exists_coe_le {p : WithBot α -> Prop} : (exists x, (a : WithBot α) <= x ∧ 
p x) ↔ exists b, a <= b ∧ p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_coe_le {p : WithBot α → Prop} :
    (∃ x, (a : WithBot α) ≤ x ∧ p x) ↔ ∃ b, a ≤ b ∧ p b := by
  simp [WithBot.exists]

end Preorder

@[to_dual]
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] : PartialOrder (WithBot α) where
  le_antisymm x y := by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

section PartialOrder
variable [PartialOrder α] {x y : WithBot α} {a b : α}

@[to_dual untopD_le]
/-
**WithBot.le_unbotD** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_unbotD (hy : b <= y) : b <= y.unbotD a
参数：hy : b <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithBot.le_unbotD_iff`：le_unbotD_iff (hx : x != ⊥) : b <= x.unbotD a ↔ b
 <= x
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma le_unbotD (hy : b ≤ y) : b ≤ y.unbotD a := by
  rwa [le_unbotD_iff]
  exact ne_bot_of_le_ne_bot (by simp) hy

@[to_dual untopA_le]
/-
**WithBot.le_unbotA** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_unbotA [Nonempty α] (hy : b <= y) : b <= y.unbotA
参数：hy : b <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_unbotD`：le_unbotD (hy : b <= y) : b <= y.unbotD a
-/
lemma le_unbotA [Nonempty α] (hy : b ≤ y) : b ≤ y.unbotA := le_unbotD hy

@[to_dual eq_bot_iff_forall_le]
/-
**WithBot.eq_top_iff_forall_ge** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：eq_top_iff_forall_ge [Nonempty α] [NoTopOrder α] {x : WithBot (WithTop α)}
 : x = ⊤ ↔ forall a : α, a <= x
参数：WithTop α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma eq_top_iff_forall_ge [Nonempty α] [NoTopOrder α] {x : WithBot (WithTop α)} :
    x = ⊤ ↔ ∀ a : α, a ≤ x := by
  refine ⟨by simp_all, fun H ↦ ?_⟩
  induction x
  · simp at H
  · simpa [WithTop.eq_top_iff_forall_ge] using H

variable [NoBotOrder α]

@[to_dual eq_of_forall_le_coe_iff]
/-
**WithBot.eq_of_forall_coe_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：eq_of_forall_coe_le_iff (h : forall a : α, a <= x ↔ a <= y) : x = y
参数：h : forall a : α, a <= x ↔ a <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.forall_coe_le_iff_le`：forall_coe_le_iff_le [NoBotOrder α] : (for
all a : α, a <= x -> a <= y) ↔ x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma eq_of_forall_coe_le_iff (h : ∀ a : α, a ≤ x ↔ a ≤ y) : x = y :=
  le_antisymm (forall_coe_le_iff_le.mp fun a ↦ (h a).1) (forall_coe_le_iff_le.mp fun a ↦ (h a).2)

@[to_dual eq_of_forall_coe_le_iff]
/-
**WithBot.eq_of_forall_le_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：eq_of_forall_le_coe_iff (h : forall a : α, x <= a ↔ y <= a) : x = y
参数：h : forall a : α, x <= a ↔ y <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.forall_le_coe_iff_le`：forall_le_coe_iff_le [NoBotOrder α] : (for
all a : α, y <= a -> x <= a) ↔ x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma eq_of_forall_le_coe_iff (h : ∀ a : α, x ≤ a ↔ y ≤ a) : x = y :=
  le_antisymm (forall_le_coe_iff_le.mp fun a ↦ (h a).2) (forall_le_coe_iff_le.mp fun a ↦ (h a).1)

end PartialOrder

/-
**WithBot.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithBot α) where sup -
- note this is `Option.merge`, but with the right defeq when unfolding | ⊥, ⊥ =>
 ⊥ | (a : α), ⊥ => a | ⊥, (b : α) => b | (a : α), (b : α) => ↑(a ⊔ b) le_sup_lef
t x y
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithBot α) where
  sup
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊥, ⊥ => ⊥
    | (a : α), ⊥ => a
    | ⊥, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual existing]
/-
**WithBot._root_.WithTop.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithTop α) where
  inf
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊤, ⊤ => ⊤
    | (a : α), ⊤ => a
    | ⊤, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊓ b)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf
/-
**WithBot.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) where inf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

@[to_dual existing]
/-
**WithBot._root_.WithTop.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithTop α) where
  sup := .map₂ (· ⊔ ·)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = (a : Wi
thBot α) ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup [SemilatticeSup α] (a b : α) :
    ((a ⊔ b : α) : WithBot α) = (a : WithBot α) ⊔ b := rfl

@[to_dual (attr := simp, norm_cast)]
/-
**WithBot.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = (a : Wi
thBot α) ⊓ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf [SemilatticeInf α] (a b : α) :
    ((a ⊓ b : α) : WithBot α) = (a : WithBot α) ⊓ b := rfl
/-
**WithBot.lattice** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → [Lattice α] → Lattice (WithBot α)
参数：WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice [Lattice α] : Lattice (WithBot α) where

@[to_dual existing]
/-
**WithBot._root_.WithTop.lattice** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.lattice [Lattice α] : Lattice (WithTop α) where
/-
**WithBot.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：distribLattice [DistribLattice α] : DistribLattice (WithBot α) where le_su
p_inf x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribLattice [DistribLattice α] : DistribLattice (WithBot α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual existing]
/-
**WithBot._root_.WithTop.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.distribLattice [DistribLattice α] : DistribLattice (WithTop α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← WithTop.coe_inf, ← WithTop.coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual]
/-
**WithBot.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：decidableEq [DecidableEq α] : DecidableEq (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEq [DecidableEq α] : DecidableEq (WithBot α) :=
  inferInstanceAs <| DecidableEq (Option α)

@[to_dual]
/-
**WithBot.decidableLE** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → [inst : LE α] → [DecidableLE α] → DecidableLE (WithBot α)
参数：WithBot α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
instance decidableLE [LE α] [DecidableLE α] : DecidableLE (WithBot α)
  | ⊥, _ => isTrue <| by simp
  | (a : α), ⊥ => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

@[to_dual]
/-
**WithBot.decidableLT** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → [inst : LT α] → [DecidableLT α] → DecidableLT (WithBot α)
参数：WithBot α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
instance decidableLT [LT α] [DecidableLT α] : DecidableLT (WithBot α)
  | _, ⊥ => isFalse <| by simp
  | ⊥, (a : α) => isTrue <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe
/-
**WithBot.total_le** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：total_le [LE α] [@Std.Total α (· <= ·)] : @Std.Total (WithBot α) (· <= ·) 
where total x y
参数：· <= ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
instance total_le [LE α] [@Std.Total α (· ≤ ·)] : @Std.Total (WithBot α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..
/-
**WithBot._root_.WithTop.total_le** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.total_le [LE α] [@Std.Total α (· ≤ ·)] :
    @Std.Total (WithTop α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..
/-
**WithBot.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：linearOrder [LinearOrder α] : LinearOrder (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder [LinearOrder α] : LinearOrder (WithBot α) := Lattice.toLinearOrder _

@[to_dual existing]
/-
**WithBot._root_.WithTop.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.linearOrder [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

@[to_dual]
/-
**WithBot.instWellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithBot α) whe
re wf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
-/
instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithBot α) where
  wf := .intro fun
  | ⊥ => ⟨_, by simp⟩
  | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih ↦ .intro _ fun
    | ⊥, _ => ⟨_, by simp⟩
    | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

@[to_dual]
/-
**WithBot.instWellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) whe
re wf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `wellFounded_gt`：∀ {α : Type u} [inst : LT α] [WellFoundedGT α], WellFoun
ded fun x1 x2 => x2 < x1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) where
  wf := have acc_some (a : α) : @Acc (WithBot α) (· > ·) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih ↦ ⟨_, by simpa [WithBot.forall]⟩
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => ⟨_, by simpa [WithBot.forall]⟩
/-
**WithBot.denselyOrdered_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：denselyOrdered_iff [LT α] [NoMinOrder α] : DenselyOrdered (WithBot α) ↔ De
nselyOrdered α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `DenselyOrdered.dense`：∀ {α : Type u_5} {inst : LT α} [self : DenselyOrde
red α] (a₁ a₂ : α), a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
-/
lemma denselyOrdered_iff [LT α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithBot.coe_lt_coe.mpr hab)
    induction c with
    | bot => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithBot.exists, WithBot.forall, exists_lt] using DenselyOrdered.dense

@[to_dual existing]
/-
**WithBot._root_.WithTop.denselyOrdered_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.WithTop.denselyOrdered_iff [LT α] [NoMaxOrder α] :
    DenselyOrdered (WithTop α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithTop.coe_lt_coe.mpr hab)
    induction c with
    | top => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithTop.exists, WithTop.forall, exists_gt] using DenselyOrdered.dense

@[to_dual]
/-
**WithBot.denselyOrdered** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (
WithBot α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.denselyOrdered_iff`：denselyOrdered_iff [LT α] [NoMinOrder α] : D
enselyOrdered (WithBot α) ↔ DenselyOrdered α
-/
instance denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) :=
  denselyOrdered_iff.mpr inferInstance
/-
**WithBot.trichotomous.lt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot.trichotomous`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Std.Trichotomous fun x1 x2 => x1 < x
2], Std.Trichotomous fun x1 x2 => x1 < x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.trichotomous_of_rel_or_eq_or_rel_swap`：∀ {α : Sort u_1} {r : α → α →
 Prop}, (∀ {a b : α}, r a b ∨ a = b ∨ r b a) → Std.Trichotomous r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
instance trichotomous.lt [Preorder α] [@Std.Trichotomous α (· < ·)] :
    @Std.Trichotomous (WithBot α) (· < ·) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} ↦ by
    cases x <;> cases y <;> simp [trichotomous]
/-
**WithBot._root_.WithTop.trichotomous.lt** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.trichotomous.lt [Preorder α] [@Std.Trichotomous α (· < ·)] :
    @Std.Trichotomous (WithTop α) (· < ·) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} ↦ by
    cases x <;> cases y <;> simp [trichotomous]

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedLT`, remove this.
/-
**WithBot.IsWellOrder.lt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot.IsWellOrder`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [IsWellOrder α fun x1 x2 => x1 < x2],
 IsWellOrder (WithBot α) fun x1 x2 => x1 < x2
参数：WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `WithBot.trichotomous.lt`：∀ {α : Type u_1} [inst : Preorder α] [Std.Trich
otomous fun x1 x2 => x1 < x2], Std.Trichotomous fun x1 x2 => x1 < x2
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
-/
instance IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
  IsWellOrder (WithBot α) (· < ·) where

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedLT`, remove this.
/-
**WithBot._root_.WithTop.IsWellOrder.lt** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
  IsWellOrder (WithTop α) (· < ·) where
/-
**WithBot.trichotomous.gt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot.trichotomous`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Std.Trichotomous fun x1 x2 => x1 > x
2], Std.Trichotomous fun x1 x2 => x1 > x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instTrichotomousSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [
Std.Trichotomous r], Std.Trichotomous (Function.swap r)
· 使用定理 `WithBot.trichotomous.lt`：∀ {α : Type u_1} [inst : Preorder α] [Std.Trich
otomous fun x1 x2 => x1 < x2], Std.Trichotomous fun x1 x2 => x1 < x2
-/
instance trichotomous.gt [Preorder α] [@Std.Trichotomous α (· > ·)] :
    @Std.Trichotomous (WithBot α) (· > ·) :=
  have : @Std.Trichotomous α (· < ·) := inferInstanceAs <| Std.Trichotomous <| Function.swap _
  inferInstance
/-
**WithBot._root_.WithTop.trichotomous.gt** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.trichotomous.gt [Preorder α] [@Std.Trichotomous α (· > ·)] :
    @Std.Trichotomous (WithTop α) (· > ·) :=
  have : @Std.Trichotomous α (· < ·) := inferInstanceAs <| Std.Trichotomous <| Function.swap _
  inferInstance

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedGT`, remove this.
/-
**WithBot.IsWellOrder.gt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot.IsWellOrder`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [IsWellOrder α fun x1 x2 => x1 > x2],
 IsWellOrder (WithBot α) fun x1 x2 => x1 > x2
参数：WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `WithBot.trichotomous.gt`：∀ {α : Type u_1} [inst : Preorder α] [Std.Trich
otomous fun x1 x2 => x1 > x2], Std.Trichotomous fun x1 x2 => x1 > x2
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
-/
instance IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) where

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedGT`, remove this.
/-
**WithBot._root_.WithTop.IsWellOrder.gt** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.WithTop.IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] :
    IsWellOrder (WithTop α) (· > ·) where

section LinearOrder
variable [LinearOrder α] {x y : WithBot α}

@[to_dual]
/-
**WithBot.coe_min** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_min (a b : α) : ↑(min a b) = min (a : WithBot α) b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_min (a b : α) : ↑(min a b) = min (a : WithBot α) b := rfl
@[to_dual]
/-
**WithBot.coe_max** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_max (a b : α) : ↑(max a b) = max (a : WithBot α) b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_max (a b : α) : ↑(max a b) = max (a : WithBot α) b := rfl

variable [DenselyOrdered α] [NoMinOrder α]

@[to_dual ge_of_forall_gt_iff_ge]
/-
**WithBot.le_of_forall_lt_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_of_forall_lt_iff_le : (forall z : α, x < z -> y <= z) ↔ y <= x
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma le_of_forall_lt_iff_le : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x := by
  cases x <;> cases y <;> simp [exists_lt, forall_gt_imp_ge_iff_le_of_dense]

@[to_dual le_of_forall_lt_iff_le]
/-
**WithBot.ge_of_forall_gt_iff_ge** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ge_of_forall_gt_iff_ge : (forall z : α, z < x -> z <= y) ↔ x <= y
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ge_of_forall_gt_iff_ge : (∀ z : α, z < x → z ≤ y) ↔ x ≤ y := by
  cases x <;> cases y <;> simp [exists_lt, forall_lt_imp_le_iff_le_of_dense]

end LinearOrder

@[to_dual lt_iff_exists_coe_btwn']
/-
**WithBot.lt_iff_exists_coe_btwn** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b
 : WithBot α} : a < b ↔ exists x : α, a < x ∧ x < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.lt_iff_exists_coe`：lt_iff_exists_coe : x < y ↔ exists b : α, y =
 b ∧ x < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < x ∧ x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

@[to_dual lt_iff_exists_coe_btwn]
/-
**WithBot.lt_iff_exists_coe_btwn'** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：lt_iff_exists_coe_btwn' [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a 
b : WithBot α} : a < b ↔ exists x : α, x < b ∧ a < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.lt_iff_exists_coe_btwn`：lt_iff_exists_coe_btwn [Preorder α] [Den
selyOrdered α] [NoMinOrder α] {a b : WithBot α} : a < b ↔ exists x : α, a < x ∧ 
x < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iff_exists_coe_btwn' [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, x < b ∧ a < x := by
  rw [lt_iff_exists_coe_btwn]; simp_rw [and_comm]

@[to_dual]
/-
**WithBot.noTopOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：noTopOrder [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) whe
re exists_not_le
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `NoTopOrder.exists_not_le`：∀ {α : Type u_3} {inst : LE α} [self : NoTopOr
der α] (a : α), ∃ b, ¬b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance noTopOrder [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) where
  exists_not_le := fun
    | ⊥ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_le a; ⟨b, mod_cast hba⟩

@[to_dual]
/-
**WithBot.noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：noMaxOrder [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) whe
re exists_gt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance noMaxOrder [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) where
  exists_gt := fun
    | ⊥ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_gt a; ⟨b, mod_cast hba⟩

variable {a b : α}

/-! ### `(WithBot α)ᵒᵈ ≃ WithTop αᵒᵈ`, `(WithTop α)ᵒᵈ ≃ WithBot αᵒᵈ` -/

open Function

/-- `WithBot.toDual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithBot.toDualTopEquiv` for the related order-iso. -/
@[to_dual
/-- `WithTop.toDual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithTop.toDualBotEquiv` for the related order-iso. -/]
/-
**WithBot.toDual** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → WithBot α ≃ WithTop αᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
protected def toDual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _

/-- `WithBot.ofDual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithBot.ofDualTopEquiv` for the related order-iso.
-/
@[to_dual
/-- `WithTop.ofDual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithTop.toDualBotEquiv` for the related order-iso. -/]
/-
**WithBot.ofDual** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u_1} → WithBot αᵒᵈ ≃ WithTop α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
protected def ofDual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _

@[to_dual (attr := simp)]
/-
**WithBot.toDual_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：toDual_symm : WithBot.toDual.symm = WithTop.ofDual (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toDual_symm : WithBot.toDual.symm = WithTop.ofDual (α := α) := rfl

@[to_dual (attr := simp)]
/-
**WithBot.ofDual_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：ofDual_symm : WithBot.ofDual.symm = WithTop.toDual (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofDual_symm : WithBot.ofDual.symm = WithTop.toDual (α := α) := rfl

@[to_dual (attr := simp)]
/-
**WithBot.toDual_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：toDual_bot : WithBot.toDual (⊥ : WithBot α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ := rfl

@[to_dual (attr := simp)]
/-
**WithBot.ofDual_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：ofDual_bot : WithBot.ofDual (⊥ : WithBot αᵒᵈ) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_bot : WithBot.ofDual (⊥ : WithBot αᵒᵈ) = ⊤ := rfl

open OrderDual

@[to_dual (attr := simp)]
/-
**WithBot.toDual_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a := rfl

@[to_dual (attr := simp)]
/-
**WithBot.ofDual_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a
参数：a : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a := rfl

@[to_dual]
/-
**WithBot.map_toDual** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_toDual (f : αᵒᵈ -> βᵒᵈ) (a : WithBot α) : map f (WithBot.toDual a) = a
.map (toDual ∘ f)
参数：f : αᵒᵈ -> βᵒᵈ；a : WithBot α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (toDual ∘ f) :=
  rfl

@[to_dual]
/-
**WithBot.map_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_ofDual (f : α -> β) (a : WithBot αᵒᵈ) : map f (WithBot.ofDual a) = a.m
ap (ofDual ∘ f)
参数：f : α -> β；a : WithBot αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_ofDual (f : α → β) (a : WithBot αᵒᵈ) :
    map f (WithBot.ofDual a) = a.map (ofDual ∘ f) :=
  rfl

@[to_dual]
/-
**WithBot.toDual_map** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：toDual_map (f : α -> β) (a : WithBot α) : WithBot.toDual (map f a) = WithT
op.map (toDual ∘ f ∘ ofDual) (WithBot.toDual a)
参数：f : α -> β；a : WithBot α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (map f a) = WithTop.map (toDual ∘ f ∘ ofDual) (WithBot.toDual a) :=
  rfl

@[to_dual]
/-
**WithBot.ofDual_map** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：ofDual_map (f : αᵒᵈ -> βᵒᵈ) (a : WithBot αᵒᵈ) : WithBot.ofDual (map f a) =
 WithTop.map (ofDual ∘ f ∘ toDual) (WithBot.ofDual a)
参数：f : αᵒᵈ -> βᵒᵈ；a : WithBot αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (map f a) = WithTop.map (ofDual ∘ f ∘ toDual) (WithBot.ofDual a) :=
  rfl

section LE
variable [LE α]

@[to_dual le_toDual_iff]
/-
**WithBot.toDual_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：toDual_le_iff {x : WithBot α} {y : WithTop αᵒᵈ} : x.toDual <= y ↔ WithTop.
ofDual y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toDual_le_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual ≤ y ↔ WithTop.ofDual y ≤ x := by cases x <;> cases y <;> simp [toDual_le]

@[to_dual toDual_le_iff]
/-
**WithBot.le_toDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} : x <= WithBot.toDual y ↔ 
y <= WithTop.ofDual x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma le_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x ≤ WithBot.toDual y ↔ y ≤ WithTop.ofDual x := by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]
/-
**WithBot.toDual_le_toDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：toDual_le_toDual_iff {x y : WithBot α} : x.toDual <= y.toDual ↔ y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toDual_le_toDual_iff {x y : WithBot α} :
    x.toDual ≤ y.toDual ↔ y ≤ x := by cases x <;> cases y <;> simp

@[to_dual le_ofDual_iff]
/-
**WithBot.ofDual_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ofDual_le_iff {x : WithBot αᵒᵈ} {y : WithTop α} : WithBot.ofDual x <= y ↔ 
y.toDual <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofDual_le_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x ≤ y ↔ y.toDual ≤ x := by cases x <;> cases y <;> simp [toDual_le]

@[to_dual ofDual_le_iff]
/-
**WithBot.le_ofDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：le_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} : x <= WithBot.ofDual y ↔ 
y <= x.toDual
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma le_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x ≤ WithBot.ofDual y ↔ y ≤ x.toDual := by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]
/-
**WithBot.ofDual_le_ofDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ofDual_le_ofDual_iff {x y : WithBot αᵒᵈ} : WithBot.ofDual x <= WithBot.ofD
ual y ↔ y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofDual_le_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x ≤ WithBot.ofDual y ↔ y ≤ x := by cases x <;> cases y <;> simp_all

end LE

section LT
variable [LT α]

@[to_dual lt_toDual_iff]
/-
**WithBot.toDual_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：toDual_lt_iff {x : WithBot α} {y : WithTop αᵒᵈ} : x.toDual < y ↔ WithTop.o
fDual y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toDual_lt_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual < y ↔ WithTop.ofDual y < x := by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual toDual_lt_iff]
/-
**WithBot.lt_toDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} : x < y.toDual ↔ y < WithT
op.ofDual x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma lt_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x < y.toDual ↔ y < WithTop.ofDual x := by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]
/-
**WithBot.toDual_lt_toDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：toDual_lt_toDual_iff {x y : WithBot α} : x.toDual < y.toDual ↔ y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toDual_lt_toDual_iff {x y : WithBot α} :
    x.toDual < y.toDual ↔ y < x := by cases x <;> cases y <;> simp

@[to_dual lt_ofDual_iff]
/-
**WithBot.ofDual_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ofDual_lt_iff {x : WithBot αᵒᵈ} {y : WithTop α} : WithBot.ofDual x < y ↔ y
.toDual < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofDual_lt_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x < y ↔ y.toDual < x := by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual ofDual_lt_iff]
/-
**WithBot.lt_ofDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：lt_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} : x < WithBot.ofDual y ↔ y
 < x.toDual
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma lt_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x < WithBot.ofDual y ↔ y < x.toDual := by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]
/-
**WithBot.ofDual_lt_ofDual_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ofDual_lt_ofDual_iff {x y : WithBot αᵒᵈ} : WithBot.ofDual x < WithBot.ofDu
al y ↔ y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofDual_lt_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x < WithBot.ofDual y ↔ y < x := by cases x <;> cases y <;> simp

end LT

end WithBot

