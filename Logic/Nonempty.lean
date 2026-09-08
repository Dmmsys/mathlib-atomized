/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Init
/-!
# Nonempty types

This file proves a few extra facts about `Nonempty`, which is defined in core Lean.

## Main declarations

* `Nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` explicitly.
* `Classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` as an
  instance.
-/

@[expose] public section

section
variable {α β : Sort*}

@[simp]
/-
**Nonempty.forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nonempty.forall {α} {p : Nonempty α -> Prop} : (forall h : Nonempty α, p h
) ↔ forall a, p ⟨a⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.forall {α} {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h _ ↦ h _) fun h ⟨a⟩ ↦ h a

@[simp]
/-
**Nonempty.exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nonempty.exists {α} {p : Nonempty α -> Prop} : (exists h : Nonempty α, p h
) ↔ exists a, p ⟨a⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.exists {α} {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ ↦ ⟨a, h⟩) fun ⟨a, h⟩ ↦ ⟨⟨a⟩, h⟩

-- Note: we set low priority here, to ensure it is not applied before `exists_prop`
-- and `exists_const`.
@[simp low]
/-
**exists_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_const_iff {α : Sort*} {P : Prop} : (exists _ : α, P) ↔ Nonempty α ∧
 P
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_const_iff {α : Sort*} {P : Prop} : (∃ _ : α, P) ↔ Nonempty α ∧ P :=
  Iff.intro (fun ⟨a, h⟩ ↦ ⟨⟨a⟩, h⟩) fun ⟨⟨a⟩, h⟩ ↦ ⟨a, h⟩
/-
**exists_true_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_true_iff_nonempty {α : Sort*} : (exists _ : α, True) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem exists_true_iff_nonempty {α : Sort*} : (∃ _ : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨a, trivial⟩
/-
**Nonempty.imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nonempty.imp {α} {p : Prop} : (Nonempty α -> p) ↔ (α -> p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.forall`：Nonempty.forall {α} {p : Nonempty α -> Prop} : (forall 
h : Nonempty α, p h) ↔ forall a, p ⟨a⟩
-/
theorem Nonempty.imp {α} {p : Prop} : (Nonempty α → p) ↔ (α → p) :=
  Nonempty.forall
/-
**not_nonempty_iff_imp_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_nonempty_iff_imp_false {α : Sort*} : ¬Nonempty α ↔ α -> False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.imp`：Nonempty.imp {α} {p : Prop} : (Nonempty α -> p) ↔ (α -> p)
-/
theorem not_nonempty_iff_imp_false {α : Sort*} : ¬Nonempty α ↔ α → False :=
  Nonempty.imp

@[simp]
/-
**nonempty_psigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_psigma {α} {β : α -> Sort*} : Nonempty (PSigma β) ↔ exists a : α,
 Nonempty (β a)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_psigma {α} {β : α → Sort*} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ ↦ ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ ↦ ⟨⟨a, c⟩⟩

@[simp]
/-
**nonempty_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subtype p) ↔ exists a : α
, p a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_subtype {α} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ ↦ ⟨a, h⟩) fun ⟨a, h⟩ ↦ ⟨⟨a, h⟩⟩

@[simp]
/-
**nonempty_pprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ ↦ ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ ↦ ⟨⟨a, b⟩⟩

@[simp]
/-
**nonempty_psum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_psum {α β} : Nonempty (α oplus' β) ↔ Nonempty α ∨ Nonempty β
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_psum {α β} : Nonempty (α ⊕' β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ ↦
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h ↦
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]
/-
**nonempty_plift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨⟨a⟩⟩

/-- Using `Classical.choice`, lifts a (`Prop`-valued) `Nonempty` instance to a (`Type`-valued)
`Inhabited` instance. `Classical.inhabited_of_nonempty` already exists, in `Init/Classical.lean`,
but the assumption is not a type class argument, which makes it unsuitable for some applications. -/
@[instance_reducible]
/-
**Classical.inhabited_of_nonempty'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Using `Classical.choice`, lifts a (`Prop`-valued) `Nonempty` instance to a (`Typ
e`-valued)
`Inhabited` instance. `Classical.inhabited_of_nonempty` already exists, in `Init
/Classical.lean`,
but the assumption is not a type class argument, which makes it unsuitable for s
ome applications.
-/
noncomputable def Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩

/-- Using `Classical.choice`, extracts a term from a `Nonempty` type. -/
/-
**Nonempty.some** 是 Mathlib 中的一个定义，位于命名空间 `Nonempty`。
形式化陈述：{α : Sort u_3} → Nonempty α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Using `Classical.choice`, extracts a term from a `Nonempty` type.
-/
protected noncomputable abbrev Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h

/-- Using `Classical.choice`, extracts a term from a `Nonempty` type. -/
/-
**Classical.arbitrary** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：(α : Sort u_3) → [h : Nonempty α] → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Using `Classical.choice`, extracts a term from a `Nonempty` type.
-/
protected noncomputable abbrev Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h

/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
`Nonempty` cannot be a `functor`, because `Functor` is restricted to `Type`. -/
/-
**Nonempty.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β | ⟨h⟩ => ⟨f h⟩ 
 protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> γ) : Nonempty α 
-> Nonempty β -> Nonempty γ | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩  protected theorem Nonempty.co
ngr {α β} (f : α -> β) (g : β -> α) : Nonempty α ↔ Nonempty β
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
`Nonempty` cannot be a `functor`, because `Functor` is restricted to `Type`.
-/
theorem Nonempty.map {α β} (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩
/-
**Nonempty.map2** 是 Mathlib 中的一个定理，位于命名空间 `Nonempty`。
形式化陈述：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β → γ), Nonempty α
 → Nonempty β → Nonempty γ
参数：f : α → β → γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Nonempty.map2 {α β γ : Sort*} (f : α → β → γ) :
    Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩
/-
**Nonempty.congr** 是 Mathlib 中的一个定理，位于命名空间 `Nonempty`。
形式化陈述：∀ {α : Sort u_3} {β : Sort u_4} (f : α → β) (g : β → α), Nonempty α ↔ None
mpty β
参数：f : α → β；g : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
protected theorem Nonempty.congr {α β} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩
/-
**Nonempty.elim_to_inhabited** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nonempty.elim_to_inhabited {α : Sort*} [h : Nonempty α] {p : Prop} (f : In
habited α -> p) : p
参数：f : Inhabited α -> p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem Nonempty.elim_to_inhabited {α : Sort*} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) :
    p :=
  h.elim <| f ∘ Inhabited.mk
/-
**Classical.nonempty_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Classical.nonempty_pi {ι} {α : ι -> Sort*} : Nonempty (forall i, α i) ↔ fo
rall i, Nonempty (α i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
-/
theorem Classical.nonempty_pi {ι} {α : ι → Sort*} : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a ↦ ⟨f a⟩, @Pi.instNonempty _ _⟩
/-
**subsingleton_of_not_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_of_not_nonempty {α : Sort*} (h : ¬Nonempty α) : Subsingleton 
α
参数：h : ¬Nonempty α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff_imp_false`：not_nonempty_iff_imp_false {α : Sort*} : ¬No
nempty α ↔ α -> False
-/
theorem subsingleton_of_not_nonempty {α : Sort*} (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x ↦ False.elim <| not_nonempty_iff_imp_false.mp h x⟩
/-
**Function.Surjective.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.nonempty [h : Nonempty β] {f : α -> β} (hf : Function.
Surjective f) : Nonempty α
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.Surjective.nonempty [h : Nonempty β] {f : α → β} (hf : Function.Surjective f) :
    Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, _⟩ := hf y
  ⟨x⟩

end

section
variable {α β : Type*} {γ : α → Type*}

@[simp]
/-
**nonempty_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_sigma : Nonempty (Σ a : α, γ a) ↔ exists a : α, Nonempty (γ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_sigma : Nonempty (Σ a : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ ↦ ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ ↦ ⟨⟨a, c⟩⟩

@[simp]
/-
**nonempty_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_sum : Nonempty (α oplus β) ↔ Nonempty α ∨ Nonempty β
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_sum : Nonempty (α ⊕ β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ ↦
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h ↦
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]
/-
**nonempty_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ ↦ ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ ↦ ⟨⟨a, b⟩⟩

@[simp]
/-
**nonempty_ulift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨⟨a⟩⟩

end

