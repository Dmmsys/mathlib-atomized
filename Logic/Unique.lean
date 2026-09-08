/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Tactic.Inhabit

/-!
# Types with a unique term

In this file we define a typeclass `Unique`,
which expresses that a type has a unique term.
In other words, a type that is `Inhabited` and a `Subsingleton`.

## Main declaration

* `Unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `Unique.mk'`: an inhabited subsingleton type is `Unique`. This cannot be an instance because it
  would lead to loops in typeclass inference.

* `Function.Surjective.unique`: if the domain of a surjective function is `Unique`, then its
  codomain is `Unique` as well.

* `Function.Injective.subsingleton`: if the codomain of an injective function is `Subsingleton`,
  then its domain is `Subsingleton` as well.

* `Function.Injective.unique`: if the codomain of an injective function is `Subsingleton` and its
  domain is `Inhabited`, then its domain is `Unique`.

## Implementation details

The typeclass `Unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/

@[expose] public section

universe u v w

-- Don't generate injectivity lemmas, which the `simpNF` linter will complain about.
set_option genInjectivity false in
/-- `Unique α` expresses that `α` is a type with a unique term `default`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
@[ext]
/-
**Unique** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u → Sort (max 1 u)
参数：max 1 u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Unique α` expresses that `α` is a type with a unique term `default`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term.
-/
structure Unique (α : Sort u) extends Inhabited α where
  /-- In a `Unique` type, every term is equal to the default element (from `Inhabited`). -/
  uniq : ∀ a : α, a = default

attribute [class] Unique
/-
**unique_iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_iff_existsUnique (α : Sort u) : Nonempty (Unique α) ↔ exists! _ : α
, True
参数：α : Sort u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
theorem unique_iff_existsUnique (α : Sort u) : Nonempty (Unique α) ↔ ∃! _ : α, True :=
  ⟨fun ⟨u⟩ ↦ ⟨u.default, trivial, fun a _ ↦ u.uniq a⟩,
   fun ⟨a, _, h⟩ ↦ ⟨⟨⟨a⟩, fun _ ↦ h _ trivial⟩⟩⟩
/-
**unique_subtype_iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_subtype_iff_existsUnique {α} (p : α -> Prop) : Nonempty (Unique (Su
btype p)) ↔ exists! a, p a
参数：p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
theorem unique_subtype_iff_existsUnique {α} (p : α → Prop) :
    Nonempty (Unique (Subtype p)) ↔ ∃! a, p a :=
  ⟨fun ⟨u⟩ ↦ ⟨u.default.1, u.default.2, fun a h ↦ congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
   fun ⟨a, ha, he⟩ ↦ ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ ↦ by
      congr
      exact he b hb⟩⟩⟩

/-- Given an explicit `a : α` with `Subsingleton α`, we can construct
a `Unique α` instance. This is a def because the typeclass search cannot
arbitrarily invent the `a : α` term. Nevertheless, these instances are all
equivalent by `Unique.Subsingleton.unique`.

See note [reducible non-instances]. -/
/-
**uniqueOfSubsingleton** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：uniqueOfSubsingleton {α : Sort*} [Subsingleton α] (a : α) : Unique α where
 default
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
Given an explicit `a : α` with `Subsingleton α`, we can construct
a `Unique α` instance. This is a def because the typeclass search cannot
arbitrarily invent the `a : α` term. Nevertheless, these instances are all
equivalent by `Unique.Subsingleton.unique`.

See note [reducible non-instances].
-/
abbrev uniqueOfSubsingleton {α : Sort*} [Subsingleton α] (a : α) : Unique α where
  default := a
  uniq _ := Subsingleton.elim _ _
/-
**PUnit.instUnique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PUnit.instUnique : Unique PUnit.{u} where default
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PUnit.ext`：∀ (a b : PUnit.{u_1}), a = b
-/
instance PUnit.instUnique : Unique PUnit.{u} where
  default := PUnit.unit
  uniq x := ext x _

@[simp]
/-
**PUnit.default_eq_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PUnit.default_eq_unit : (default : PUnit) = PUnit.unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl

/-- Every provable proposition is unique, as all proofs are equal. -/
@[instance_reducible]
/-
**uniqueProp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniqueProp {p : Prop} (h : p) : Unique.{0} p where default
参数：h : p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every provable proposition is unique, as all proofs are equal.
-/
def uniqueProp {p : Prop} (h : p) : Unique.{0} p where
  default := h
  uniq _ := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique True :=
  uniqueProp trivial

namespace Unique

open Function

section

variable {α : Sort*} [Unique α]

-- see Note [lower instance priority]
/-
**Unique.** 是 Mathlib 中的一个实例，位于命名空间 `Unique`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : Inhabited α :=
  toInhabited ‹Unique α›
/-
**Unique.eq_default** 是 Mathlib 中的一个定理，位于命名空间 `Unique`。
形式化陈述：eq_default (a : α) : a = default
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
theorem eq_default (a : α) : a = default :=
  uniq _ a
/-
**Unique.default_eq** 是 Mathlib 中的一个定理，位于命名空间 `Unique`。
形式化陈述：default_eq (a : α) : default = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
-/
theorem default_eq (a : α) : default = a :=
  (uniq _ a).symm

-- see Note [lower instance priority]
/-
**Unique.** 是 Mathlib 中的一个实例，位于命名空间 `Unique`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instSubsingleton : Subsingleton α :=
  subsingleton_of_forall_eq _ eq_default
/-
**Unique.forall_iff** 是 Mathlib 中的一个定理，位于命名空间 `Unique`。
形式化陈述：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p default
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ p default :=
  ⟨fun h ↦ h _, fun h x ↦ by rwa [Unique.eq_default x]⟩
/-
**Unique.exists_iff** 是 Mathlib 中的一个定理，位于命名空间 `Unique`。
形式化陈述：exists_iff {p : α -> Prop} : Exists p ↔ p default
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem exists_iff {p : α → Prop} : Exists p ↔ p default :=
  ⟨fun ⟨a, ha⟩ ↦ eq_default a ▸ ha, Exists.intro default⟩

end

variable {α : Sort*}

@[ext]
/-
**Unique.subsingleton_unique'** 是 Mathlib 中的一个定理，位于命名空间 `Unique`。
形式化陈述：∀ {α : Sort u_1} (h₁ h₂ : Unique α), h₁ = h₂
参数：h₁ h₂ : Unique α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected theorem subsingleton_unique' : ∀ h₁ h₂ : Unique α, h₁ = h₂
  | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => by congr; rw [h x, h y]
/-
**Unique.subsingleton_unique** 是 Mathlib 中的一个实例，位于命名空间 `Unique`。
形式化陈述：subsingleton_unique : Subsingleton (Unique α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.subsingleton_unique'`：∀ {α : Sort u_1} (h₁ h₂ : Unique α), h₁ = h
₂
-/
instance subsingleton_unique : Subsingleton (Unique α) :=
  ⟨Unique.subsingleton_unique'⟩

/-- Construct `Unique` from `Inhabited` and `Subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
/-
**Unique.mk'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Unique`。
形式化陈述：mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α
参数：α : Sort u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct `Unique` from `Inhabited` and `Subsingleton`. Making this an instance 
would create
a loop in the class inheritance graph.
-/
abbrev mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun _ ↦ Subsingleton.elim _ _ }

end Unique

/-
**nonempty_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty α] : Nonempty (Uni
que α)
参数：α : Sort u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty α] : Nonempty (Unique α) := by
  inhabit α
  exact ⟨Unique.mk' α⟩
/-
**unique_iff_subsingleton_and_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_iff_subsingleton_and_nonempty (α : Sort u) : Nonempty (Unique α) ↔ 
Subsingleton α ∧ Nonempty α
参数：α : Sort u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
-/
theorem unique_iff_subsingleton_and_nonempty (α : Sort u) :
    Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α :=
  ⟨fun ⟨u⟩ ↦ by constructor <;> exact inferInstance,
   fun ⟨hs, hn⟩ ↦ nonempty_unique α⟩

variable {α : Sort*}

@[simp, push ←]
/-
**Pi.default_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.default_def {β : α -> Sort v} [forall a, Inhabited (β a)] : @default (f
orall a, β a) _ = fun a : α => @default (β a) _
参数：β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.default_def {β : α → Sort v} [∀ a, Inhabited (β a)] :
    @default (∀ a, β a) _ = fun a : α ↦ @default (β a) _ :=
  rfl
/-
**Pi.default_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.default_apply {β : α -> Sort v} [forall a, Inhabited (β a)] (a : α) : @
default (forall a, β a) _ a = default
参数：β a；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.default_apply {β : α → Sort v} [∀ a, Inhabited (β a)] (a : α) :
    @default (∀ a, β a) _ a = default :=
  rfl
/-
**Pi.unique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.unique {β : α -> Sort v} [forall a, Unique (β a)] : Unique (forall a, β
 a) where uniq
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.unique {β : α → Sort v} [∀ a, Unique (β a)] : Unique (∀ a, β a) where
  uniq := fun _ ↦ funext fun _ ↦ Unique.eq_default _

/-- There is a unique function on an empty domain. -/
/-
**Pi.uniqueOfIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.uniqueOfIsEmpty [IsEmpty α] (β : α -> Sort v) : Unique (forall a, β a) 
where default
参数：β : α -> Sort v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique function on an empty domain.
-/
instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : α → Sort v) : Unique (∀ a, β a) where
  default := isEmptyElim
  uniq _ := funext isEmptyElim
/-
**eq_const_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_const_of_subsingleton {β : Sort*} [Subsingleton α] (f : α -> β) (a : α)
 : f = Function.const α (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_const_of_subsingleton {β : Sort*} [Subsingleton α] (f : α → β) (a : α) :
    f = Function.const α (f a) :=
  funext fun x ↦ Subsingleton.elim x a ▸ rfl
/-
**eq_const_of_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_const_of_unique {β : Sort*} [Unique α] (f : α -> β) : f = Function.cons
t α (f default)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_const_of_subsingleton`：eq_const_of_subsingleton {β : Sort*} [Subsingl
eton α] (f : α -> β) (a : α) : f = Function.const α (f a)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem eq_const_of_unique {β : Sort*} [Unique α] (f : α → β) : f = Function.const α (f default) :=
  eq_const_of_subsingleton ..
/-
**heq_const_of_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：heq_const_of_unique [Unique α] {β : α -> Sort v} (f : forall a, β a) : f ≍
 Function.const α (f default)
参数：f : forall a, β a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem heq_const_of_unique [Unique α] {β : α → Sort v} (f : ∀ a, β a) :
    f ≍ Function.const α (f default) :=
  (Function.hfunext rfl) fun i _ _ ↦ by rw [Subsingleton.elim i default]; rfl

namespace Function

variable {β : Sort*} {f : α → β}

/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
/-
**Function.Injective.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`
。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Injective f → ∀ [Sub
singleton β], Subsingleton α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well.
-/
protected theorem Injective.subsingleton (hf : Injective f) [Subsingleton β] : Subsingleton α :=
  ⟨fun _ _ ↦ hf <| Subsingleton.elim _ _⟩

/-- If the domain of a surjective function is a subsingleton, then the codomain is a subsingleton as
well. -/
/-
**Function.Surjective.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} [Subsingleton α], Function.Sur
jective f → Subsingleton β
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
If the domain of a surjective function is a subsingleton, then the codomain is a
 subsingleton as
well.
-/
protected theorem Surjective.subsingleton [Subsingleton α] (hf : Surjective f) : Subsingleton β :=
  ⟨hf.forall₂.2 fun x y ↦ congr_arg f <| Subsingleton.elim x y⟩

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
@[instance_reducible]
/-
**Function.Surjective.unique** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：{β : Sort u_2} → {α : Sort u} → (f : α → β) → Function.Surjective f → [Uni
que α] → Unique β
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the domain of a surjective function is a singleton,
then the codomain is a singleton as well.
-/
protected def Surjective.unique {α : Sort u} (f : α → β) (hf : Surjective f) [Unique.{u} α] :
    Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.subsingleton

/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `Unique`. -/
@[instance_reducible]
/-
**Function.Injective.unique** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → {f : α → β} → [Inhabited α] → [Subsingle
ton β] → Function.Injective f → Unique α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α

--- 原说明 ---
If `α` is inhabited and admits an injective map to a subsingleton type, then `α`
 is `Unique`.
-/
protected def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
  @Unique.mk' _ _ hf.subsingleton

/-- If a constant function is surjective, then the codomain is a singleton. -/
@[instance_reducible]
/-
**Function.Surjective.uniqueOfSurjectiveConst** 是 Mathlib 中的一个定义，位于命名空间 `Functio
n.Surjective`。
形式化陈述：(α : Type u_3) → {β : Type u_4} → (b : β) → Function.Surjective (Function.
const α b) → Unique β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a constant function is surjective, then the codomain is a singleton.
-/
def Surjective.uniqueOfSurjectiveConst (α : Type*) {β : Type*} (b : β)
    (h : Function.Surjective (Function.const α b)) : Unique β :=
  @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ ↦ rfl) b

end Function

section Pi

variable {ι : Sort*} {α : ι → Sort*}

/-- Given one value over a unique, we get a dependent function. -/
/-
**uniqueElim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i
参数：x : α (default : ι)；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given one value over a unique, we get a dependent function.
-/
def uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i := by
  rw [Unique.eq_default i]
  exact x

@[simp]
/-
**uniqueElim_default** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (de
fault : ι) = x
参数：x : α (default : ι)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (default : ι) = x :=
  rfl

@[simp]
/-
**uniqueElim_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueElim_const {β : Sort*} {_ : Unique ι} (x : β) (i : ι) : uniqueElim (
α
参数：x : β；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueElim_const {β : Sort*} {_ : Unique ι} (x : β) (i : ι) :
    uniqueElim (α := fun _ ↦ β) x i = x :=
  rfl

end Pi

-- TODO: Mario turned this off as a simp lemma in Batteries, wanting to profile it.
attribute [local simp] eq_iff_true_of_subsingleton in
/-
**Unique.bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Unique.bijective {A B} [Unique A] [Unique B] {f : A -> B} : Function.Bijec
tive f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem Unique.bijective {A B} [Unique A] [Unique B] {f : A → B} : Function.Bijective f := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨default, ?_, ?_⟩ <;> intro x <;> simp

namespace Option

/-- `Option α` is a `Subsingleton` if and only if `α` is empty. -/
/-
**Option.subsingleton_iff_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：subsingleton_iff_isEmpty {α : Type u} : Subsingleton (Option α) ↔ IsEmpty 
α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
`Option α` is a `Subsingleton` if and only if `α` is empty.
-/
theorem subsingleton_iff_isEmpty {α : Type u} : Subsingleton (Option α) ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ Option.noConfusion rfl (heq_of_eq (@Subsingleton.elim _ h x none))⟩,
   fun h ↦ ⟨fun x y ↦
     Option.casesOn x (Option.casesOn y rfl fun x ↦ h.elim x) fun x ↦ h.elim x⟩⟩
/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [IsEmpty α] : Unique (Option α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)

end Option

section Subtype

/-
**Unique.subtypeEq** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unique.subtypeEq (y : α) : Unique { x // x = y } where default
参数：y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Unique.subtypeEq (y : α) : Unique { x // x = y } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ ↦ by congr
/-
**Unique.subtypeEq'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unique.subtypeEq' (y : α) : Unique { x // y = x } where default
参数：y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Unique.subtypeEq' (y : α) : Unique { x // y = x } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ ↦ by subst hx; congr

end Subtype

/-
**Fin.instUnique** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.instUnique : Unique (Fin 1) where uniq _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Fin.instUnique : Unique (Fin 1) where uniq _ := Subsingleton.elim _ _
