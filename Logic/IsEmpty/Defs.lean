/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init

/-!
# Types that are empty

In this file we define a typeclass `IsEmpty`, which expresses that a type has no elements.

## Main declaration

* `IsEmpty`: a typeclass that expresses that a type is empty.
-/

@[expose] public section

universe u v

variable {α : Sort u} {β : Sort v}

/-- `IsEmpty α` expresses that `α` is empty. -/
/-
**IsEmpty** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsEmpty α` expresses that `α` is empty.
-/
class IsEmpty (α : Sort u) : Prop where
  protected false : α → False
/-
**Empty.instIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Empty.instIsEmpty : IsEmpty Empty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Empty.instIsEmpty : IsEmpty Empty :=
  ⟨Empty.elim⟩
/-
**PEmpty.instIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PEmpty.instIsEmpty : IsEmpty PEmpty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PEmpty.instIsEmpty : IsEmpty PEmpty :=
  ⟨PEmpty.elim⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty False :=
  ⟨id⟩
/-
**Fin.isEmpty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.isEmpty : IsEmpty (Fin 0)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_lt_zero`：∀ (n : ℕ), ¬n < 0
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
instance Fin.isEmpty : IsEmpty (Fin 0) :=
  ⟨fun n ↦ Nat.not_lt_zero n.1 n.2⟩
/-
**Fin.isEmpty'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.isEmpty' : IsEmpty (Fin Nat.zero)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Fin.isEmpty' : IsEmpty (Fin Nat.zero) :=
  Fin.isEmpty
/-
**Function.isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), IsEmpty α
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
protected theorem Function.isEmpty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x ↦ IsEmpty.false (f x)⟩
/-
**Function.Surjective.isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.isEmpty [IsEmpty α] {f : α -> β} (hf : f.Surjective) :
 IsEmpty β
参数：hf : f.Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
theorem Function.Surjective.isEmpty [IsEmpty α] {f : α → β} (hf : f.Surjective) : IsEmpty β :=
  ⟨fun y ↦ let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

-- See note [instance argument order]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : α → Sort v} [∀ x, IsEmpty (p x)] [h : Nonempty α] : IsEmpty (∀ x, p x) :=
  h.elim fun x ↦ Function.isEmpty fun f ↦ f x
/-
**PProd.isEmpty_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
-/
instance PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst
/-
**PProd.isEmpty_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
-/
instance PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd
/-
**Prod.isEmpty_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
-/
instance Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst
/-
**Prod.isEmpty_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
-/
instance Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd
/-
**Quot.instIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quot.instIsEmpty [IsEmpty α] {r : α -> α -> Prop} : IsEmpty (Quot r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.isEmpty`：Function.Surjective.isEmpty [IsEmpty α] {f 
: α -> β} (hf : f.Surjective) : IsEmpty β
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
instance Quot.instIsEmpty [IsEmpty α] {r : α → α → Prop} : IsEmpty (Quot r) :=
  Function.Surjective.isEmpty Quot.exists_rep
/-
**Quotient.instIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.instIsEmpty [IsEmpty α] {s : Setoid α} : IsEmpty (Quotient s)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quotient.instIsEmpty [IsEmpty α] {s : Setoid α} : IsEmpty (Quotient s) :=
  Quot.instIsEmpty
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) :=
  ⟨fun x ↦ PSum.rec IsEmpty.false IsEmpty.false x⟩
/-
**instIsEmptySum** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIsEmptySum {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
instance instIsEmptySum {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) :=
  ⟨fun x ↦ Sum.rec IsEmpty.false IsEmpty.false x⟩

/-- subtypes of an empty type are empty -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
subtypes of an empty type are empty
-/
instance [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ IsEmpty.false x.1⟩

/-- subtypes by an all-false predicate are false. -/
/-
**Subtype.isEmpty_of_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.isEmpty_of_false {p : α -> Prop} (hp : forall a, ¬p a) : IsEmpty (
Subtype p)
参数：hp : forall a, ¬p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
subtypes by an all-false predicate are false.
-/
theorem Subtype.isEmpty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x ↦ hp _ x.2⟩

/-- subtypes by false are false. -/
/-
**Subtype.isEmpty_false** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.isEmpty_false : IsEmpty { _a : α // False }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.isEmpty_of_false`：Subtype.isEmpty_of_false {p : α -> Prop} (hp :
 forall a, ¬p a) : IsEmpty (Subtype p)

--- 原说明 ---
subtypes by false are false.
-/
instance Subtype.isEmpty_false : IsEmpty { _a : α // False } :=
  Subtype.isEmpty_of_false fun _ ↦ id
/-
**Sigma.isEmpty_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sigma.isEmpty_left {α} [IsEmpty α] {E : α -> Type v} : IsEmpty (Sigma E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
-/
instance Sigma.isEmpty_left {α} [IsEmpty α] {E : α → Type v} : IsEmpty (Sigma E) :=
  Function.isEmpty Sigma.fst
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance

/-- Eliminate out of a type that `IsEmpty` (without using projection notation). -/
@[elab_as_elim]
/-
**isEmptyElim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isEmptyElim [IsEmpty α] {p : α -> Sort v} (a : α) : p a
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False

--- 原说明 ---
Eliminate out of a type that `IsEmpty` (without using projection notation).
-/
def isEmptyElim [IsEmpty α] {p : α → Sort v} (a : α) : p a :=
  (IsEmpty.false a).elim
/-
**isEmpty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_iff : IsEmpty α ↔ α -> False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
theorem isEmpty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩

namespace IsEmpty

open Function

/-- Eliminate out of a type that `IsEmpty` (using projection notation). -/
@[elab_as_elim]
/-
**IsEmpty.elim** 是 Mathlib 中的一个定义，位于命名空间 `IsEmpty`。
形式化陈述：{α : Sort u} → IsEmpty α → {p : α → Sort v} → (a : α) → p a
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Eliminate out of a type that `IsEmpty` (using projection notation).
-/
protected def elim (_ : IsEmpty α) {p : α → Sort v} (a : α) : p a :=
  isEmptyElim a

/-- Non-dependent version of `IsEmpty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
correctly. -/
/-
**IsEmpty.elim'** 是 Mathlib 中的一个定义，位于命名空间 `IsEmpty`。
形式化陈述：{α : Sort u} → {β : Sort v} → IsEmpty α → α → β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False

--- 原说明 ---
Non-dependent version of `IsEmpty.elim`. Helpful if the elaborator cannot elabor
ate `h.elim a`
correctly.
-/
protected def elim' (h : IsEmpty α) (a : α) : β :=
  (h.false a).elim
/-
**IsEmpty.prop_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsEmpty`。
形式化陈述：∀ {p : Prop}, IsEmpty p ↔ ¬p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_iff`：isEmpty_iff : IsEmpty α ↔ α -> False
-/
protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  isEmpty_iff

variable [IsEmpty α]

@[simp]
/-
**IsEmpty.forall_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsEmpty`。
形式化陈述：forall_iff {p : α -> Prop} : (forall a, p a) ↔ True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
-/
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim

@[simp]
/-
**IsEmpty.exists_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsEmpty`。
形式化陈述：exists_iff {p : α -> Prop} : (exists a, p a) ↔ False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_false_intro`：∀ {a : Prop}, ¬a → (a ↔ False)
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, _⟩ ↦ IsEmpty.false x

-- see Note [lower instance priority]
/-
**IsEmpty.** 是 Mathlib 中的一个实例，位于命名空间 `IsEmpty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty

