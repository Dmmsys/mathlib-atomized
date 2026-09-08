/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Coe

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `Monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `Antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `MonotoneOn f s`: Same as `Monotone f`, but for all `a, b ∈ s`.
* `AntitoneOn f s`: Same as `Antitone f`, but for all `a, b ∈ s`.
* `StrictMono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `StrictAnti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `StrictMonoOn f s`: Same as `StrictMono f`, but for all `a, b ∈ s`.
* `StrictAntiOn f s`: Same as `StrictAnti f`, but for all `a, b ∈ s`.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

@[expose] public section

assert_not_exists Nat.instLinearOrder Int.instLinearOrder


open Function

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {π : ι → Type*}

section MonotoneDef

variable [Preorder α] [Preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
/-
**Monotone** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Monotone (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`.
-/
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

to_dual_insert_cast Monotone := forall_comm.eq

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
/-
**Antitone** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Antitone (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`.
-/
def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

to_dual_insert_cast Antitone := forall_comm.eq

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
/-
**MonotoneOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonotoneOn (f : α -> β) (s : Set α) : Prop
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤
 f b`.
-/
def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b

to_dual_insert_cast MonotoneOn := by grind only

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
/-
**AntitoneOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AntitoneOn (f : α -> β) (s : Set α) : Prop
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤
 f a`.
-/
def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a

to_dual_insert_cast AntitoneOn := by grind only

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
/-
**StrictMono** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictMono (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is strictly monotone if `a < b` implies `f a < f b`.
-/
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

to_dual_insert_cast StrictMono := forall_comm.eq

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
/-
**StrictAnti** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictAnti (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is strictly antitone if `a < b` implies `f b < f a`.
-/
def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a

to_dual_insert_cast StrictAnti := forall_comm.eq

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
/-
**StrictMonoOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictMonoOn (f : α -> β) (s : Set α) : Prop
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` impli
es
`f a < f b`.
-/
def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a < f b

to_dual_insert_cast StrictMonoOn := by grind only

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
/-
**StrictAntiOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictAntiOn (f : α -> β) (s : Set α) : Prop
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` impli
es
`f b < f a`.
-/
def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b < f a

to_dual_insert_cast StrictAntiOn := by grind only

end MonotoneDef

section Decidable

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a b, a ≤ b → f a ≤ f b)] : Decidable (Monotone f) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a b, a ≤ b → f b ≤ f a)] : Decidable (Antitone f) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a ≤ b → f a ≤ f b)] :
    Decidable (MonotoneOn f s) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a ≤ b → f b ≤ f a)] :
    Decidable (AntitoneOn f s) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a b, a < b → f a < f b)] : Decidable (StrictMono f) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a b, a < b → f b < f a)] : Decidable (StrictAnti f) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b)] :
    Decidable (StrictMonoOn f s) := i
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a < b → f b < f a)] :
    Decidable (StrictAntiOn f s) := i

end Decidable

/-! ### Monotonicity in function spaces -/


section Preorder

variable [Preorder α]

@[to_dual self]
/-
**Monotone.comp_le_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.comp_le_comp_left [Preorder β] {f : β -> α} {g h : γ -> β} (hf : 
Monotone f) (le_gh : g <= h) : LE.le.{max w u} (f ∘ g) (f ∘ h)
参数：hf : Monotone f；le_gh : g <= h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.comp_le_comp_left
    [Preorder β] {f : β → α} {g h : γ → β} (hf : Monotone f) (le_gh : g ≤ h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) :=
  fun x ↦ hf (le_gh x)

variable [Preorder γ]
/-
**monotone_lam** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_lam {f : α -> β -> γ} (hf : forall b, Monotone fun a => f a b) : 
Monotone f
参数：hf : forall b, Monotone fun a => f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monotone_lam {f : α → β → γ} (hf : ∀ b, Monotone fun a ↦ f a b) : Monotone f :=
  fun _ _ h b ↦ hf b h
/-
**monotone_app** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_app (f : β -> α -> γ) (b : β) (hf : Monotone fun a b => f b a) : 
Monotone (f b)
参数：f : β -> α -> γ；b : β；hf : Monotone fun a b => f b a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monotone_app (f : β → α → γ) (b : β) (hf : Monotone fun a b ↦ f b a) : Monotone (f b) :=
  fun _ _ h ↦ hf h b
/-
**antitone_lam** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_lam {f : α -> β -> γ} (hf : forall b, Antitone fun a => f a b) : 
Antitone f
参数：hf : forall b, Antitone fun a => f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antitone_lam {f : α → β → γ} (hf : ∀ b, Antitone fun a ↦ f a b) : Antitone f :=
  fun _ _ h b ↦ hf b h
/-
**antitone_app** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_app (f : β -> α -> γ) (b : β) (hf : Antitone fun a b => f b a) : 
Antitone (f b)
参数：f : β -> α -> γ；b : β；hf : Antitone fun a b => f b a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antitone_app (f : β → α → γ) (b : β) (hf : Antitone fun a b ↦ f b a) : Antitone (f b) :=
  fun _ _ h ↦ hf h b

end Preorder

/-
**Function.monotone_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.monotone_eval {ι : Type u} {α : ι -> Type v} [forall i, Preorder 
(α i)] (i : ι) : Monotone (Function.eval i : (forall i, α i) -> α i)
参数：α i；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] (i : ι) :
    Monotone (Function.eval i : (∀ i, α i) → α i) := fun _ _ H ↦ H i

/-! ### Monotonicity hierarchy -/


section Preorder

variable [Preorder α]

section Preorder

variable [Preorder β] {f : α → β} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `Monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/

@[to_dual self]
/-
**Monotone.imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.imp (hf : Monotone f) (h : a <= b) : f a <= f b
参数：hf : Monotone f；h : a <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`
. This is useful
when you do not want to apply a `Monotone` assumption (i.e. your goal is `a ≤ b 
→ f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `h
f h` instead.
-/
theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b :=
  hf h

@[to_dual self]
/-
**Antitone.imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.imp (hf : Antitone f) (h : a <= b) : f b <= f a
参数：hf : Antitone f；h : a <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antitone.imp (hf : Antitone f) (h : a ≤ b) : f b ≤ f a :=
  hf h

@[to_dual self]
/-
**StrictMono.imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b
参数：hf : StrictMono f；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b :=
  hf h

@[to_dual self]
/-
**StrictAnti.imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f a
参数：hf : StrictAnti f；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f a :=
  hf h
/-
**Monotone.monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.imp`：Monotone.imp (hf : Monotone f) (h : a <= b) : f a <= f b
-/
protected theorem Monotone.monotoneOn (hf : Monotone f) (s : Set α) : MonotoneOn f s :=
  fun _ _ _ _ ↦ hf.imp
/-
**Antitone.antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.imp`：Antitone.imp (hf : Antitone f) (h : a <= b) : f b <= f a
-/
protected theorem Antitone.antitoneOn (hf : Antitone f) (s : Set α) : AntitoneOn f s :=
  fun _ _ _ _ ↦ hf.imp
/-
**monotoneOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β}, MonotoneOn f Set.univ ↔ Monotone f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
@[simp] theorem monotoneOn_univ : MonotoneOn f Set.univ ↔ Monotone f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.monotoneOn _⟩
/-
**antitoneOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β}, AntitoneOn f Set.univ ↔ Antitone f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
@[simp] theorem antitoneOn_univ : AntitoneOn f Set.univ ↔ Antitone f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.antitoneOn _⟩
/-
**StrictMono.strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn f s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.imp`：StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f
 b
-/
protected theorem StrictMono.strictMonoOn (hf : StrictMono f) (s : Set α) : StrictMonoOn f s :=
  fun _ _ _ _ ↦ hf.imp
/-
**StrictAnti.strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn f s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.imp`：StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f
 a
-/
protected theorem StrictAnti.strictAntiOn (hf : StrictAnti f) (s : Set α) : StrictAntiOn f s :=
  fun _ _ _ _ ↦ hf.imp
/-
**strictMonoOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   StrictMonoOn f Set.univ ↔ StrictMono f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
@[simp] theorem strictMonoOn_univ : StrictMonoOn f Set.univ ↔ StrictMono f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.strictMonoOn _⟩
/-
**strictAntiOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f :
 α → β},   StrictAntiOn f Set.univ ↔ StrictAnti f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
@[simp] theorem strictAntiOn_univ : StrictAntiOn f Set.univ ↔ StrictAnti f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.strictAntiOn _⟩

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β}

/-
**Monotone.strictMono_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.strictMono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : St
rictMono f
参数：h₁ : Monotone f；h₂ : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem Monotone.strictMono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : StrictMono f :=
  fun _ _ h ↦ (h₁ h.le).lt_of_ne fun H ↦ h.ne <| h₂ H
/-
**Antitone.strictAnti_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.strictAnti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : St
rictAnti f
参数：h₁ : Antitone f；h₂ : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Antitone.strictAnti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : StrictAnti f :=
  fun _ _ h ↦ (h₁ h.le).lt_of_ne fun H ↦ h.ne <| h₂ H.symm

end PartialOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {f : α → β} {s : Set α}

@[to_dual none]
/-
**monotone_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a b⦄, a < b -> f a <= f b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congr fun _ _ ↦
    ⟨fun hf h ↦ hf h.le, fun hf h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).le) hf⟩

@[to_dual none]
/-
**antitone_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a b⦄, a < b -> f b <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem antitone_iff_forall_lt : Antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congr fun _ _ ↦
    ⟨fun hf h ↦ hf h.le, fun hf h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).ge) hf⟩

@[to_dual none]
/-
**monotoneOn_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_iff_forall_lt : MonotoneOn f s ↔ forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_
 : b in s), a < b -> f a <= f b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem monotoneOn_iff_forall_lt :
    MonotoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a ≤ f b :=
  ⟨fun hf _ ha _ hb h ↦ hf ha hb h.le,
   fun hf _ ha _ hb h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).le) (hf ha hb)⟩

@[to_dual none]
/-
**antitoneOn_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_iff_forall_lt : AntitoneOn f s ↔ forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_
 : b in s), a < b -> f b <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem antitoneOn_iff_forall_lt :
    AntitoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b ≤ f a :=
  ⟨fun hf _ ha _ hb h ↦ hf ha hb h.le,
   fun hf _ ha _ hb h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).ge) (hf ha hb)⟩

-- `Preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `StrictMono f` is vacuously true.
/-
**StrictMonoOn.monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `StrictMonoOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   StrictMonoOn f s → MonotoneOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotoneOn_iff_forall_lt`：monotoneOn_iff_forall_lt : MonotoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a <= f b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
protected theorem StrictMonoOn.monotoneOn (hf : StrictMonoOn f s) : MonotoneOn f s :=
  monotoneOn_iff_forall_lt.2 fun _ ha _ hb h ↦ (hf ha hb h).le
/-
**StrictAntiOn.antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `StrictAntiOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder α] [inst_1 : Preorder β] 
{f : α → β} {s : Set α},   StrictAntiOn f s → AntitoneOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitoneOn_iff_forall_lt`：antitoneOn_iff_forall_lt : AntitoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b <= f a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
protected theorem StrictAntiOn.antitoneOn (hf : StrictAntiOn f s) : AntitoneOn f s :=
  antitoneOn_iff_forall_lt.2 fun _ ha _ hb h ↦ (hf ha hb h).le
/-
**StrictMono.monotone** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder α] [inst_1 : Preorder β] 
{f : α → β}, StrictMono f → Monotone f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
protected theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  monotone_iff_forall_lt.2 fun _ _ h ↦ (hf h).le
/-
**StrictAnti.antitone** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PartialOrder α] [inst_1 : Preorder β] 
{f : α → β}, StrictAnti f → Antitone f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitone_iff_forall_lt`：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a 
b⦄, a < b -> f b <= f a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
protected theorem StrictAnti.antitone (hf : StrictAnti f) : Antitone f :=
  antitone_iff_forall_lt.2 fun _ _ h ↦ (hf h).le

end PartialOrder

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorder α] [Preorder β]

/-
**Subsingleton.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] [Sub
singleton α] (f : α → β), Monotone f
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem monotone [Subsingleton α] (f : α → β) : Monotone f :=
  fun _ _ _ ↦ (congr_arg _ <| Subsingleton.elim _ _).le
/-
**Subsingleton.antitone** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] [Sub
singleton α] (f : α → β), Antitone f
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem antitone [Subsingleton α] (f : α → β) : Antitone f :=
  fun _ _ _ ↦ (congr_arg _ <| Subsingleton.elim _ _).le
/-
**Subsingleton.monotone'** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：monotone' [Subsingleton β] (f : α -> β) : Monotone f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem monotone' [Subsingleton β] (f : α → β) : Monotone f :=
  fun _ _ _ ↦ (Subsingleton.elim _ _).le
/-
**Subsingleton.antitone'** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：antitone' [Subsingleton β] (f : α -> β) : Antitone f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem antitone' [Subsingleton β] (f : α → β) : Antitone f :=
  fun _ _ _ ↦ (Subsingleton.elim _ _).le
/-
**Subsingleton.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] [Sub
singleton α] (f : α → β), StrictMono f
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem strictMono [Subsingleton α] (f : α → β) : StrictMono f :=
  fun _ _ h ↦ (h.ne <| Subsingleton.elim _ _).elim
/-
**Subsingleton.strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] [Sub
singleton α] (f : α → β), StrictAnti f
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem strictAnti [Subsingleton α] (f : α → β) : StrictAnti f :=
  fun _ _ h ↦ (h.ne <| Subsingleton.elim _ _).elim

end Subsingleton

/-! ### Miscellaneous monotonicity results -/


/-
**monotone_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_id [Preorder α] : Monotone (id : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Miscellaneous monotonicity results
-/
theorem monotone_id [Preorder α] : Monotone (id : α → α) := fun _ _ ↦ id
/-
**monotoneOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_id [Preorder α] {s : Set α} : MonotoneOn id s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monotoneOn_id [Preorder α] {s : Set α} : MonotoneOn id s := fun _ _ _ _ ↦ id
/-
**strictMono_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_id [Preorder α] : StrictMono (id : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem strictMono_id [Preorder α] : StrictMono (id : α → α) := fun _ _ ↦ id
/-
**strictMonoOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_id [Preorder α] {s : Set α} : StrictMonoOn id s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem strictMonoOn_id [Preorder α] {s : Set α} : StrictMonoOn id s := fun _ _ _ _ ↦ id
/-
**monotone_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_const [Preorder α] [Preorder β] {c : β} : Monotone fun _ : α => c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monotone_const [Preorder α] [Preorder β] {c : β} : Monotone fun _ : α ↦ c :=
  fun _ _ _ ↦ le_rfl
/-
**monotoneOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} : MonotoneO
n (fun _ : α => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monotoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    MonotoneOn (fun _ : α ↦ c) s :=
  fun _ _ _ _ _ ↦ le_rfl
/-
**antitone_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_const [Preorder α] [Preorder β] {c : β} : Antitone fun _ : α => c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem antitone_const [Preorder α] [Preorder β] {c : β} : Antitone fun _ : α ↦ c :=
  fun _ _ _ ↦ le_refl c
/-
**antitoneOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} : AntitoneO
n (fun _ : α => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem antitoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    AntitoneOn (fun _ : α ↦ c) s :=
  fun _ _ _ _ _ ↦ le_rfl

@[to_dual self]
/-
**strictMono_of_le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_of_le_iff_le [Preorder α] [Preorder β] {f : α -> β} (h : forall
 x y, x <= y ↔ f x <= f y) : StrictMono f
参数：h : forall x y, x <= y ↔ f x <= f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
-/
theorem strictMono_of_le_iff_le [Preorder α] [Preorder β] {f : α → β}
    (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : StrictMono f :=
  fun _ _ ↦ (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1
/-
**strictAnti_of_le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_of_le_iff_le [Preorder α] [Preorder β] {f : α -> β} (h : forall
 x y, x <= y ↔ f y <= f x) : StrictAnti f
参数：h : forall x y, x <= y ↔ f y <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
-/
theorem strictAnti_of_le_iff_le [Preorder α] [Preorder β] {f : α → β}
    (h : ∀ x y, x ≤ y ↔ f y ≤ f x) : StrictAnti f :=
  fun _ _ ↦ (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

@[to_dual none]
/-
**Function.Injective.of_lt_imp_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.of_lt_imp_ne [LinearOrder α] {f : α -> β} (h : forall x
 y, x < y -> f x != f y) : Injective f
参数：h : forall x y, x < y -> f x != f y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.Injective.of_lt_imp_ne [LinearOrder α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
    Injective f := by
  grind [Injective]
/-
**Function.Injective.of_eq_imp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.of_eq_imp_le [PartialOrder α] {f : α -> β} (h : forall 
{x y}, f x = f y -> x <= y) : f.Injective
参数：h : forall {x y}, f x = f y -> x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Function.Injective.of_eq_imp_le [PartialOrder α] {f : α → β}
    (h : ∀ {x y}, f x = f y → x ≤ y) : f.Injective :=
  fun _ _ hxy ↦ h hxy |>.antisymm <| h hxy.symm

/-! ### Monotonicity under composition -/


section Composition

variable [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α} {t : Set β}

/-
**Monotone.comp** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monotone g → Monotone 
f → Monotone (g ∘ f)
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**Monotone.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘
 f)
参数：hg : Monotone g；hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**Antitone.comp** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antitone g → Antitone 
f → Monotone (g ∘ f)
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**Antitone.comp_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘
 f)
参数：hg : Antitone g；hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**Monotone.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Monotone f → ∀ (n : ℕ), Mo
notone f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
-/
protected theorem Monotone.iterate {f : α → α} (hf : Monotone f) (n : ℕ) : Monotone f^[n] :=
  Nat.recOn n monotone_id fun _ h ↦ h.comp hf
/-
**Monotone.comp_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β} {s : Set α}, Monotone g
 → MonotoneOn f s → MonotoneOn (g ∘ f) s
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Monotone.comp_monotoneOn (hg : Monotone g) (hf : MonotoneOn f s) :
    MonotoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**Monotone.comp_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.comp_antitoneOn (hg : Monotone g) (hf : AntitoneOn f s) : Antiton
eOn (g ∘ f) s
参数：hg : Monotone g；hf : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.comp_antitoneOn (hg : Monotone g) (hf : AntitoneOn f s) : AntitoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**Antitone.comp_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β} {s : Set α}, Antitone g
 → AntitoneOn f s → MonotoneOn (g ∘ f) s
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Antitone.comp_antitoneOn (hg : Antitone g) (hf : AntitoneOn f s) :
    MonotoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**Antitone.comp_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.comp_monotoneOn (hg : Antitone g) (hf : MonotoneOn f s) : Antiton
eOn (g ∘ f) s
参数：hg : Antitone g；hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antitone.comp_monotoneOn (hg : Antitone g) (hf : MonotoneOn f s) : AntitoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**StrictMono.comp** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, StrictMono g → StrictM
ono f → StrictMono (g ∘ f)
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem StrictMono.comp (hg : StrictMono g) (hf : StrictMono f) : StrictMono (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**StrictMono.comp_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.comp_strictAnti (hg : StrictMono g) (hf : StrictAnti f) : Stric
tAnti (g ∘ f)
参数：hg : StrictMono g；hf : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictMono.comp_strictAnti (hg : StrictMono g) (hf : StrictAnti f) : StrictAnti (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**StrictAnti.comp** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, StrictAnti g → StrictA
nti f → StrictMono (g ∘ f)
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem StrictAnti.comp (hg : StrictAnti g) (hf : StrictAnti f) : StrictMono (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**StrictAnti.comp_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.comp_strictMono (hg : StrictAnti g) (hf : StrictMono f) : Stric
tAnti (g ∘ f)
参数：hg : StrictAnti g；hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictAnti.comp_strictMono (hg : StrictAnti g) (hf : StrictMono f) : StrictAnti (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)
/-
**StrictMono.iterate** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} [inst : Preorder α] {f : α → α}, StrictMono f → ∀ (n : ℕ), 
StrictMono f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
-/
protected theorem StrictMono.iterate {f : α → α} (hf : StrictMono f) (n : ℕ) : StrictMono f^[n] :=
  Nat.recOn n strictMono_id fun _ h ↦ h.comp hf
/-
**StrictMono.comp_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β} {s : Set α}, StrictMono
 g → StrictMonoOn f s → StrictMonoOn (g ∘ f) s
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem StrictMono.comp_strictMonoOn (hg : StrictMono g) (hf : StrictMonoOn f s) :
    StrictMonoOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**StrictMono.comp_strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.comp_strictAntiOn (hg : StrictMono g) (hf : StrictAntiOn f s) :
 StrictAntiOn (g ∘ f) s
参数：hg : StrictMono g；hf : StrictAntiOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictMono.comp_strictAntiOn (hg : StrictMono g) (hf : StrictAntiOn f s) :
    StrictAntiOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**StrictAnti.comp_strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder α] [inst_1 : Pre
order β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β} {s : Set α}, StrictAnti
 g → StrictAntiOn f s → StrictMonoOn (g ∘ f) s
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem StrictAnti.comp_strictAntiOn (hg : StrictAnti g) (hf : StrictAntiOn f s) :
    StrictMonoOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**StrictAnti.comp_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.comp_strictMonoOn (hg : StrictAnti g) (hf : StrictMonoOn f s) :
 StrictAntiOn (g ∘ f) s
参数：hg : StrictAnti g；hf : StrictMonoOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictAnti.comp_strictMonoOn (hg : StrictAnti g) (hf : StrictMonoOn f s) :
    StrictAntiOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)
/-
**MonotoneOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.comp (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.Maps
To f s t) : MonotoneOn (g ∘ f) s
参数：hg : MonotoneOn g t；hf : MonotoneOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonotoneOn.comp (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.MapsTo f s t) :
    MonotoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hx) (hs hy) <| hf hx hy hxy
/-
**MonotoneOn.comp_AntitoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.comp_AntitoneOn (hg : MonotoneOn g t) (hf : AntitoneOn f s) (hs
 : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s
参数：hg : MonotoneOn g t；hf : AntitoneOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonotoneOn.comp_AntitoneOn (hg : MonotoneOn g t) (hf : AntitoneOn f s)
    (hs : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hy) (hs hx) <| hf hx hy hxy
/-
**AntitoneOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.comp (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.Maps
To f s t) : MonotoneOn (g ∘ f) s
参数：hg : AntitoneOn g t；hf : AntitoneOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AntitoneOn.comp (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.MapsTo f s t) :
    MonotoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hy) (hs hx) <| hf hx hy hxy
/-
**AntitoneOn.comp_MonotoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.comp_MonotoneOn (hg : AntitoneOn g t) (hf : MonotoneOn f s) (hs
 : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s
参数：hg : AntitoneOn g t；hf : MonotoneOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma AntitoneOn.comp_MonotoneOn (hg : AntitoneOn g t) (hf : MonotoneOn f s)
    (hs : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hx) (hs hy) <| hf hx hy hxy
/-
**StrictMonoOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Se
t.MapsTo f s t) : StrictMonoOn (g ∘ f) s
参数：hg : StrictMonoOn g t；hf : StrictMonoOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hx) (hs hy) <| hf hx hy hxy
/-
**StrictMonoOn.comp_strictAntiOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.comp_strictAntiOn (hg : StrictMonoOn g t) (hf : StrictAntiOn 
f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s
参数：hg : StrictMonoOn g t；hf : StrictAntiOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma StrictMonoOn.comp_strictAntiOn (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hy) (hs hx) <| hf hx hy hxy
/-
**StrictAntiOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.comp (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Se
t.MapsTo f s t) : StrictMonoOn (g ∘ f) s
参数：hg : StrictAntiOn g t；hf : StrictAntiOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma StrictAntiOn.comp (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hy) (hs hx) <| hf hx hy hxy
/-
**StrictAntiOn.comp_strictMonoOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.comp_strictMonoOn (hg : StrictAntiOn g t) (hf : StrictMonoOn 
f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s
参数：hg : StrictAntiOn g t；hf : StrictMonoOn f s；hs : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma StrictAntiOn.comp_strictMonoOn (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hx) (hs hy) <| hf hx hy hxy

end Composition

/-! ### Monotonicity in linear orders  -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α → β} {s : Set α}

open Ordering

@[to_dual self]
/-
**Monotone.reflect_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b
参数：hf : Monotone f；h : f a < f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' ↦ h.not_ge (hf h')

@[to_dual self]
/-
**Antitone.reflect_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a
参数：hf : Antitone f；h : f a < f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' ↦ h.not_ge (hf h')

@[to_dual self (reorder := a b, ha hb)]
/-
**MonotoneOn.reflect_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a in s) (hb : 
b in s) (h : f a < f b) : a < b
参数：hf : MonotoneOn f s；ha : a in s；hb : b in s；h : f a < f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' ↦ h.not_ge <| hf hb ha h'

@[to_dual self (reorder := a b, ha hb)]
/-
**AntitoneOn.reflect_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a in s) (hb : 
b in s) (h : f a < f b) : b < a
参数：hf : AntitoneOn f s；ha : a in s；hb : b in s；h : f a < f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' ↦ h.not_ge <| hf ha hb h'

end Preorder

end LinearOrder

/-
**Subtype.mono_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monotone ((↑) : Subtype p 
-> α)
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subtype.mono_coe [Preorder α] (p : α → Prop) : Monotone ((↑) : Subtype p → α) :=
  fun _ _ ↦ id
/-
**Subtype.strictMono_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.strictMono_coe [Preorder α] (p : α -> Prop) : StrictMono ((↑) : Su
btype p -> α)
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subtype.strictMono_coe [Preorder α] (p : α → Prop) :
    StrictMono ((↑) : Subtype p → α) :=
  fun _ _ ↦ id

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ}

/-
**monotone_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_fst : Monotone (@Prod.fst α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem monotone_fst : Monotone (@Prod.fst α β) := fun _ _ ↦ And.left
/-
**monotone_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_snd : Monotone (@Prod.snd α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem monotone_snd : Monotone (@Prod.snd α β) := fun _ _ ↦ And.right
/-
**monotone_prodMk_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_prodMk_iff {f : γ -> α} {g : γ -> β} : Monotone (fun x => (f x, g
 x)) ↔ Monotone f ∧ Monotone g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monotone_prodMk_iff {f : γ → α} {g : γ → β} :
    Monotone (fun x => (f x, g x)) ↔ Monotone f ∧ Monotone g := by
  simp_rw [Monotone, Prod.mk_le_mk, forall_and]
/-
**Monotone.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.prodMk {f : γ -> α} {g : γ -> β} (hf : Monotone f) (hg : Monotone
 g) : Monotone (fun x => (f x, g x))
参数：hf : Monotone f；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_prodMk_iff`：monotone_prodMk_iff {f : γ -> α} {g : γ -> β} : Mon
otone (fun x => (f x, g x)) ↔ Monotone f ∧ Monotone g
-/
theorem Monotone.prodMk {f : γ → α} {g : γ → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x => (f x, g x)) :=
  monotone_prodMk_iff.2 ⟨hf, hg⟩
/-
**Monotone.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.prodMap (hf : Monotone f) (hg : Monotone g) : Monotone (Prod.map 
f g)
参数：hf : Monotone f；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Monotone.prodMap (hf : Monotone f) (hg : Monotone g) : Monotone (Prod.map f g) :=
  fun _ _ h ↦ ⟨hf h.1, hg h.2⟩
/-
**Antitone.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.prodMap (hf : Antitone f) (hg : Antitone g) : Antitone (Prod.map 
f g)
参数：hf : Antitone f；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Antitone.prodMap (hf : Antitone f) (hg : Antitone g) : Antitone (Prod.map f g) :=
  fun _ _ h ↦ ⟨hf h.1, hg h.2⟩
/-
**monotone_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_prod_iff {h : α × β -> γ} : Monotone h ↔ (forall a, Monotone (fun
 b => h (a, b))) ∧ (forall b, Monotone (fun a => h (a, b))) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_le_mk_iff_right`：mk_le_mk_iff_right : (a, b₁) <= (a, b₂) ↔ b₁ <=
 b₂
· 使用定理 `Prod.mk_le_mk_iff_left`：mk_le_mk_iff_left : (a₁, b) <= (a₂, b) ↔ a₁ <= a
₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_le_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : L
E β] {a₁ a₂ : α} {b₁ b₂ : β},   (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂
-/
lemma monotone_prod_iff {h : α × β → γ} :
    Monotone h ↔ (∀ a, Monotone (fun b => h (a, b))) ∧ (∀ b, Monotone (fun a => h (a, b))) where
  mp h := ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)
/-
**antitone_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_prod_iff {h : α × β -> γ} : Antitone h ↔ (forall a, Antitone (fun
 b => h (a, b))) ∧ (forall b, Antitone (fun a => h (a, b))) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_le_mk_iff_right`：mk_le_mk_iff_right : (a, b₁) <= (a, b₂) ↔ b₁ <=
 b₂
· 使用定理 `Prod.mk_le_mk_iff_left`：mk_le_mk_iff_left : (a₁, b) <= (a₂, b) ↔ a₁ <= a
₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_le_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : L
E β] {a₁ a₂ : α} {b₁ b₂ : β},   (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂
-/
lemma antitone_prod_iff {h : α × β → γ} :
    Antitone h ↔ (∀ a, Antitone (fun b => h (a, b))) ∧ (∀ b, Antitone (fun a => h (a, b))) where
  mp h := ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ}

/-
**StrictMono.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.prodMap (hf : StrictMono f) (hg : StrictMono g) : StrictMono (P
rod.map f g)
参数：hf : StrictMono f；hg : StrictMono g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `StrictMono.imp`：StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f
 b
· 使用定理 `Monotone.imp`：Monotone.imp (hf : Monotone f) (h : a <= b) : f a <= f b
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
-/
theorem StrictMono.prodMap (hf : StrictMono f) (hg : StrictMono g) : StrictMono (Prod.map f g) :=
  fun a b ↦ by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)
/-
**StrictAnti.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.prodMap (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti (P
rod.map f g)
参数：hf : StrictAnti f；hg : StrictAnti g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `StrictAnti.imp`：StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f
 a
· 使用定理 `Antitone.imp`：Antitone.imp (hf : Antitone f) (h : a <= b) : f b <= f a
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
-/
theorem StrictAnti.prodMap (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti (Prod.map f g) :=
  fun a b ↦ by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.antitone.imp) (And.imp hf.antitone.imp hg.imp)

end PartialOrder

/-! ### Pi types -/

namespace Function

variable [Preorder α] [DecidableEq ι] [∀ i, Preorder (π i)] {f : ∀ i, π i} {i : ι}

-- Porting note: Dot notation breaks in `f.update i`
/-
**Function.update_mono** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_mono : Monotone (update f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `update_le_update_iff'`：update_le_update_iff' : update x i a <= update x 
i b ↔ a <= b
-/
theorem update_mono : Monotone (update f i) := fun _ _ => update_le_update_iff'.2
/-
**Function.update_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_strictMono : StrictMono (update f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `update_lt_update_iff`：update_lt_update_iff : update x i a < update x i b
 ↔ a < b
-/
theorem update_strictMono : StrictMono (update f i) := fun _ _ => update_lt_update_iff.2
/-
**Function.const_mono** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_mono : Monotone (const β : α -> β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_mono : Monotone (const β : α → β → α) := fun _ _ h _ ↦ h
/-
**Function.const_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_strictMono [Nonempty β] : StrictMono (const β : α -> β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.const_lt_const`：const_lt_const : const β a < const β b ↔ a < b
-/
theorem const_strictMono [Nonempty β] : StrictMono (const β : α → β → α) :=
  fun _ _ ↦ const_lt_const.2

end Function

section apply
variable {β : ι → Type*} [∀ i, Preorder (β i)] [Preorder α] {f : α → ∀ i, β i}

/-
**monotone_iff_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monotone_iff_apply₂ : Monotone f ↔ ∀ i, Monotone (f · i) := by
  simp [Monotone, Pi.le_def, @forall_comm ι]
/-
**antitone_iff_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma antitone_iff_apply₂ : Antitone f ↔ ∀ i, Antitone (f · i) := by
  simp [Antitone, Pi.le_def, @forall_comm ι]

alias ⟨Monotone.apply₂, Monotone.of_apply₂⟩ := monotone_iff_apply₂
alias ⟨Antitone.apply₂, Antitone.of_apply₂⟩ := antitone_iff_apply₂

end apply

