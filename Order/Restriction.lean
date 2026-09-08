/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Restriction of a function indexed by a preorder

Given a preorder `α` and dependent function `f : (i : α) → π i` and `a : α`, one might want
to consider the restriction of `f` to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe a f`.
Similarly, if we have `a b : α`, `hab : a ≤ b` and `f : (i : ↑(Set.Iic b)) → π ↑i`,
one might want to restrict it to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe₂ hab f`.

We also provide versions where the intervals are seen as finite sets, see `Preorder.frestrictLe`
and `Preorder.frestrictLe₂`.

## Main definitions
* `Preorder.restrictLe a f`: Restricts the function `f` to the variables indexed by elements `≤ a`.
-/

@[expose] public section

namespace Preorder

variable {α : Type*} [Preorder α] {π : α → Type*}

section Set

open Set

/-- Restrict domain of a function `f` indexed by `α` to elements `≤ a`. -/
/-
**Preorder.restrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：restrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict domain of a function `f` indexed by `α` to elements `≤ a`.
-/
def restrictLe (a : α) := (Iic a).domRestrict (π := π)

@[simp]
/-
**Preorder.restrictLe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：restrictLe_apply (a : α) (f : (a : α) -> π a) (i : Iic a) : restrictLe a f
 i = f i
参数：a : α；f : (a : α) -> π a；i : Iic a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictLe_apply (a : α) (f : (a : α) → π a) (i : Iic a) : restrictLe a f i = f i := rfl

/-- If a function `f` indexed by `α` is restricted to elements `≤ π`, and `a ≤ b`,
this is the restriction to elements `≤ a`. -/
/-
**Preorder.restrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：restrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` indexed by `α` is restricted to elements `≤ π`, and `a ≤ b`,
this is the restriction to elements `≤ a`.
-/
def restrictLe₂ {a b : α} (hab : a ≤ b) := Set.domRestrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
/-
**Preorder.restrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：restrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictLe₂_apply {a b : α} (hab : a ≤ b) (f : (i : Iic b) → π i) (i : Iic a) :
    restrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl
/-
**Preorder.restrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：restrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictLe₂_comp_restrictLe {a b : α} (hab : a ≤ b) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe b) = restrictLe a := rfl
/-
**Preorder.restrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：restrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictLe₂_comp_restrictLe₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe₂ hbc) = restrictLe₂ (hab.trans hbc) := rfl
/-
**Preorder.dependsOn_restrictLe** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：dependsOn_restrictLe (a : α) : DependsOn (restrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.dependsOn_domRestrict`：Set.dependsOn_domRestrict (s : Set ι) : Depen
dsOn (s.domRestrict (π
-/
lemma dependsOn_restrictLe (a : α) : DependsOn (restrictLe (π := π) a) (Iic a) :=
  (Iic a).dependsOn_domRestrict

end Set

section Finset

variable [LocallyFiniteOrderBot α]

open Finset

/-- Restrict domain of a function `f` indexed by `α` to elements `≤ a`, seen as a finite set. -/
/-
**Preorder.frestrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：frestrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict domain of a function `f` indexed by `α` to elements `≤ a`, seen as a fi
nite set.
-/
def frestrictLe (a : α) := (Iic a).restrict (π := π)

@[simp]
/-
**Preorder.frestrictLe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：frestrictLe_apply (a : α) (f : (a : α) -> π a) (i : Iic a) : frestrictLe a
 f i = f i
参数：a : α；f : (a : α) -> π a；i : Iic a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma frestrictLe_apply (a : α) (f : (a : α) → π a) (i : Iic a) : frestrictLe a f i = f i := rfl

/-- If a function `f` indexed by `α` is restricted to elements `≤ b`, and `a ≤ b`,
this is the restriction to elements `≤ b`. Intervals are seen as finite sets. -/
/-
**Preorder.frestrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：frestrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` indexed by `α` is restricted to elements `≤ b`, and `a ≤ b`,
this is the restriction to elements `≤ b`. Intervals are seen as finite sets.
-/
def frestrictLe₂ {a b : α} (hab : a ≤ b) := restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
/-
**Preorder.frestrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：frestrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma frestrictLe₂_apply {a b : α} (hab : a ≤ b) (f : (i : Iic b) → π i) (i : Iic a) :
    frestrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl
/-
**Preorder.frestrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：frestrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem frestrictLe₂_comp_frestrictLe {a b : α} (hab : a ≤ b) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe b) = frestrictLe a := rfl
/-
**Preorder.frestrictLe** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：frestrictLe (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem frestrictLe₂_comp_frestrictLe₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe₂ hbc) = frestrictLe₂ (hab.trans hbc) := rfl
/-
**Preorder.piCongrLeft_comp_restrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：piCongrLeft_comp_restrictLe {a : α} : ((Equiv.IicFinsetSet a).symm.piCongr
Left (fun i : Iic a => π i)) ∘ (restrictLe a) = frestrictLe a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem piCongrLeft_comp_restrictLe {a : α} :
    ((Equiv.IicFinsetSet a).symm.piCongrLeft (fun i : Iic a ↦ π i)) ∘ (restrictLe a) =
    frestrictLe a := rfl
/-
**Preorder.piCongrLeft_comp_frestrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：piCongrLeft_comp_frestrictLe {a : α} : ((Equiv.IicFinsetSet a).piCongrLeft
 (fun i : Set.Iic a => π i)) ∘ (frestrictLe a) = restrictLe a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrLeft_comp_frestrictLe {a : α} :
    ((Equiv.IicFinsetSet a).piCongrLeft (fun i : Set.Iic a ↦ π i)) ∘ (frestrictLe a) =
    restrictLe a := rfl

section updateFinset

open Function

variable [DecidableEq α]

/-
**Preorder.frestrictLe_updateFinset_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：frestrictLe_updateFinset_of_le {a b : α} (hab : a <= b) (x : Π c, π c) (y 
: Π c : Iic b, π c) : frestrictLe a (updateFinset x _ y) = frestrictLe₂ hab y
参数：hab : a <= b；x : Π c, π c；y : Π c : Iic b, π c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.restrict_updateFinset_of_subset`：restrict_updateFinset_of_subse
t {s t : Finset ι} (hst : s subseteq t) (x : Π i, π i) (y : Π i : t, π i) : s.re
strict (updateFinset x t y) = …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
-/
lemma frestrictLe_updateFinset_of_le {a b : α} (hab : a ≤ b) (x : Π c, π c) (y : Π c : Iic b, π c) :
    frestrictLe a (updateFinset x _ y) = frestrictLe₂ hab y :=
  restrict_updateFinset_of_subset (Iic_subset_Iic.2 hab) ..
/-
**Preorder.frestrictLe_updateFinset** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：frestrictLe_updateFinset {a : α} (x : Π a, π a) (y : Π b : Iic a, π b) : f
restrictLe a (updateFinset x _ y) = y
参数：x : Π a, π a；y : Π b : Iic a, π b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.restrict_updateFinset`：restrict_updateFinset {s : Finset ι} (x 
: Π i, π i) (y : Π i : s, π i) : s.restrict (updateFinset x s y) = y
-/
lemma frestrictLe_updateFinset {a : α} (x : Π a, π a) (y : Π b : Iic a, π b) :
    frestrictLe a (updateFinset x _ y) = y := restrict_updateFinset ..

@[simp]
/-
**Preorder.updateFinset_frestrictLe** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：updateFinset_frestrictLe (a : α) (x : Π a, π a) : updateFinset x _ (frestr
ictLe a x) = x
参数：a : α；x : Π a, π a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.updateFinset_restrict`：updateFinset_restrict {s : Finset ι} (x 
: Π i, π i) : updateFinset x s (s.restrict x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma updateFinset_frestrictLe (a : α) (x : Π a, π a) : updateFinset x _ (frestrictLe a x) = x := by
  simp [frestrictLe]

end updateFinset

/-
**Preorder.dependsOn_frestrictLe** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：dependsOn_frestrictLe (a : α) : DependsOn (frestrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.dependsOn_restrict`：dependsOn_restrict (s : Finset ι) : DependsOn
 (s.restrict (π
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
-/
lemma dependsOn_frestrictLe (a : α) : DependsOn (frestrictLe (π := π) a) (Set.Iic a) :=
  coe_Iic a ▸ (Finset.Iic a).dependsOn_restrict

end Finset

end Preorder

