/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Operations

/-!
# Fixed points of a self-map

In this file we define the set `Function.fixedPoints` of fixed points of a function `f : α → α`.
The related predicate `IsFixedPt` is defined in `Mathlib.Logic.Function.Defs`.

## Tags

fixed point
-/

@[expose] public section

namespace Function

variable {α : Type*} {x : α} {f g : α → α}

/-- The set of fixed points of a map `f : α → α`. -/
/-
**Function.fixedPoints** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：fixedPoints (f : α -> α) : Set α
参数：f : α -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of fixed points of a map `f : α → α`.
-/
def fixedPoints (f : α → α) : Set α :=
  { x : α | IsFixedPt f x }
/-
**Function.fixedPoints.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Function.fixedPoints
`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (f : α → α) → (x : α) → Decidable (x ∈ 
Function.fixedPoints f)
参数：f : α → α；x : α；x ∈ Function.fixedPoints f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fixedPoints.decidable [DecidableEq α] (f : α → α) (x : α) :
    Decidable (x ∈ fixedPoints f) :=
  IsFixedPt.decidable

@[simp]
/-
**Function.mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mem_fixedPoints : x in fixedPoints f ↔ IsFixedPt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fixedPoints : x ∈ fixedPoints f ↔ IsFixedPt f x :=
  .rfl
/-
**Function.mem_fixedPoints_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mem_fixedPoints_iff {α : Type*} {f : α -> α} {x : α} : x in fixedPoints f 
↔ f x = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fixedPoints_iff {α : Type*} {f : α → α} {x : α} : x ∈ fixedPoints f ↔ f x = x :=
  .rfl

@[simp]
/-
**Function.fixedPoints_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fixedPoints_id : fixedPoints (@id α) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Function.isFixedPt_id`：isFixedPt_id (x : α) : IsFixedPt id x
-/
theorem fixedPoints_id : fixedPoints (@id α) = Set.univ :=
  Set.ext fun _ => by simpa using isFixedPt_id _

@[simp]
/-
**Function.inter_subset_fixedPoints_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：inter_subset_fixedPoints_comp : fixedPoints f inter fixedPoints g subseteq
 fixedPoints (f ∘ g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem inter_subset_fixedPoints_comp : fixedPoints f ∩ fixedPoints g ⊆ fixedPoints (f ∘ g) := by
  rintro x ⟨hf, hg⟩
  rw [mem_fixedPoints_iff] at *
  rw [comp_apply, hg, hf]
/-
**Function.fixedPoints_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fixedPoints_subset_range : fixedPoints f subseteq Set.range f
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixedPoints_subset_range : fixedPoints f ⊆ Set.range f := fun x hx => ⟨x, hx⟩

end Function

