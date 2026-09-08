/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists MulAction IsOrderedMonoid Field

open Function
open scoped Pointwise

variable {α : Type*}

namespace Set

/-- `Set α` has distributive negation if `α` has. -/
@[instance_reducible]
/-
**Set.hasDistribNeg** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → [inst : Mul α] → [HasDistribNeg α] → HasDistribNeg (Set α
)
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set α` has distributive negation if `α` has.
-/
protected noncomputable def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) where
  __ := Set.involutiveNeg
  neg_mul _ _ := by simp_rw [← image_neg_eq_neg]; exact image2_image_left_comm neg_mul
  mul_neg _ _ := by simp_rw [← image_neg_eq_neg]; exact image_image2_right_comm mul_neg

scoped[Pointwise] attribute [instance] Set.hasDistribNeg

section Distrib
variable [Distrib α] (s t u : Set α)

/-!
Note that `Set α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/

/-
**Set.mul_add_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mul_add_subset : s * (t + u) subseteq s * t + s * u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_distrib_subset_left`：image2_distrib_subset_left {f : α -> δ -
> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' ->
 ε} (h_distrib : for…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R

--- 原说明 ---
Note that `Set α` is not a `Distrib` because `s * t + s * u` has cross terms tha
t `s * (t + u)`
lacks.
-/
lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add
/-
**Set.add_mul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：add_mul_subset : (s + t) * u subseteq s * u + t * u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_distrib_subset_right`：image2_distrib_subset_right {f : δ -> γ
 -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' 
-> ε} (h_distrib : fo…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul

end Distrib
end Set

