/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Pointwise.Set
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists MulAction

open scoped Pointwise

namespace Finset
variable {α β : Type*}

/-- `Finset α` has distributive negation if `α` has. -/
@[instance_reducible]
/-
**Finset.distribNeg** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → [inst : DecidableEq α] → [inst_1 : Mul α] → [HasDistribNe
g α] → HasDistribNeg (Finset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t

--- 原说明 ---
`Finset α` has distributive negation if `α` has.
-/
protected noncomputable def distribNeg [DecidableEq α] [Mul α] [HasDistribNeg α] :
    HasDistribNeg (Finset α) :=
  coe_injective.hasDistribNeg _ coe_neg coe_mul

scoped[Pointwise] attribute [instance] Finset.distribNeg

section Distrib
variable [DecidableEq α] [Distrib α] (s t u : Finset α)

/-!
Note that `Finset α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : Finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : Finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/

/-
**Finset.mul_add_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_add_subset : s * (t + u) subseteq s * t + s * u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_distrib_subset_left`：image₂_distrib_subset_left {γ : Type*
} {u : Finset γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α
 -> γ -> γ'} {g' : β' -…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R

--- 原说明 ---
Note that `Finset α` is not a `Distrib` because `s * t + s * u` has cross terms 
that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : Finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : Finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/
lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image₂_distrib_subset_left mul_add
/-
**Finset.add_mul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：add_mul_subset : (s + t) * u subseteq s * u + t * u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_distrib_subset_right`：image₂_distrib_subset_right {γ : Typ
e*} {u : Finset γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ :
 β -> γ -> β'} {g' : α' …
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image₂_distrib_subset_right add_mul

end Distrib
end Finset

