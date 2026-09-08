/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Group.Int.Units

/-!
# Basic lemmas for `ℤˣ`.

This file contains lemmas on the units of `ℤ`.

## Main results

* `Int.units_eq_one_or`: the invertible integers are 1 and -1.

See note [foundational algebra order theory].
-/

public section

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/-! #### Units -/

/-
**Int.units_eq_one_or** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
参数：u : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.isUnit_eq_one_or`：isUnit_eq_one_or (hu : IsUnit u) : u = 1 ∨ u = -1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u

--- 原说明 ---
#### Units
-/
lemma units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using! isUnit_eq_one_or u.isUnit
/-
**Int.units_ne_iff_eq_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：units_ne_iff_eq_neg {u v : Intˣ} : u != v ↔ u = -v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.isUnit_ne_iff_eq_neg`：isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsU
nit v) : u != v ↔ u = -v
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma units_ne_iff_eq_neg {u v : ℤˣ} : u ≠ v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using! isUnit_ne_iff_eq_neg u.isUnit v.isUnit

end Int

