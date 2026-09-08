/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of support
-/

public section

assert_not_exists Monoid

namespace Function
variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
/-
**Function.mulSupport_along_fiber_finite_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Fu
nction`。
形式化陈述：mulSupport_along_fiber_finite_of_finite (f : α × β -> γ) (a : α) (h : HasF
initeMulSupport f) : HasFiniteMulSupport fun b => f (a, b)
参数：f : α × β -> γ；a : α；h : HasFiniteMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用引理 `Function.mulSupport_along_fiber_subset`：mulSupport_along_fiber_subset (f
 : ι × κ -> M) (i : ι) : (mulSupport fun j => f (i, j)) subseteq (mulSupport f).
image Prod.snd
-/
lemma mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun b ↦ f (a, b) :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end Function

