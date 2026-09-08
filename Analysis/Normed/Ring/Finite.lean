/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Analysis.Normed.Ring.Basic


/-!
# Finite order elements in normed rings.

A finite order element in a normed ring has norm 1.

The values of additive characters on finite cancellative monoids have norm 1.

-/

public section

variable {α β : Type*}

section NormedRing
variable [NormedRing α] [NormMulClass α] [NormOneClass α] {a : α}

/-
**IsOfFinOrder.norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsOfFinOrder`。
形式化陈述：∀ {α : Type u_1} [inst : NormedRing α] [NormMulClass α] [NormOneClass α] {
a : α}, IsOfFinOrder a → ‖a‖ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.eq_one`：∀ {G : Type u_1} [inst : Semiring G] [inst_1 : Line
arOrder G] [IsStrictOrderedRing G] {a : G},   0 ≤ a → IsOfFinOrder a → a = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MonoidHom.isOfFinOrder`：MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) 
{x : G} (h : IsOfFinOrder x) : IsOfFinOrder f x
-/
protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.isOfFinOrder ha).eq_one <| norm_nonneg _
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one
/-
**AddChar.norm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {α : Type u_1} [inst : NormedRing α] [NormMulClass α] [NormOneClass α] {
G : Type u_3} [inst_3 : AddLeftCancelMonoid G]   [Finite G] (ψ : AddChar G α) (x
 : G), ‖ψ x‖ = 1
参数：ψ : AddChar G α；x : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOfFinOrder.norm_eq_one`：∀ {α : Type u_1} [inst : NormedRing α] [NormMu
lClass α] [NormOneClass α] {a : α}, IsOfFinOrder a → ‖a‖ = 1
· 使用定理 `MonoidHom.isOfFinOrder`：MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) 
{x : G} (h : IsOfFinOrder x) : IsOfFinOrder f x
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `instFiniteMultiplicative`：∀ {α : Type u} [Finite α], Finite (Multiplicat
ive α)
-/
@[simp] lemma AddChar.norm_apply {G : Type*} [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
    (x : G) : ‖ψ x‖ = 1 := (ψ.toMonoidHom.isOfFinOrder <| isOfFinOrder_of_finite _).norm_eq_one

end NormedRing

