/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinality of Polynomial Ring

The result in this file is that the cardinality of `R[X]` is at most the maximum
of `#R` and `ℵ₀`.
-/

public section

open Cardinal Fintype

universe u v
variable {R : Type u} {M : Type v} [Semiring R]

namespace Polynomial

@[simp]
/-
**Polynomial.cardinalMk_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cardinalMk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : #(R[X]) = max
 #R ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `AddMonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`：∀ (R : Type u) (M' 
: Type v) [inst : Semiring R] [Infinite M'] [Nontrivial R],   Cardinal.mk (AddMo
noidAlgebra R M') =     max (Cardinal.lif…
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : #(R[X]) = max #R ℵ₀ := by
  simp [(toFinsuppIso R).toEquiv.cardinal_eq]
/-
**Polynomial.cardinalMk_le_max** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cardinalMk_le_max {R : Type u} [Semiring R] : #(R[X]) <= max #R ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `Cardinal.one_le_aleph0`：one_le_aleph0 : 1 <= ℵ₀
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Polynomial.cardinalMk_eq_max`：cardinalMk_eq_max {R : Type u} [Semiring R
] [Nontrivial R] : #(R[X]) = max #R ℵ₀
-/
lemma cardinalMk_le_max {R : Type u} [Semiring R] : #(R[X]) ≤ max #R ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact cardinalMk_eq_max.le

end Polynomial

