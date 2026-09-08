/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinality of monoid algebras

This file computes the cardinality of `R[M]` in terms of `#R` and `#M`.
-/

public section

open Cardinal Fintype

universe u v
variable (R M : Type u) (M' : Type v) [Semiring R]

namespace MonoidAlgebra

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.cardinalMk_eq_lift_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `MonoidA
lgebra`。
形式化陈述：cardinalMk_eq_lift_of_fintype [Fintype M'] : #R[M'] = lift.{v} #R ^ card M
'
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
· 使用定理 `Cardinal.mk_finsupp_lift_of_fintype`：mk_finsupp_lift_of_fintype (α : Typ
e u) (β : Type v) [Fintype α] [Zero β] : #(α ->₀ β) = lift.{u} #β ^ Fintype.card
 α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_eq_lift_of_fintype [Fintype M'] : #R[M'] = lift.{v} #R ^ card M' := by
  simp [coeffEquiv.cardinal_eq]

@[deprecated (since := "2026-03-26")]
alias cardinalMk_lift_of_fintype := cardinalMk_eq_lift_of_fintype

@[to_additive]
/-
**MonoidAlgebra.cardinalMk_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：cardinalMk_of_fintype [Fintype M] : #R[M] = #R ^ card M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.cardinalMk_eq_lift_of_fintype`：cardinalMk_eq_lift_of_finty
pe [Fintype M'] : #R[M'] = lift.{v} #R ^ card M'
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_of_fintype [Fintype M] : #R[M] = #R ^ card M := by simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 `Mo
noidAlgebra`。
形式化陈述：cardinalMk_eq_max_lift_of_infinite [Infinite M'] [Nontrivial R] : #R[M'] =
 max (lift.{v} #R) (lift.{u} #M')
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
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite`：mk_finsupp_lift_of_infinite (α : T
ype u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_eq_max_lift_of_infinite [Infinite M'] [Nontrivial R] :
    #R[M'] = max (lift.{v} #R) (lift.{u} #M') := by simp [coeffEquiv.cardinal_eq, max_comm]

@[deprecated (since := "2026-03-26")]
alias cardinalMk_lift_of_infinite := cardinalMk_eq_max_lift_of_infinite

@[to_additive]
/-
**MonoidAlgebra.cardinalMk_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：cardinalMk_of_infinite [Infinite M] [Nontrivial R] : #R[M] = max #R #M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`：cardinalMk_eq_max_lift
_of_infinite [Infinite M'] [Nontrivial R] : #R[M'] = max (lift.{v} #R) (lift.{u}
 #M')
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_of_infinite [Infinite M] [Nontrivial R] : #R[M] = max #R #M := by simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite'** 是 Mathlib 中的一个引理，位于命名空间 `M
onoidAlgebra`。
形式化陈述：cardinalMk_eq_max_lift_of_infinite' [Nonempty M'] [Infinite R] : #R[M'] = 
max (lift.{v} #R) (lift.{u} #M')
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
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite'`：mk_finsupp_lift_of_infinite' (α :
 Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_eq_max_lift_of_infinite' [Nonempty M'] [Infinite R] :
    #R[M'] = max (lift.{v} #R) (lift.{u} #M') := by simp [coeffEquiv.cardinal_eq, max_comm]

@[deprecated (since := "2026-03-26")]
alias cardinalMk_lift_of_infinite' := cardinalMk_eq_max_lift_of_infinite'

@[to_additive]
/-
**MonoidAlgebra.cardinalMk_of_infinite'** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：cardinalMk_of_infinite' [Nonempty M] [Infinite R] : #R[M] = max #R #M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite'`：cardinalMk_eq_max_lif
t_of_infinite' [Nonempty M'] [Infinite R] : #R[M'] = max (lift.{v} #R) (lift.{u}
 #M')
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cardinalMk_of_infinite' [Nonempty M] [Infinite R] : #R[M] = max #R #M := by simp

end MonoidAlgebra

