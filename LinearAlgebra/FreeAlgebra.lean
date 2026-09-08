/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Linear algebra properties of `FreeAlgebra R X`

This file provides a `FreeMonoid X` basis on the `FreeAlgebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `List X`
-/

@[expose] public section

open Module

universe u v

namespace FreeAlgebra

variable (R : Type u) (X : Type v)

section
variable [CommSemiring R]

/-- The `FreeMonoid X` basis on the `FreeAlgebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
-- @[simps]
/-
**FreeAlgebra.basisFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra`。
形式化陈述：basisFreeMonoid : Basis (FreeMonoid X) R (FreeAlgebra R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def basisFreeMonoid : Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans <| MonoidAlgebra.coeffLinearEquiv _).symm
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R (FreeAlgebra R X) :=
  .of_equiv equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv

end

/-
**FreeAlgebra.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：rank_eq [CommRing R] [Nontrivial R] : Module.rank R (FreeAlgebra R X) = Ca
rdinal.lift.{u} (Cardinal.mk (List X))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.mk_eq_rank'`：mk_eq_rank'.{m} (v : Basis ι R M) : Cardinal.l
ift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M)
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `FreeMonoid.eq_1`：∀ (α : Type u_6), FreeMonoid α = List α
-/
theorem rank_eq [CommRing R] [Nontrivial R] :
    Module.rank R (FreeAlgebra R X) = Cardinal.lift.{u} (Cardinal.mk (List X)) := by
  rw [← (Basis.mk_eq_rank'.{_, _, _, u} (basisFreeMonoid R X)).trans (Cardinal.lift_id _),
    Cardinal.lift_umax.{v, u}, FreeMonoid]

end FreeAlgebra

open Cardinal

/-
**Algebra.rank_adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.rank_adjoin_le {R : Type u} {S : Type v} [CommRing R] [Ring S] [Al
gebra R S] (s : Set S) : Module.rank R (adjoin R s) <= max #s ℵ₀
参数：s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_range_freeAlgebra_lift`：∀ (R : Type u_1) [inst : CommS
emiring R] {A : Type u_3} [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set 
A),   Algebra.adjoin R s = ((F…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.one_le_aleph0`：one_le_aleph0 : 1 <= ℵ₀
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
· 使用定理 `FreeAlgebra.rank_eq`：rank_eq [CommRing R] [Nontrivial R] : Module.rank R
 (FreeAlgebra R X) = Cardinal.lift.{u} (Cardinal.mk (List X))
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Cardinal.mk_list_le_max`：mk_list_le_max (α : Type u) : #(List α) <= max 
ℵ₀ #α
-/
theorem Algebra.rank_adjoin_le {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
    (s : Set S) : Module.rank R (adjoin R s) ≤ max #s ℵ₀ := by
  rw [adjoin_eq_range_freeAlgebra_lift]
  cases subsingleton_or_nontrivial R
  · rw [rank_subsingleton]; exact one_le_aleph0.trans (le_max_right _ _)
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le (FreeAlgebra.lift R ((↑) : s → S)).toLinearMap).trans ?_
  rw [FreeAlgebra.rank_eq, lift_id'.{v, u}, lift_umax.{v, u}, lift_le, max_comm]
  exact mk_list_le_max _
