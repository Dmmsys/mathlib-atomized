/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
public import Mathlib.Algebra.DirectSum.Module

/-!
# Tensor products of direct sums

This file shows that taking `PiTensorProduct`s commutes with taking `DirectSum`s in all arguments.

## Main results

* `ofDirectSumEquiv`: the linear equivalence between a `PiTensorProduct` of `DirectSum`s
  and the `DirectSum` of the `PiTensorProduct`s.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct DirectSum TensorProduct

variable {R ι : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]

open scoped Classical in
/-- The n-ary tensor product distributes over m-ary direct sums. -/
/-
**PiTensorProduct.ofDirectSumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：ofDirectSumEquiv [Finite ι] : (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i
, κ i, ⨂[R] i, M i (p i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-ary tensor product distributes over m-ary direct sums.
-/
noncomputable def ofDirectSumEquiv [Finite ι] :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  have : Fintype ι := Fintype.ofFinite ι
  ofDFinsuppEquiv

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PiTensorProduct.ofDirectSumEquiv_tprod_lof** 是 Mathlib 中的一个定理，位于命名空间 `PiTensor
Product`。
形式化陈述：ofDirectSumEquiv_tprod_lof [Fintype ι] [(i : ι) -> DecidableEq (κ i)] (p :
 Π i, κ i) (x : Π i, M i (p i)) : ofDirectSumEquiv (⨂ₜ[R] i, DirectSum.lof R _ _
 (p i) (x i)) = DirectSum.lof R _ _ p (⨂ₜ[R] i, x i)
参数：i : ι；κ i；p : Π i, κ i；x : Π i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.ofDirectSumEquiv.eq_1`：∀ {R : Type u_1} {ι : Type u_2} {
κ : ι → Type u_3} {M : (i : ι) → κ i → Type u_4} [inst : CommSemiring R]   [inst
_1 : (i : ι) → (j : κ i) → …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `PiTensorProduct.ofDFinsuppEquiv_tprod_single`：ofDFinsuppEquiv_tprod_sing
le (p : Π i, κ i) (x : Π i, M i (p i)) : ofDFinsuppEquiv (⨂ₜ[R] i, DFinsupp.sing
le (p i) (x i)) = DFinsupp.single …
-/
theorem ofDirectSumEquiv_tprod_lof [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDirectSumEquiv (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) =
      DirectSum.lof R _ _ p (⨂ₜ[R] i, x i) := by
  classical
  rw [ofDirectSumEquiv]
  convert! ofDFinsuppEquiv_tprod_single p x

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PiTensorProduct.ofDirectSumEquiv_symm_lof_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiT
ensorProduct`。
形式化陈述：ofDirectSumEquiv_symm_lof_tprod [Fintype ι] [(i : ι) -> DecidableEq (κ i)]
 (p : Π i, κ i) (x : Π i, M i (p i)) : ofDirectSumEquiv.symm (DirectSum.lof R _ 
_ p (tprod R x)) = (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i))
参数：i : ι；κ i；p : Π i, κ i；x : Π i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.ofDirectSumEquiv.eq_1`：∀ {R : Type u_1} {ι : Type u_2} {
κ : ι → Type u_3} {M : (i : ι) → κ i → Type u_4} [inst : CommSemiring R]   [inst
_1 : (i : ι) → (j : κ i) → …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `PiTensorProduct.ofDFinsuppEquiv_symm_single_tprod`：ofDFinsuppEquiv_symm_
single_tprod (p : Π i, κ i) (x : Π i, M i (p i)) : ofDFinsuppEquiv.symm (DFinsup
p.single p (tprod R x)) = (⨂ₜ[R] i, DFi…
-/
theorem ofDirectSumEquiv_symm_lof_tprod [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDirectSumEquiv.symm (DirectSum.lof R _ _ p (tprod R x)) =
      (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) := by
  classical
  rw [ofDirectSumEquiv]
  convert! ofDFinsuppEquiv_symm_single_tprod p x

@[simp]
/-
**PiTensorProduct.ofDirectSumEquiv_tprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTens
orProduct`。
形式化陈述：ofDirectSumEquiv_tprod_apply [Finite ι] (x : Π i, ⨁ j, M i j) (p : Π i, κ 
i) : ofDirectSumEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i)
参数：x : Π i, ⨁ j, M i j；p : Π i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ofDFinsuppEquiv_tprod_apply`：ofDFinsuppEquiv_tprod_apply
 (x : Π i, Π₀ j, M i j) (p : Π i, κ i) : ofDFinsuppEquiv (tprod R x) p = ⨂ₜ[R] i
, x i (p i)
-/
theorem ofDirectSumEquiv_tprod_apply [Finite ι]
    (x : Π i, ⨁ j, M i j) (p : Π i, κ i) :
    ofDirectSumEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  have : Fintype ι := Fintype.ofFinite ι
  convert! ofDFinsuppEquiv_tprod_apply _ _

end PiTensorProduct

