/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Vertex.HVertexOperator
public import Mathlib.Data.Int.Interval

/-!
# Vertex operators

In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
* `VertexOperator` is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* `VertexOperator.ncoeff` is the coefficient of a vertex operator under normalized indexing.

## TODO
* `HasseDerivative` : A divided-power derivative.
* `Locality` : A weak form of commutativity.
* `Residue products` : A family of products on `VertexOperator R V` parametrized by integers.

## References
* [G. Mason, *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
-/

@[expose] public section

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of the heterogeneous
case. -/
/-
**VertexOperator** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] [Modu
le R V]
参数：R : Type*；V : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-m
odule `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of t
he heterogeneous
case.
-/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := HVertexOperator ℤ R V V

namespace VertexOperator

open HVertexOperator

@[ext]
/-
**VertexOperator.ext** 是 Mathlib 中的一个定理，位于命名空间 `VertexOperator`。
形式化陈述：ext (A B : VertexOperator R V) (h : forall v : V, A v = B v) : A = B
参数：A B : VertexOperator R V；h : forall v : V, A v = B v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem ext (A B : VertexOperator R V) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a vertex operator under normalized indexing. -/
/-
**VertexOperator.ncoeff** 是 Mathlib 中的一个定义，位于命名空间 `VertexOperator`。
形式化陈述：ncoeff : VertexOperator R V ->ₗ[R] Int -> Module.End R V where toFun A n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficient of a vertex operator under normalized indexing.
-/
def ncoeff : VertexOperator R V →ₗ[R] ℤ → Module.End R V where
  toFun A n := HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
/-
**VertexOperator.ncoeff_apply** 是 Mathlib 中的一个定理，位于命名空间 `VertexOperator`。
形式化陈述：ncoeff_apply (A : VertexOperator R V) (n : Int) : ncoeff A n = coeff A (-n
 - 1)
参数：A : VertexOperator R V；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ncoeff_apply (A : VertexOperator R V) (n : ℤ) : ncoeff A n = coeff A (-n - 1) :=
  rfl

/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

@[simp]
/-
**VertexOperator.coeff_eq_ncoeff** 是 Mathlib 中的一个定理，位于命名空间 `VertexOperator`。
形式化陈述：coeff_eq_ncoeff (A : VertexOperator R V) (n : Int) : HVertexOperator.coeff
 A n = A[[-n - 1]]
参数：A : VertexOperator R V；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VertexOperator.ncoeff_apply`：ncoeff_apply (A : VertexOperator R V) (n : 
Int) : ncoeff A n = coeff A (-n - 1)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Int.sub_neg`：∀ (a b : ℤ), a - -b = a + b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A[[-n - 1]] := by
  rw [ncoeff_apply, neg_sub, Int.sub_neg, add_sub_cancel_left]
/-
**VertexOperator.ncoeff_eq_zero_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `VertexOpe
rator`。
形式化陈述：ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : Int) (x : V) (h :
 -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A[[n]]) x = 0
参数：A : VertexOperator R V；n : Int；x : V；h : -n - 1 < HahnSeries.order ((HahnModu
le.of R).symm (A x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_order`：coeff_eq_zero_of_lt_order {x : R⟦Γ
⟧} {i : Γ} (hi : i < x.order) : x.coeff i = 0
-/
theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A[[n]]) x = 0 := by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h
/-
**VertexOperator.coeff_eq_zero_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `VertexOper
ator`。
形式化陈述：coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : Int) (x : V) (h : 
n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0
参数：A : VertexOperator R V；n : Int；x : V；h : n < HahnSeries.order ((HahnModule.of
 R).symm (A x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VertexOperator.coeff_eq_ncoeff`：coeff_eq_ncoeff (A : VertexOperator R V)
 (n : Int) : HVertexOperator.coeff A n = A[[-n - 1]]
· 使用定理 `VertexOperator.ncoeff_eq_zero_of_lt_order`：ncoeff_eq_zero_of_lt_order (A
 : VertexOperator R V) (n : Int) (x : V) (h : -n - 1 < HahnSeries.order ((HahnMo
dule.of R).symm (A x))) : (A[[n…
-/
theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0 := by
  rw [coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  lia

/-- Given an endomorphism-valued function on integers satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
/-
**VertexOperator.of_coeff** 是 Mathlib 中的一个定义，位于命名空间 `VertexOperator`。
形式化陈述：of_coeff (f : Int -> Module.End R V) (hf : forall x, BddBelow (Function.su
pport fun y => f y x)) : VertexOperator R V
参数：f : Int -> Module.End R V；hf : forall x, BddBelow (Function.support fun y => 
f y x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an endomorphism-valued function on integers satisfying a pointwise bounded
-pole condition,
we produce a vertex operator.
-/
noncomputable def of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) : VertexOperator R V :=
  HVertexOperator.of_coeff f fun x ↦ (BddBelow.isWF (hf x)).isPWO

@[simp]
/-
**VertexOperator.of_coeff_apply_coeff** 是 Mathlib 中的一个定理，位于命名空间 `VertexOperator`
。
形式化陈述：of_coeff_apply_coeff (f : Int -> Module.End R V) (hf : forall x, BddBelow 
(Function.support fun y => f y x)) (x : V) (n : Int) : ((HahnModule.of R).symm (
(of_coeff f hf) x)).coeff n = (f n) x
参数：f : Int -> Module.End R V；hf : forall x, BddBelow (Function.support fun y => 
f y x)；x : V；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem of_coeff_apply_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) (x : V) (n : ℤ) :
    ((HahnModule.of R).symm ((of_coeff f hf) x)).coeff n = (f n) x := by
  rfl

@[simp]
/-
**VertexOperator.ncoeff_of_coeff** 是 Mathlib 中的一个定理，位于命名空间 `VertexOperator`。
形式化陈述：ncoeff_of_coeff (f : Int -> Module.End R V) (hf : forall x, BddBelow (Func
tion.support fun y => f y x)) (n : Int) : (of_coeff f hf)[[n]] = f (-n - 1)
参数：f : Int -> Module.End R V；hf : forall x, BddBelow (Function.support fun y => 
f y x)；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VertexOperator.ncoeff_apply`：ncoeff_apply (A : VertexOperator R V) (n : 
Int) : ncoeff A n = coeff A (-n - 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HVertexOperator.coeff_apply_apply`：∀ {Γ : Type u_1} [inst : PartialOrder
 Γ] {R : Type u_2} {V : Type u_3} {W : Type u_4} [inst_1 : CommRing R]   [inst_2
 : AddCommGroup V] [ins…
· 使用定理 `VertexOperator.of_coeff_apply_coeff`：of_coeff_apply_coeff (f : Int -> Mo
dule.End R V) (hf : forall x, BddBelow (Function.support fun y => f y x)) (x : V
) (n : Int) : ((HahnModul…
-/
theorem ncoeff_of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) (n : ℤ) :
    (of_coeff f hf)[[n]] = f (-n - 1) := by
  ext v
  rw [ncoeff_apply, coeff_apply_apply, of_coeff_apply_coeff]

end VertexOperator

