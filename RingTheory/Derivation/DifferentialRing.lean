/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Differential and Algebras

This file defines derivations from a commutative ring to itself as a typeclass, which lets us
use the x′ notation for the derivative of x.
-/

@[expose] public section

/-- A derivation from a ring to itself, as a typeclass. -/
@[ext]
/-
**Differential** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommRing R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A derivation from a ring to itself, as a typeclass.
-/
class Differential (R : Type*) [CommRing R] where
  /-- The `Derivation` associated with the ring. -/
  deriv : Derivation ℤ R R

@[inherit_doc]
scoped[Differential] postfix:max "′" => Differential.deriv

open scoped Differential

open Lean PrettyPrinter Delaborator SubExpr in
/--
A delaborator for the x′ notation. This is required because it's not direct function application,
so the default delaborator doesn't work.
-/
@[app_delab DFunLike.coe]
meta def delabDeriv : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``DFunLike.coe 6
  guard <| (e.getArg!' 4).isAppOf' ``Differential.deriv
  let arg ← withAppArg delab
  `($arg′)

/--
A differential algebra is an `Algebra` where the derivation commutes with `algebraMap`.
-/
/-
**DifferentialAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) →   (B : Type u_2) →     [inst : CommRing A] → [inst_1 : Co
mmRing B] → [Algebra A B] → [Differential A] → [Differential B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A differential algebra is an `Algebra` where the derivation commutes with `algeb
raMap`.
-/
class DifferentialAlgebra (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Differential A] [Differential B] : Prop where
  deriv_algebraMap : ∀ a : A, (algebraMap A B a)′ = algebraMap A B a′

export DifferentialAlgebra (deriv_algebraMap)

@[norm_cast]
/-
**algebraMap.coe_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：algebraMap.coe_deriv {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Al
gebra A B] [Differential A] [Differential B] [DifferentialAlgebra A B] (a : A) :
 (a′ : A) = (a : B)′
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DifferentialAlgebra.deriv_algebraMap`：∀ {A : Type u_1} {B : Type u_2} {i
nst : CommRing A} {inst_1 : CommRing B} {inst_2 : Algebra A B}   {inst_3 : Diffe
rential A} {inst_4 : Diffe…
-/
lemma algebraMap.coe_deriv {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Differential A] [Differential B] [DifferentialAlgebra A B] (a : A) :
    (a′ : A) = (a : B)′ :=
  (DifferentialAlgebra.deriv_algebraMap _).symm

/--
A differential ring `A` and an algebra over it `B` share constants if all
constants in B are in the range of `algebraMap A B`.
-/
/-
**Differential.ContainConstants** 是 Mathlib 中的一个归纳类型，位于命名空间 `Differential`。
形式化陈述：(A : Type u_1) → (B : Type u_2) → [inst : CommRing A] → [inst_1 : CommRing
 B] → [Algebra A B] → [Differential B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A differential ring `A` and an algebra over it `B` share constants if all
constants in B are in the range of `algebraMap A B`.
-/
class Differential.ContainConstants (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Differential B] : Prop where
  /-- If the derivative of x is 0, then it's in the range of `algebraMap A B`. -/
  protected mem_range_of_deriv_eq_zero {x : B} (h : x′ = 0) : x ∈ (algebraMap A B).range
/-
**mem_range_of_deriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_range_of_deriv_eq_zero (A : Type*) {B : Type*} [CommRing A] [CommRing 
B] [Algebra A B] [Differential B] [Differential.ContainConstants A B] {x : B} (h
 : x′ = 0) : x in (algebraMap A B).range
参数：A : Type*；h : x′ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differential.ContainConstants.mem_range_of_deriv_eq_zero`：∀ {A : Type u_
1} {B : Type u_2} {inst : CommRing A} {inst_1 : CommRing B} {inst_2 : Algebra A 
B}   {inst_3 : Differential B} [self : Differe…
-/
lemma mem_range_of_deriv_eq_zero (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Differential B] [Differential.ContainConstants A B] {x : B} (h : x′ = 0) :
    x ∈ (algebraMap A B).range :=
  Differential.ContainConstants.mem_range_of_deriv_eq_zero h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Type*) [CommRing A] [Differential A] : DifferentialAlgebra A A where
  deriv_algebraMap _ := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Type*) [CommRing A] [Differential A] : Differential.ContainConstants A A where
  mem_range_of_deriv_eq_zero {x} _ := ⟨x, rfl⟩

/-- Transfer a `Differential` instance across a `RingEquiv`. -/
@[reducible]
/-
**Differential.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Differential.equiv {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential
 R₂] (h : R ≃+* R₂) : Differential R
参数：h : R ≃+* R₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `Differential` instance across a `RingEquiv`.
-/
def Differential.equiv {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂]
    (h : R ≃+* R₂) : Differential R :=
  ⟨Derivation.mk' (h.symm.toAddMonoidHom.toIntLinearMap ∘ₗ
    Differential.deriv.toLinearMap ∘ₗ h.toAddMonoidHom.toIntLinearMap) (by simp)⟩

/--
Transfer a `DifferentialAlgebra` instance across a `AlgEquiv`.
-/
/-
**DifferentialAlgebra.equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentialAlgebra.equiv {A : Type*} [CommRing A] [Differential A] {R R₂ 
: Type*} [CommRing R] [CommRing R₂] [Differential R₂] [Algebra A R] [Algebra A R
₂] [DifferentialAlgebra A R₂] (h : R ≃ₐ[A] R₂) : letI
参数：h : R ≃ₐ[A] R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `DifferentialAlgebra.deriv_algebraMap`：∀ {A : Type u_1} {B : Type u_2} {i
nst : CommRing A} {inst_1 : CommRing B} {inst_2 : Algebra A B}   {inst_3 : Diffe
rential A} {inst_4 : Diffe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer a `DifferentialAlgebra` instance across a `AlgEquiv`.
-/
lemma DifferentialAlgebra.equiv {A : Type*} [CommRing A] [Differential A]
    {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂] [Algebra A R]
    [Algebra A R₂] [DifferentialAlgebra A R₂] (h : R ≃ₐ[A] R₂) :
    letI := Differential.equiv h.toRingEquiv
    DifferentialAlgebra A R :=
  letI := Differential.equiv h.toRingEquiv
  ⟨fun a ↦ by
    change (LinearMap.comp ..) _ = _
    simp [deriv_algebraMap]⟩
