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
/--
Definition of `Differential` / `Differential` 的定义

English:
class Differential
  parameters: (R : Type*) [CommRing R]
  axioms and operations (1):
    - deriv : Derivation Int R R

中文:
类 微分
  参数: (R : 类型) [交换环 R]
  公理与运算 (1 个):
    - deriv : 导子 整数 R R
-/
class Differential (R : Type*) [CommRing R] where
  /-- The `Derivation` associated with the ring. -/
  deriv : Derivation Int R R

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
guard e.isAppOfArity' ``DFunLike.coe 6
guard (e.getArg!' 4).isAppOf' ``Differential.deriv
  let arg ← withAppArg delab
  `($arg′)

/--
Definition of `DifferentialAlgebra` / `DifferentialAlgebra` 的定义

English:
class DifferentialAlgebra
  parameters: (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  axioms and operations (1):
    - deriv_algebraMap : forall a : A, (algebraMap A B a)′ = algebraMap A B a′

中文:
类 微分代数
  参数: (A B : 类型) [交换环 A] [交换环 B] [代数 A B]
  公理与运算 (1 个):
    - deriv_algebraMap : 对任意 a : A, (algebraMap A B a)′ = algebraMap A B a′
-/
class DifferentialAlgebra (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Differential A] [Differential B] : Prop where
  deriv_algebraMap : forall a : A, (algebraMap A B a)′ = algebraMap A B a′

export DifferentialAlgebra (deriv_algebraMap)

@[norm_cast]
/--
lemma `algebraMap.coe_deriv` / 引理 `algebraMap.coe_deriv`

English:
lemma algebraMap.coe_deriv
  statement: {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  proof: (DifferentialAlgebra.deriv_algebraMap _).symm

中文:
引理 algebraMap.coe_deriv
  结论: {A : 类型} {B : 类型} [交换环 A] [交换环 B] [代数 A B]
  证明: (DifferentialAlgebra.deriv_algebraMap _).symm

Depends on / 依赖: DifferentialAlgebra, DifferentialAlgebra.deriv_algebraMap, deriv_algebraMap
-/
lemma algebraMap.coe_deriv {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Differential A] [Differential B] [DifferentialAlgebra A B] (a : A) :
    (a′ : A) = (a : B)′ :=
  (DifferentialAlgebra.deriv_algebraMap _).symm

/--
Definition of `Differential.ContainConstants` / `Differential.ContainConstants` 的定义

English:
class Differential.ContainConstants
  parameters: (A B : Type*) [CommRing A] [CommRing B]
  axioms and operations (1):
    - mem_range_of_deriv_eq_zero({x : B} (h : x′ = 0)) : x in (algebraMap A B).range

中文:
类 微分.余ntainConstants
  参数: (A B : 类型) [交换环 A] [交换环 B]
  公理与运算 (1 个):
    - mem_range_of_deriv_eq_zero({x : B} (h : x′ = 0)) : x in (algebraMap A B).range
-/
class Differential.ContainConstants (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Differential B] : Prop where
  /-- If the derivative of x is 0, then it's in the range of `algebraMap A B`. -/
  protected mem_range_of_deriv_eq_zero {x : B} (h : x′ = 0) : x in (algebraMap A B).range

/--
lemma `mem_range_of_deriv_eq_zero` / 引理 `mem_range_of_deriv_eq_zero`

English:
lemma mem_range_of_deriv_eq_zero
  statement: (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  proof: Differential.ContainConstants.mem_range_of_deriv_eq_zero h

中文:
引理 mem_range_of_deriv_eq_zero
  结论: (A : 类型) {B : 类型} [交换环 A] [交换环 B] [代数 A B]
  证明: Differential.ContainConstants.mem_range_of_deriv_eq_zero h

Depends on / 依赖: ContainConstants, Differential, Differential.ContainConstants.mem_range_of_deriv_eq_zero, mem_range_of_deriv_eq_zero
-/
lemma mem_range_of_deriv_eq_zero (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Differential B] [Differential.ContainConstants A B] {x : B} (h : x′ = 0) :
    x in (algebraMap A B).range :=
  Differential.ContainConstants.mem_range_of_deriv_eq_zero h

instance (A : Type*) [CommRing A] [Differential A] : DifferentialAlgebra A A where
  deriv_algebraMap _ := rfl

instance (A : Type*) [CommRing A] [Differential A] : Differential.ContainConstants A A where
  mem_range_of_deriv_eq_zero {x} _ := ⟨x, rfl⟩

/-- Transfer a `Differential` instance across a `RingEquiv`. -/
@[reducible]
/--
Definition of `Differential.equiv` / `Differential.equiv` 的定义

English:
definition Differential.equiv
  signature: {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂]
  body: ⟨Derivation.mk' (h.symm.toAddMonoidHom.toIntLinearMap ∘ₗ
    Differential.deriv.toLinearMap ∘ₗ h.toAddMonoidHom.toIntLinearMap) (by simp)⟩

中文:
定义 微分.equiv
  签名: {R R₂ : 类型} [交换环 R] [交换环 R₂] [微分 R₂]
  定义体: ⟨Derivation.mk' (h.symm.toAddMonoidHom.toIntLinearMap ∘ₗ
    Differential.deriv.toLinearMap ∘ₗ h.toAddMonoidHom.toIntLinearMap) (by simp)⟩

Depends on / 依赖: Derivation, Derivation.mk, Differential, Differential.deriv.toLinearMap, h.symm.toAddMonoidHom.toIntLinearMap, h.toAddMonoidHom.toIntLinearMap, toAddMonoidHom, toIntLinearMap, toLinearMap
-/
def Differential.equiv {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂]
    (h : R ≃+* R₂) : Differential R :=
  ⟨Derivation.mk' (h.symm.toAddMonoidHom.toIntLinearMap ∘ₗ
    Differential.deriv.toLinearMap ∘ₗ h.toAddMonoidHom.toIntLinearMap) (by simp)⟩

/--
lemma `DifferentialAlgebra.equiv` / 引理 `DifferentialAlgebra.equiv`

English:
lemma DifferentialAlgebra.equiv
  statement: {A : Type*} [CommRing A] [Differential A]
  proof: Differential.equiv h.toRingEquiv
    DifferentialAlgebra A R :=
  letI := Differential.equiv h.toRingEquiv
  ⟨fun a => by
    change (LinearMap.comp ..) _ = _
    simp [deriv_algebraMap]⟩

中文:
引理 微分代数.equiv
  结论: {A : 类型} [交换环 A] [微分 A]
  证明: Differential.equiv h.toRingEquiv
    DifferentialAlgebra A R :=
  letI := Differential.equiv h.toRingEquiv
  ⟨fun a => by
    change (LinearMap.comp ..) _ = _
    simp [deriv_algebraMap]⟩

Depends on / 依赖: Differential, Differential.equiv, h.toRingEquiv, toRingEquiv
-/
lemma DifferentialAlgebra.equiv {A : Type*} [CommRing A] [Differential A]
    {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂] [Algebra A R]
    [Algebra A R₂] [DifferentialAlgebra A R₂] (h : R ≃ₐ[A] R₂) :
    letI := Differential.equiv h.toRingEquiv
    DifferentialAlgebra A R :=
  letI := Differential.equiv h.toRingEquiv
  ⟨fun a => by
    change (LinearMap.comp ..) _ = _
    simp [deriv_algebraMap]⟩
