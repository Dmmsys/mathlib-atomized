/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Tannaka duality for rings

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/

@[expose] public section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] add_smul mul_smul in
attribute [local ext] End.ext in
/--
Definition of `ringEquivEndForget₂` / `ringEquivEndForget₂` 的定义

English:
definition ringEquivEndForget₂
  signature: (R : Type u) [Ring R]
  body: ObjectProperty.homMk
      { app M := @AddCommGrpCat.ofHom M.carrier M.carrier _ _
          (DistribSMul.toAddMonoidHom M r) }
  invFun φ := φ.hom.app (ModuleCat.of R R) (1 : R)
  left_inv _ := by simp
  right_inv φ := by
    ext M (x : M)
    have w := CategoryTheory.congr_fun
      (φ.hom.natural

中文:
定义 ringEquivEndForget₂
  签名: (R : 类型u) [环 R]
  定义体: ObjectProperty.homMk
      { app M := @AddCommGrpCat.ofHom M.carrier M.carrier _ _
          (DistribSMul.toAddMonoidHom M r) }
  invFun φ := φ.hom.app (ModuleCat.of R R) (1 : R)
  left_inv _ := by simp
  right_inv φ := by
    ext M (x : M)
    have w := CategoryTheory.congr_fun
      (φ.hom.natural

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ofHom, CategoryTheory, CategoryTheory.congr_fun, DistribSMul, DistribSMul.toAddMonoidHom, LinearMap, LinearMap.toSpanSingleton, M.carrier, ModuleCat, ModuleCat.of, ModuleCat.ofHom, ObjectProperty, ObjectProperty.homMk, carrier, cat_disch, congr_arg, congr_fun, hom.app, hom.naturality
-/
def ringEquivEndForget₂ (R : Type u) [Ring R] :
    R ≃+* End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) where
  toFun r :=
    ObjectProperty.homMk
      { app M := @AddCommGrpCat.ofHom M.carrier M.carrier _ _
          (DistribSMul.toAddMonoidHom M r) }
  invFun φ := φ.hom.app (ModuleCat.of R R) (1 : R)
  left_inv _ := by simp
  right_inv φ := by
    ext M (x : M)
    have w := CategoryTheory.congr_fun
      (φ.hom.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton R M x))) (1 : R)
    exact w.symm.trans (congr_arg (φ.hom.app M) (one_smul R x))
  map_add' := by cat_disch
  map_mul' := by cat_disch
