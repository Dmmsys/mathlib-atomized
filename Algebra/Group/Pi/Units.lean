/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Util.Delaborators

/-! # Units in pi types -/

@[expose] public section

variable {ι : Type*} {M : ι -> Type*} [forall i, Monoid (M i)] {x : Π i, M i}

open Units in
/-- The monoid equivalence between units of a product,
and the product of the units of each monoid. -/
@[to_additive (attr := simps)
  /-- The additive-monoid equivalence between (additive) units of a product,
  and the product of the (additive) units of each monoid. -/]
/--
Definition of `MulEquiv.piUnits` / `MulEquiv.piUnits` 的定义

English:
definition MulEquiv.piUnits
  signature: : (Π i, M i)ˣ ≃* Π i, (M i)ˣ where
  body: ⟨f.val i, f.inv i, congr_fun f.val_inv i, congr_fun f.inv_val i⟩
  invFun f := ⟨(val <| f ·), (inv <| f ·), funext (val_inv <| f ·), funext (inv_val <| f ·)⟩
  map_mul' _ _ := rfl

@[to_additive]

中文:
定义 乘法等价.piUnits
  签名: : (Π i, M i)ˣ ≃* Π i, (M i)ˣ where
  定义体: ⟨f.val i, f.inv i, congr_fun f.val_inv i, congr_fun f.inv_val i⟩
  invFun f := ⟨(val <| f ·), (inv <| f ·), funext (val_inv <| f ·), funext (inv_val <| f ·)⟩
  map_mul' _ _ := rfl

@[to_additive]

Depends on / 依赖: congr_fun, f.inv, f.inv_val, f.val, f.val_inv, inv_val, val_inv
-/
def MulEquiv.piUnits : (Π i, M i)ˣ ≃* Π i, (M i)ˣ where
  toFun f i := ⟨f.val i, f.inv i, congr_fun f.val_inv i, congr_fun f.inv_val i⟩
  invFun f := ⟨(val <| f ·), (inv <| f ·), funext (val_inv <| f ·), funext (inv_val <| f ·)⟩
  map_mul' _ _ := rfl

@[to_additive]
/--
lemma `Pi.isUnit_iff` / 引理 `Pi.isUnit_iff`

English:
lemma Pi.isUnit_iff
  proof: by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y => x i * y = 1 ∧ y * x i = 1).symm

@[to_additive]

中文:
引理 依赖函数类型.isUnit_iff
  证明: by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y => x i * y = 1 ∧ y * x i = 1).symm

@[to_additive]

Depends on / 依赖: Classical, Classical.skolem, forall_and, funext_iff, isUnit_iff_exists, simp_rw, skolem
-/
lemma Pi.isUnit_iff :
    IsUnit x ↔ forall i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y => x i * y = 1 ∧ y * x i = 1).symm

@[to_additive]
/--
Instance `Pi.instSubsingletonUnits` / 实例 `Pi.instSubsingletonUnits`

English:
instance Pi.instSubsingletonUnits
  signature: [forall i, Subsingleton (M i)ˣ]
  body: .units_of_isUnit by simp [Pi.isUnit_iff, funext_iff]

@[to_additive]
alias ⟨IsUnit.apply, _⟩ := Pi.isUnit_iff

@[to_additive]

中文:
实例 依赖函数类型.instSubsingletonUnits
  签名: [对任意 i, 子单例 (M i)ˣ]
  定义体: .units_of_isUnit by simp [Pi.isUnit_iff, funext_iff]

@[to_additive]
alias ⟨IsUnit.apply, _⟩ := Pi.isUnit_iff

@[to_additive]

Depends on / 依赖: Pi.isUnit_iff, funext_iff, isUnit_iff, units_of_isUnit
-/
instance Pi.instSubsingletonUnits [forall i, Subsingleton (M i)ˣ] : Subsingleton (forall i, M i)ˣ :=
.units_of_isUnit by simp [Pi.isUnit_iff, funext_iff]

@[to_additive]
alias ⟨IsUnit.apply, _⟩ := Pi.isUnit_iff

@[to_additive]
/--
lemma `IsUnit.val_inv_apply` / 引理 `IsUnit.val_inv_apply`

English:
lemma IsUnit.val_inv_apply
  given: (hx : IsUnit x) (i : ι)
  statement: (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹
  proof: by
  rw [← Units.inv_eq_val_inv]; rw [← MulEquiv.val_inv_piUnits_apply]; congr; ext; rfl

中文:
引理 是单位.val_inv_apply
  条件: (hx : 是单位 x) (i : ι)
  结论: (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹
  证明: by
  rw [← Units.inv_eq_val_inv]; rw [← MulEquiv.val_inv_piUnits_apply]; congr; ext; rfl

Depends on / 依赖: MulEquiv, MulEquiv.val_inv_piUnits_apply, Units.inv_eq_val_inv, inv_eq_val_inv, val_inv_piUnits_apply
-/
lemma IsUnit.val_inv_apply (hx : IsUnit x) (i : ι) : (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹ := by
  rw [← Units.inv_eq_val_inv]; rw [← MulEquiv.val_inv_piUnits_apply]; congr; ext; rfl
