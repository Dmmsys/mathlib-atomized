/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Reinterpret an additive homomorphism as a `ℚ`-linear map.
-/

@[expose] public section

open Function

variable {M M₂ : Type*}

/--
Definition of `AddMonoidHom.toRatLinearMap` / `AddMonoidHom.toRatLinearMap` 的定义

English:
definition AddMonoidHom.toRatLinearMap
  signature: [AddCommGroup M] [Module Rat M] [AddCommGroup M₂] [Module Rat M₂]
  body: { f with map_smul' := map_rat_smul f }

中文:
定义 AddMonoidHom.toRatLinearMap
  签名: [AddCommGroup M] [Module Rat M] [AddCommGroup M₂] [Module Rat M₂]
  定义体: { f with map_smul' := map_rat_smul f }

Depends on / 依赖: map_rat_smul, map_smul
-/
def AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module Rat M] [AddCommGroup M₂] [Module Rat M₂]
    (f : M ->+ M₂) : M ->ₗ[Rat] M₂ :=
  { f with map_smul' := map_rat_smul f }

/--
theorem `AddMonoidHom.toRatLinearMap_injective` / 定理 `AddMonoidHom.toRatLinearMap_injective`

English:
theorem AddMonoidHom.toRatLinearMap_injective
  statement: [AddCommGroup M] [Module Rat M] [AddCommGroup M₂]
  proof: by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]

中文:
定理 AddMonoidHom.toRatLinearMap_injective
  结论: [AddCommGroup M] [Module Rat M] [AddCommGroup M₂]
  证明: by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem AddMonoidHom.toRatLinearMap_injective [AddCommGroup M] [Module Rat M] [AddCommGroup M₂]
    [Module Rat M₂] : Function.Injective (@AddMonoidHom.toRatLinearMap M M₂ _ _ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
/--
theorem `AddMonoidHom.coe_toRatLinearMap` / 定理 `AddMonoidHom.coe_toRatLinearMap`

English:
theorem AddMonoidHom.coe_toRatLinearMap
  statement: [AddCommGroup M] [Module Rat M] [AddCommGroup M₂]
  proof: rfl

中文:
定理 AddMonoidHom.coe_toRatLinearMap
  结论: [AddCommGroup M] [Module Rat M] [AddCommGroup M₂]
  证明: rfl
-/
theorem AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module Rat M] [AddCommGroup M₂]
    [Module Rat M₂] (f : M ->+ M₂) : ⇑f.toRatLinearMap = f :=
  rfl
