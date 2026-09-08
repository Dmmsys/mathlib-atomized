/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Limit creation properties of `Functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
create certain (co)limits and vice versa.

-/

public section

universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

namespace Limits

/-- If `F : C ⥤ D` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：createsLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesColimit K.leftOp F] : Cre
atesLimit K F.op where __
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ`
 creates
limits of `K : J ⥤ Cᵒᵖ`.
-/
def createsLimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.op where
  __ := reflectsLimit_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) _ (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` creates
limits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitOfOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：createsLimitOfOp (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K.op F.op] : Crea
tesLimit K F where __
参数：K : J ⥤ C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` c
reates
limits of `K : J ⥤ C`.
-/
def createsLimitOfOp (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K.op F.op] :
    CreatesLimit K F where
  __ := reflectsLimit_of_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.op) _ hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : C ⥤ Dᵒᵖ` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D`
creates limits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：createsLimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F]
 : CreatesLimit K F.leftOp where __
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ 
⥤ D`
creates limits of `K : J ⥤ Cᵒᵖ`.
-/
def createsLimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F] :
    CreatesLimit K F.leftOp where
  __ := reflectsLimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：createsLimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.op F.left
Op] : CreatesLimit K F where __
参数：K : J ⥤ C；F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒ
ᵖ` creates
limits of `K : J ⥤ C`.
-/
def createsLimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.op F.leftOp] :
    CreatesLimit K F where
  __ := reflectsLimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.leftOp)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : Cᵒᵖ ⥤ D` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitRightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：createsLimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.op F] : Cr
eatesLimit K F.rightOp where __
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ D
ᵒᵖ` creates
limits of `K : J ⥤ C`.
-/
def createsLimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.op F] :
    CreatesLimit K F.rightOp where
  __ := reflectsLimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
creates limits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitOfRightOp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsLimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.leftOp
 F.rightOp] : CreatesLimit K F where __
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C
ᵒᵖ ⥤ D`
creates limits of `K : J ⥤ Cᵒᵖ`.
-/
def createsLimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.leftOp F.rightOp] :
    CreatesLimit K F where
  __ := reflectsLimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` creates
limits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：createsLimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.op F] : Cre
atesLimit K F.unop where __
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D`
 creates
limits of `K : J ⥤ C`.
-/
def createsLimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.op F] :
    CreatesLimit K F.unop where
  __ := reflectsLimit_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F.unop : C ⥤ D` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates
limits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：createsLimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.leftOp 
F.unop] : CreatesLimit K F where __
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates colimits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒ
ᵖ` creates
limits of `K : J ⥤ Cᵒᵖ`.
-/
def createsLimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F.unop] :
    CreatesLimit K F where
  __ := reflectsLimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.unop)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

/-- If `F : C ⥤ D` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：createsColimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesLimit K.leftOp F] : Cre
atesColimit K F.op where __
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` c
reates
colimits of `K : J ⥤ Cᵒᵖ`.
-/
def createsColimitOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesLimit K.leftOp F] :
    CreatesColimit K F.op where
  __ := reflectsColimit_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` creates
colimits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitOfOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：createsColimitOfOp (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K.op F.op] : Crea
tesColimit K F where __
参数：K : J ⥤ C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ D` cre
ates
colimits of `K : J ⥤ C`.
-/
def createsColimitOfOp (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K.op F.op] :
    CreatesColimit K F where
  __ := reflectsColimit_of_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.op) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F : C ⥤ Dᵒᵖ` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ D` creates
colimits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：createsColimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F]
 : CreatesColimit K F.leftOp where __
参数：K : J ⥤ Cᵒᵖ；F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates limits of `K.leftOp : Jᵒᵖ ⥤ C`, then `F.leftOp : Cᵒᵖ ⥤ 
D` creates
colimits of `K : J ⥤ Cᵒᵖ`.
-/
def createsColimitLeftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F] :
    CreatesColimit K F.leftOp where
  __ := reflectsColimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：createsColimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.op F.left
Op] : CreatesColimit K F where __
参数：K : J ⥤ C；F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : C ⥤ Dᵒᵖ`
 creates
colimits of `K : J ⥤ C`.
-/
def createsColimitOfLeftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.op F.leftOp] :
    CreatesColimit K F where
  __ := reflectsColimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.leftOp)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F : Cᵒᵖ ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitRightOp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsColimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.op F] : Cr
eatesColimit K F.rightOp where __
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ
` creates
colimits of `K : J ⥤ C`.
-/
def createsColimitRightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.op F] :
    CreatesColimit K F.rightOp where
  __ := reflectsColimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ ⥤ D`
creates colimits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitOfRightOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsColimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.leftOp
 F.rightOp] : CreatesColimit K F where __
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of `K.leftOp : Jᵒᵖ ⥤ Cᵒᵖ`, then `F : Cᵒᵖ
 ⥤ D`
creates colimits of `K : J ⥤ Cᵒᵖ`.
-/
def createsColimitOfRightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.leftOp F.rightOp] :
    CreatesColimit K F where
  __ := reflectsColimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` creates
colimits of `K : J ⥤ C`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：createsColimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.op F] : Cre
atesColimit K F.unop where __
参数：K : J ⥤ C；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` c
reates
colimits of `K : J ⥤ C`.
-/
def createsColimitUnop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.op F] :
    CreatesColimit K F.unop where
  __ := reflectsColimit_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

/-- If `F.unop : C ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates
colimits of `K : J ⥤ Cᵒᵖ`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：createsColimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.leftOp 
F.unop] : CreatesColimit K F where __
参数：K : J ⥤ Cᵒᵖ；F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates limits of `K.op : Jᵒᵖ ⥤ C`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` cre
ates
colimits of `K : J ⥤ Cᵒᵖ`.
-/
def createsColimitOfUnop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F.unop] :
    CreatesColimit K F where
  __ := reflectsColimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.unop)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

section

variable (J)

/-- If `F : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of
shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeOp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：createsLimitsOfShapeOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] : Create
sLimitsOfShape J F.op where CreatesLimit {K}
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates 
limits of
shape `J`.
-/
def createsLimitsOfShapeOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.op where CreatesLimit {K} := createsLimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] : 
CreatesLimitsOfShape J F.leftOp where CreatesLimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` crea
tes limits
of shape `J`.
-/
def createsLimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.leftOp where CreatesLimit {K} := createsLimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
 CreatesLimitsOfShape J F.rightOp where CreatesLimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` cre
ates limits
of shape `J`.
-/
def createsLimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.rightOp where CreatesLimit {K} := createsLimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates limits of
shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：createsLimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] : 
CreatesLimitsOfShape J F.unop where CreatesLimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` create
s limits of
shape `J`.
-/
def createsLimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.unop where CreatesLimit {K} := createsLimitUnop K F

/-- If `F : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of
shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeOp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：createsColimitsOfShapeOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] : Create
sColimitsOfShape J F.op where CreatesColimit {K}
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates co
limits of
shape `J`.
-/
def createsColimitsOfShapeOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.op where CreatesColimit {K} := createsColimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] : 
CreatesColimitsOfShape J F.leftOp where CreatesColimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` create
s colimits
of shape `J`.
-/
def createsColimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.leftOp where CreatesColimit {K} := createsColimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeRightOp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
 CreatesColimitsOfShape J F.rightOp where CreatesColimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creat
es colimits
of shape `J`.
-/
def createsColimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.rightOp where CreatesColimit {K} := createsColimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] : 
CreatesColimitsOfShape J F.unop where CreatesColimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates 
colimits
of shape `J`.
-/
def createsColimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.unop where CreatesColimit {K} := createsColimitUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates limits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeOfOp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：createsLimitsOfShapeOfOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.op] : C
reatesLimitsOfShape J F where CreatesLimit {K}
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates 
limits
of shape `J`.
-/
def createsLimitsOfShapeOfOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.op] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.l
eftOp] : CreatesLimitsOfShape J F where CreatesLimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` crea
tes limits
of shape `J`.
-/
def createsLimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creates limits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeOfRightOp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.
rightOp] : CreatesLimitsOfShape J F where CreatesLimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` cre
ates limits
of shape `J`.
-/
def createsLimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfRightOp K F

/-- If `F.unop : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfShapeOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsLimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.u
nop] : CreatesLimitsOfShape J F where CreatesLimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` create
s limits
of shape `J`.
-/
def createsLimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.unop] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeOfOp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeOfOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.op] : C
reatesColimitsOfShape J F where CreatesColimit {K}
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates co
limits
of shape `J`.
-/
def createsColimitsOfShapeOfOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.op] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.l
eftOp] : CreatesColimitsOfShape J F where CreatesColimit {K}
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` create
s colimits
of shape `J`.
-/
def createsColimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeOfRightOp** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.
rightOp] : CreatesColimitsOfShape J F where CreatesColimit {K}
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creat
es colimits
of shape `J`.
-/
def createsColimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfRightOp K F

/-- If `F.unop : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfShapeOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsColimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.u
nop] : CreatesColimitsOfShape J F where CreatesColimit {K}
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates 
colimits
of shape `J`.
-/
def createsColimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.unop] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfUnop K F

end

/-- If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeOp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsLimitsOfSizeOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F] : Crea
tesLimitsOfSize.{w, w'} F.op where CreatesLimitsOfShape {_} _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits.
-/
def createsLimitsOfSizeOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.op where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsLimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] 
: CreatesLimitsOfSize.{w, w'} F.leftOp where CreatesLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits.
-/
def createsLimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.leftOp where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsLimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F]
 : CreatesLimitsOfSize.{w, w'} F.rightOp where CreatesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits.
-/
def createsLimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.rightOp where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsLimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] 
: CreatesLimitsOfSize.{w, w'} F.unop where CreatesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits.
-/
def createsLimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.unop where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeUnop _ _

/-- If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsColimitsOfSizeOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F] : Crea
tesColimitsOfSize.{w, w'} F.op where CreatesColimitsOfShape {_} _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits.
-/
def createsColimitsOfSizeOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.op where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] 
: CreatesColimitsOfSize.{w, w'} F.leftOp where CreatesColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits.
-/
def createsColimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.leftOp where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F]
 : CreatesColimitsOfSize.{w, w'} F.rightOp where CreatesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits.
-/
def createsColimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.rightOp where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] 
: CreatesColimitsOfSize.{w, w'} F.unop where CreatesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits.
-/
def createsColimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.unop where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeOfOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsLimitsOfSizeOfOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op] :
 CreatesLimitsOfSize.{w, w'} F where CreatesLimitsOfShape {_} _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits.
-/
def createsLimitsOfSizeOfOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsLimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F
.leftOp] : CreatesLimitsOfSize.{w, w'} F where CreatesLimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits.
-/
def createsLimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.leftOp] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeOfRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsLimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} 
F.rightOp] : CreatesLimitsOfSize.{w, w'} F where CreatesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits.
-/
def createsLimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F.rightOp] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsLimitsOfSizeOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsLimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F
.unop] : CreatesLimitsOfSize.{w, w'} F where CreatesLimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits.
-/
def createsLimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.unop] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeOfOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeOfOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op] :
 CreatesColimitsOfSize.{w, w'} F where CreatesColimitsOfShape {_} _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits.
-/
def createsColimitsOfSizeOfOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F
.leftOp] : CreatesColimitsOfSize.{w, w'} F where CreatesColimitsOfShape {_} _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits.
-/
def createsColimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.leftOp] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeOfRightOp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} 
F.rightOp] : CreatesColimitsOfSize.{w, w'} F where CreatesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits.
-/
def createsColimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F.rightOp] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsColimitsOfSizeOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsColimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F
.unop] : CreatesColimitsOfSize.{w, w'} F where CreatesColimitsOfShape {_} _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits.
-/
def createsColimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.unop] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfUnop _ _

/-- If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：createsLimitsOp (F : C ⥤ D) [CreatesColimits F] : CreatesLimits F.op
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits.
-/
abbrev createsLimitsOp (F : C ⥤ D) [CreatesColimits F] : CreatesLimits F.op :=
  createsLimitsOfSizeOp F

/-- If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsLeftOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.le
ftOp
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits.
-/
abbrev createsLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.leftOp :=
  createsLimitsOfSizeLeftOp F

/-- If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsRightOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：createsLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F] : CreatesLimits F.r
ightOp
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits.
-/
abbrev createsLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F] : CreatesLimits F.rightOp :=
  createsLimitsOfSizeRightOp F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsUnop** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：createsLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.un
op
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits.
-/
abbrev createsLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.unop :=
  createsLimitsOfSizeUnop F

/-- If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：createsColimitsOp (F : C ⥤ D) [CreatesLimits F] : CreatesColimits F.op
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits.
-/
abbrev createsColimitsOp (F : C ⥤ D) [CreatesLimits F] : CreatesColimits F.op :=
  createsColimitsOfSizeOp F

/-- If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsLeftOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.
leftOp
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits.
-/
abbrev createsColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.leftOp :=
  createsColimitsOfSizeLeftOp F

/-- If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsRightOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：createsColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F] : CreatesColimits F
.rightOp
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits.
-/
abbrev createsColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F] : CreatesColimits F.rightOp :=
  createsColimitsOfSizeRightOp F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsUnop** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.
unop
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits.
-/
abbrev createsColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.unop :=
  createsColimitsOfSizeUnop F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsOfOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：createsLimitsOfOp (F : C ⥤ D) [CreatesColimits F.op] : CreatesLimits F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits.
-/
abbrev createsLimitsOfOp (F : C ⥤ D) [CreatesColimits F.op] : CreatesLimits F :=
  createsLimitsOfSizeOfOp F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsOfLeftOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp] : CreatesLi
mits F
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits.
-/
abbrev createsLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp] : CreatesLimits F :=
  createsLimitsOfSizeOfLeftOp F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsOfRightOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：createsLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp] : Creates
Limits F
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits.
-/
abbrev createsLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp] : CreatesLimits F :=
  createsLimitsOfSizeOfRightOp F

/-- If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
/-
**CategoryTheory.Limits.createsLimitsOfUnop** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop] : CreatesLimi
ts F
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits.
-/
abbrev createsLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop] : CreatesLimits F :=
  createsLimitsOfSizeOfUnop F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsOfOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsColimitsOfOp (F : C ⥤ D) [CreatesLimits F.op] : CreatesColimits F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits.
-/
abbrev createsColimitsOfOp (F : C ⥤ D) [CreatesLimits F.op] : CreatesColimits F :=
  createsColimitsOfSizeOfOp F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsOfLeftOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp] : CreatesCo
limits F
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits.
-/
abbrev createsColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp] : CreatesColimits F :=
  createsColimitsOfSizeOfLeftOp F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsOfRightOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp] : Creates
Colimits F
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits.
-/
abbrev createsColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp] : CreatesColimits F :=
  createsColimitsOfSizeOfRightOp F

/-- If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
/-
**CategoryTheory.Limits.createsColimitsOfUnop** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop] : CreatesColi
mits F
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits.
-/
abbrev createsColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop] : CreatesColimits F :=
  createsColimitsOfSizeOfUnop F

/-- If `F : C ⥤ D` creates finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：createsFiniteLimitsOp (F : C ⥤ D) [CreatesFiniteColimits F] : CreatesFinit
eLimits F.op where createsFiniteLimits J _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
limits.
-/
def createsFiniteLimitsOp (F : C ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.op where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` creates finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F] : Create
sFiniteLimits F.leftOp where createsFiniteLimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates fini
te
limits.
-/
def createsFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.leftOp where
  createsFiniteLimits J _ _ := createsLimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` creates finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsRightOp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：createsFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F] : Creat
esFiniteLimits F.rightOp where createsFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates fin
ite
limits.
-/
def createsFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.rightOp where
  createsFiniteLimits J _ _ := createsLimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F.unop : C ⥤ D` creates finite
limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsUnop** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F] : Create
sFiniteLimits F.unop where createsFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F.unop : C ⥤ D` creates finite
limits.
-/
def createsFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.unop where
  createsFiniteLimits J _ _ := createsLimitsOfShapeUnop J F

/-- If `F : C ⥤ D` creates finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsFiniteColimitsOp (F : C ⥤ D) [CreatesFiniteLimits F] : CreatesFinit
eColimits F.op where createsFiniteColimits J _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
colimits.
-/
def createsFiniteColimitsOp (F : C ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.op where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` creates finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F] : Create
sFiniteColimits F.leftOp where createsFiniteColimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
colimits.
-/
def createsFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.leftOp where
  createsFiniteColimits J _ _ := createsColimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` creates finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F] : Creat
esFiniteColimits F.rightOp where createsFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finit
e
colimits.
-/
def createsFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.rightOp where
  createsFiniteColimits J _ _ := createsColimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F.unop : C ⥤ D` creates finite
colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F] : Create
sFiniteColimits F.unop where createsFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F.unop : C ⥤ D` creates finite
colimits.
-/
def createsFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.unop where
  createsFiniteColimits J _ _ := createsColimitsOfShapeUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F : C ⥤ D` creates finite limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfOp (F : C ⥤ D) [CreatesFiniteColimits F.op] : Creates
FiniteLimits F where createsFiniteLimits J _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F : C ⥤ D` creates finite l
imits.
-/
def createsFiniteLimitsOfOp (F : C ⥤ D) [CreatesFiniteColimits F.op] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates finite colimits, then `F : C ⥤ Dᵒᵖ` creates finite
limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F.leftOp]
 : CreatesFiniteLimits F where createsFiniteLimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates finite colimits, then `F : C ⥤ Dᵒᵖ` creates fini
te
limits.
-/
def createsFiniteLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F.leftOp] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates finite colimits, then `F : Cᵒᵖ ⥤ D` creates finite
limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F.rightO
p] : CreatesFiniteLimits F where createsFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates finite colimits, then `F : Cᵒᵖ ⥤ D` creates fin
ite
limits.
-/
def createsFiniteLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F.rightOp] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` creates finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteLimitsOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsFiniteLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop] :
 CreatesFiniteLimits F where createsFiniteLimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
 limits.
-/
def createsFiniteLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F : C ⥤ D` creates finite colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfOp (F : C ⥤ D) [CreatesFiniteLimits F.op] : Creates
FiniteColimits F where createsFiniteColimits J _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F : C ⥤ D` creates finite col
imits.
-/
def createsFiniteColimitsOfOp (F : C ⥤ D) [CreatesFiniteLimits F.op] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates finite limits, then `F : C ⥤ Dᵒᵖ` creates finite
colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfLeftOp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F.leftOp]
 : CreatesFiniteColimits F where createsFiniteColimits J _ _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.leftOp : Cᵒᵖ ⥤ D` creates finite limits, then `F : C ⥤ Dᵒᵖ` creates finite
colimits.
-/
def createsFiniteColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F.leftOp] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates finite limits, then `F : Cᵒᵖ ⥤ D` creates finite
colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfRightOp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F.rightO
p] : CreatesFiniteColimits F where createsFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp : C ⥤ Dᵒᵖ` creates finite limits, then `F : Cᵒᵖ ⥤ D` creates finit
e
colimits.
-/
def createsFiniteColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F.rightOp] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` creates finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteColimitsOfUnop** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsFiniteColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F.unop] :
 CreatesFiniteColimits F where createsFiniteColimits J _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.unop : C ⥤ D` creates finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite c
olimits.
-/
def createsFiniteColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F.unop] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfUnop J F

/-- If `F : C ⥤ D` creates finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
products. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteProductsOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：createsFiniteProductsOp (F : C ⥤ D) [CreatesFiniteCoproducts F] : CreatesF
initeProducts F.op where creates _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
products.
-/
def createsFiniteProductsOp (F : C ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.op where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` creates finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
products. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteProductsLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsFiniteProductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] : Cr
eatesFiniteProducts F.leftOp where creates _ _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` creates fi
nite
products.
-/
def createsFiniteProductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.leftOp where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeLeftOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` creates finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
products. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteProductsRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：createsFiniteProductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F] : C
reatesFiniteProducts F.rightOp where creates _ _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` creates f
inite
products.
-/
def createsFiniteProductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.rightOp where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeRightOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite coproducts, then `F.unop : C ⥤ D` creates finite
products. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteProductsUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsFiniteProductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] : Cr
eatesFiniteProducts F.unop where creates _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite coproducts, then `F.unop : C ⥤ D` creates fini
te
products.
-/
def createsFiniteProductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.unop where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeUnop
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` creates finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
coproducts. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteCoproductsOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：createsFiniteCoproductsOp (F : C ⥤ D) [CreatesFiniteProducts F] : CreatesF
initeCoproducts F.op where creates _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` creates finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
coproducts.
-/
def createsFiniteCoproductsOp (F : C ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.op where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` creates finite products, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
coproducts. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteCoproductsLeftOp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：createsFiniteCoproductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F] : Cr
eatesFiniteCoproducts F.leftOp where creates _ _
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Dᵒᵖ` creates finite products, then `F.leftOp : Cᵒᵖ ⥤ D` creates fini
te
coproducts.
-/
def createsFiniteCoproductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.leftOp where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeLeftOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` creates finite products, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
coproducts. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteCoproductsRightOp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：createsFiniteCoproductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F] : C
reatesFiniteCoproducts F.rightOp where creates _ _
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` creates finite products, then `F.rightOp : C ⥤ Dᵒᵖ` creates fin
ite
coproducts.
-/
def createsFiniteCoproductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.rightOp where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeRightOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite products, then `F.unop : C ⥤ D` creates finite
coproducts. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.createsFiniteCoproductsUnop** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：createsFiniteCoproductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F] : Cr
eatesFiniteCoproducts F.unop where creates _ _
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite products, then `F.unop : C ⥤ D` creates finite
coproducts.
-/
def createsFiniteCoproductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.unop where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeUnop
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

end CategoryTheory.Limits

