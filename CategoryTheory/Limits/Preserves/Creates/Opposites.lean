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
/--
Definition of `createsLimitOp` / `createsLimitOp` 的定义

English:
definition createsLimitOp
  signature: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesColimit K.leftOp F]
  body: reflectsLimit_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) _ (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitOp
  签名: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [创造余极限 K.leftOp F]
  定义体: reflectsLimit_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) _ (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: reflectsLimit_op
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
/--
Definition of `createsLimitOfOp` / `createsLimitOfOp` 的定义

English:
definition createsLimitOfOp
  signature: (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K.op F.op]
  body: reflectsLimit_of_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.op) _ hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitOfOp
  签名: (K : J ⥤ C) (F : C ⥤ D) [创造余极限 K.op F.op]
  定义体: reflectsLimit_of_op _ _
  lifts _ hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.op) _ hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: reflectsLimit_of_op
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
/--
Definition of `createsLimitLeftOp` / `createsLimitLeftOp` 的定义

English:
definition createsLimitLeftOp
  signature: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F]
  body: reflectsLimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitLeftOp
  签名: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [创造余极限 K.leftOp F]
  定义体: reflectsLimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: PreservesLimitOfIsCosplitPair, PreservesLimitOfIsCosplitPair.out, reflectsLimit_leftOp
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
/--
Definition of `createsLimitOfLeftOp` / `createsLimitOfLeftOp` 的定义

English:
definition createsLimitOfLeftOp
  signature: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesColimit K.op F.leftOp]
  body: reflectsLimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.leftOp)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitOfLeftOp
  签名: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [创造余极限 K.op F.leftOp]
  定义体: reflectsLimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F.leftOp)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: reflectsLimit_of_leftOp
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
/--
Definition of `createsLimitRightOp` / `createsLimitRightOp` 的定义

English:
definition createsLimitRightOp
  signature: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.op F]
  body: reflectsLimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitRightOp
  签名: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [创造余极限 K.op F]
  定义体: reflectsLimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := lc.liftedCocone.unop
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: ReflectsLimitOfIsCosplitPair, ReflectsLimitOfIsCosplitPair.out, reflectsLimit_rightOp
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
/--
Definition of `createsLimitOfRightOp` / `createsLimitOfRightOp` 的定义

English:
definition createsLimitOfRightOp
  signature: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesColimit K.leftOp F.rightOp]
  body: reflectsLimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitOfRightOp
  签名: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [创造余极限 K.leftOp F.rightOp]
  定义体: reflectsLimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: reflectsLimit_of_rightOp
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
/--
Definition of `createsLimitUnop` / `createsLimitUnop` 的定义

English:
definition createsLimitUnop
  signature: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.op F]
  body: reflectsLimit_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

中文:
定义 createsLimitUnop
  签名: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造余极限 K.op F]
  定义体: reflectsLimit_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCone := lc.liftedCocone.unop
      validLift := (coneOpEquiv.inverse.mapIso lc.validLift.symm).unop }

Depends on / 依赖: reflectsLimit_unop
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
/--
Definition of `createsLimitOfUnop` / `createsLimitOfUnop` 的定义

English:
definition createsLimitOfUnop
  signature: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimit K.leftOp F.unop]
  body: reflectsLimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.unop)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.s

中文:
定义 createsLimitOfUnop
  签名: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造余极限 K.leftOp F.unop]
  定义体: reflectsLimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesColimit.lifts (K := K.leftOp) (F := F.unop)
      (coconeLeftOpOfCone c) (isColimitCoconeLeftOpOfCone _ hc)
    { liftedCone := coneOfCoconeLeftOp lc.liftedCocone
      validLift := (coconeLeftOpOfConeEquiv.inverse.mapIso lc.validLift.s

Depends on / 依赖: CreatesLimitOfIsCosplitPair, CreatesLimitOfIsCosplitPair.out, reflectsLimit_of_unop
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
/--
Definition of `createsColimitOp` / `createsColimitOp` 的定义

English:
definition createsColimitOp
  signature: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [CreatesLimit K.leftOp F]
  body: reflectsColimit_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitOp
  签名: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [创造极限 K.leftOp F]
  定义体: reflectsColimit_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: reflectsColimit_op
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
/--
Definition of `createsColimitOfOp` / `createsColimitOfOp` 的定义

English:
definition createsColimitOfOp
  signature: (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K.op F.op]
  body: reflectsColimit_of_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.op) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitOfOp
  签名: (K : J ⥤ C) (F : C ⥤ D) [创造极限 K.op F.op]
  定义体: reflectsColimit_of_op _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.op) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: reflectsColimit_of_op
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
/--
Definition of `createsColimitLeftOp` / `createsColimitLeftOp` 的定义

English:
definition createsColimitLeftOp
  signature: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F]
  body: reflectsColimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitLeftOp
  签名: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [创造极限 K.leftOp F]
  定义体: reflectsColimit_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: reflectsColimit_leftOp
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
/--
Definition of `createsColimitOfLeftOp` / `createsColimitOfLeftOp` 的定义

English:
definition createsColimitOfLeftOp
  signature: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [CreatesLimit K.op F.leftOp]
  body: reflectsColimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.leftOp)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitOfLeftOp
  签名: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [创造极限 K.op F.leftOp]
  定义体: reflectsColimit_of_leftOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F.leftOp)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: PreservesLimitOfIsCoreflexivePair, PreservesLimitOfIsCoreflexivePair.out, reflectsColimit_of_leftOp
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
/--
Definition of `createsColimitRightOp` / `createsColimitRightOp` 的定义

English:
definition createsColimitRightOp
  signature: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.op F]
  body: reflectsColimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitRightOp
  签名: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [创造极限 K.op F]
  定义体: reflectsColimit_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: reflectsColimit_rightOp
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
/--
Definition of `createsColimitOfRightOp` / `createsColimitOfRightOp` 的定义

English:
definition createsColimitOfRightOp
  signature: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [CreatesLimit K.leftOp F.rightOp]
  body: reflectsColimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitOfRightOp
  签名: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [创造极限 K.leftOp F.rightOp]
  定义体: reflectsColimit_of_rightOp _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.rightOp) c.op hc.op
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: reflectsColimit_of_rightOp
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
/--
Definition of `createsColimitUnop` / `createsColimitUnop` 的定义

English:
definition createsColimitUnop
  signature: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.op F]
  body: reflectsColimit_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

中文:
定义 createsColimitUnop
  签名: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造极限 K.op F]
  定义体: reflectsColimit_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.op) (F := F) c.op hc.op
    { liftedCocone := lc.liftedCone.unop
      validLift := (coconeUnopOfConeEquiv.functor.mapIso lc.validLift.op).symm }

Depends on / 依赖: reflectsColimit_unop
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
/--
Definition of `createsColimitOfUnop` / `createsColimitOfUnop` 的定义

English:
definition createsColimitOfUnop
  signature: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimit K.leftOp F.unop]
  body: reflectsColimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.unop)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op

中文:
定义 createsColimitOfUnop
  签名: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造极限 K.leftOp F.unop]
  定义体: reflectsColimit_of_unop _ _
  lifts c hc :=
    letI lc := CreatesLimit.lifts (K := K.leftOp) (F := F.unop)
      (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone _ hc)
    { liftedCocone := coconeOfConeLeftOp lc.liftedCone
      validLift := (coconeRightOpOfConeEquiv.functor.mapIso lc.validLift.op

Depends on / 依赖: reflectsColimit_of_unop
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
/--
Definition of `createsLimitsOfShapeOp` / `createsLimitsOfShapeOp` 的定义

English:
definition createsLimitsOfShapeOp
  signature: (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F]
  body: createsLimitOp K F

中文:
定义 createsLimitsOfShapeOp
  签名: (F : C ⥤ D) [创造形状余极限 Jᵒᵖ F]
  定义体: createsLimitOp K F

Depends on / 依赖: createsLimitOp
-/
def createsLimitsOfShapeOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.op where CreatesLimit {K} := createsLimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeLeftOp` / `createsLimitsOfShapeLeftOp` 的定义

English:
definition createsLimitsOfShapeLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F]
  body: createsLimitLeftOp K F

中文:
定义 createsLimitsOfShapeLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造形状余极限 Jᵒᵖ F]
  定义体: createsLimitLeftOp K F

Depends on / 依赖: createsLimitLeftOp
-/
def createsLimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.leftOp where CreatesLimit {K} := createsLimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeRightOp` / `createsLimitsOfShapeRightOp` 的定义

English:
definition createsLimitsOfShapeRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F]
  body: createsLimitRightOp K F

中文:
定义 createsLimitsOfShapeRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造形状余极限 Jᵒᵖ F]
  定义体: createsLimitRightOp K F

Depends on / 依赖: createsLimitRightOp
-/
def createsLimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.rightOp where CreatesLimit {K} := createsLimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates limits of
shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeUnop` / `createsLimitsOfShapeUnop` 的定义

English:
definition createsLimitsOfShapeUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F]
  body: createsLimitUnop K F

中文:
定义 createsLimitsOfShapeUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造形状余极限 Jᵒᵖ F]
  定义体: createsLimitUnop K F

Depends on / 依赖: createsLimitUnop
-/
def createsLimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F] :
    CreatesLimitsOfShape J F.unop where CreatesLimit {K} := createsLimitUnop K F

/-- If `F : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of
shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOp` / `createsColimitsOfShapeOp` 的定义

English:
definition createsColimitsOfShapeOp
  signature: (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F]
  body: createsColimitOp K F

中文:
定义 createsColimitsOfShapeOp
  签名: (F : C ⥤ D) [创造形状极限 Jᵒᵖ F]
  定义体: createsColimitOp K F

Depends on / 依赖: createsColimitOp
-/
def createsColimitsOfShapeOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.op where CreatesColimit {K} := createsColimitOp K F

/-- If `F : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeLeftOp` / `createsColimitsOfShapeLeftOp` 的定义

English:
definition createsColimitsOfShapeLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F]
  body: createsColimitLeftOp K F

中文:
定义 createsColimitsOfShapeLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造形状极限 Jᵒᵖ F]
  定义体: createsColimitLeftOp K F

Depends on / 依赖: createsColimitLeftOp
-/
def createsColimitsOfShapeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.leftOp where CreatesColimit {K} := createsColimitLeftOp K F

/-- If `F : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeRightOp` / `createsColimitsOfShapeRightOp` 的定义

English:
definition createsColimitsOfShapeRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F]
  body: createsColimitRightOp K F

中文:
定义 createsColimitsOfShapeRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造形状极限 Jᵒᵖ F]
  定义体: createsColimitRightOp K F

Depends on / 依赖: createsColimitRightOp
-/
def createsColimitsOfShapeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.rightOp where CreatesColimit {K} := createsColimitRightOp K F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeUnop` / `createsColimitsOfShapeUnop` 的定义

English:
definition createsColimitsOfShapeUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F]
  body: createsColimitUnop K F

中文:
定义 createsColimitsOfShapeUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造形状极限 Jᵒᵖ F]
  定义体: createsColimitUnop K F

Depends on / 依赖: createsColimitUnop
-/
def createsColimitsOfShapeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F] :
    CreatesColimitsOfShape J F.unop where CreatesColimit {K} := createsColimitUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates limits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfOp` / `createsLimitsOfShapeOfOp` 的定义

English:
definition createsLimitsOfShapeOfOp
  signature: (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.op]
  body: createsLimitOfOp K F

中文:
定义 createsLimitsOfShapeOfOp
  签名: (F : C ⥤ D) [创造形状余极限 Jᵒᵖ F.op]
  定义体: createsLimitOfOp K F

Depends on / 依赖: createsLimitOfOp
-/
def createsLimitsOfShapeOfOp (F : C ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.op] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfLeftOp` / `createsLimitsOfShapeOfLeftOp` 的定义

English:
definition createsLimitsOfShapeOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.leftOp]
  body: createsLimitOfLeftOp K F

中文:
定义 createsLimitsOfShapeOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造形状余极限 Jᵒᵖ F.leftOp]
  定义体: createsLimitOfLeftOp K F

Depends on / 依赖: createsLimitOfLeftOp
-/
def createsLimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creates limits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfRightOp` / `createsLimitsOfShapeOfRightOp` 的定义

English:
definition createsLimitsOfShapeOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.rightOp]
  body: createsLimitOfRightOp K F

中文:
定义 createsLimitsOfShapeOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造形状余极限 Jᵒᵖ F.rightOp]
  定义体: createsLimitOfRightOp K F

Depends on / 依赖: createsLimitOfRightOp
-/
def createsLimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfRightOp K F

/-- If `F.unop : C ⥤ D` creates colimits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfUnop` / `createsLimitsOfShapeOfUnop` 的定义

English:
definition createsLimitsOfShapeOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.unop]
  body: createsLimitOfUnop K F

中文:
定义 createsLimitsOfShapeOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造形状余极限 Jᵒᵖ F.unop]
  定义体: createsLimitOfUnop K F

Depends on / 依赖: createsLimitOfUnop
-/
def createsLimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfShape Jᵒᵖ F.unop] :
    CreatesLimitsOfShape J F where CreatesLimit {K} := createsLimitOfUnop K F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfOp` / `createsColimitsOfShapeOfOp` 的定义

English:
definition createsColimitsOfShapeOfOp
  signature: (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.op]
  body: createsColimitOfOp K F

中文:
定义 createsColimitsOfShapeOfOp
  签名: (F : C ⥤ D) [创造形状极限 Jᵒᵖ F.op]
  定义体: createsColimitOfOp K F

Depends on / 依赖: createsColimitOfOp
-/
def createsColimitsOfShapeOfOp (F : C ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.op] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfOp K F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : C ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfLeftOp` / `createsColimitsOfShapeOfLeftOp` 的定义

English:
definition createsColimitsOfShapeOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.leftOp]
  body: createsColimitOfLeftOp K F

中文:
定义 createsColimitsOfShapeOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造形状极限 Jᵒᵖ F.leftOp]
  定义体: createsColimitOfLeftOp K F

Depends on / 依赖: createsColimitOfLeftOp
-/
def createsColimitsOfShapeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.leftOp] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfLeftOp K F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ D` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfRightOp` / `createsColimitsOfShapeOfRightOp` 的定义

English:
definition createsColimitsOfShapeOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.rightOp]
  body: createsColimitOfRightOp K F

中文:
定义 createsColimitsOfShapeOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造形状极限 Jᵒᵖ F.rightOp]
  定义体: createsColimitOfRightOp K F

Depends on / 依赖: createsColimitOfRightOp
-/
def createsColimitsOfShapeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfShape Jᵒᵖ F.rightOp] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfRightOp K F

/-- If `F.unop : C ⥤ D` creates limits of shape `Jᵒᵖ`, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits
of shape `J`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfUnop` / `createsColimitsOfShapeOfUnop` 的定义

English:
definition createsColimitsOfShapeOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.unop]
  body: createsColimitOfUnop K F

中文:
定义 createsColimitsOfShapeOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造形状极限 Jᵒᵖ F.unop]
  定义体: createsColimitOfUnop K F

Depends on / 依赖: createsColimitOfUnop
-/
def createsColimitsOfShapeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfShape Jᵒᵖ F.unop] :
    CreatesColimitsOfShape J F where CreatesColimit {K} := createsColimitOfUnop K F

end

/-- If `F : C ⥤ D` creates colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeOp` / `createsLimitsOfSizeOp` 的定义

English:
definition createsLimitsOfSizeOp
  signature: (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F]
  body: createsLimitsOfShapeOp _ _

中文:
定义 createsLimitsOfSizeOp
  签名: (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F]
  定义体: createsLimitsOfShapeOp _ _

Depends on / 依赖: createsLimitsOfShapeOp
-/
def createsLimitsOfSizeOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.op where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` creates colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeLeftOp` / `createsLimitsOfSizeLeftOp` 的定义

English:
definition createsLimitsOfSizeLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F]
  body: createsLimitsOfShapeLeftOp _ _

中文:
定义 createsLimitsOfSizeLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F]
  定义体: createsLimitsOfShapeLeftOp _ _

Depends on / 依赖: createsLimitsOfShapeLeftOp
-/
def createsLimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.leftOp where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` creates colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeRightOp` / `createsLimitsOfSizeRightOp` 的定义

English:
definition createsLimitsOfSizeRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F]
  body: createsLimitsOfShapeRightOp _ _

中文:
定义 createsLimitsOfSizeRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F]
  定义体: createsLimitsOfShapeRightOp _ _

Depends on / 依赖: createsLimitsOfShapeRightOp
-/
def createsLimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.rightOp where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F.unop : C ⥤ D` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeUnop` / `createsLimitsOfSizeUnop` 的定义

English:
definition createsLimitsOfSizeUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F]
  body: createsLimitsOfShapeUnop _ _

中文:
定义 createsLimitsOfSizeUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F]
  定义体: createsLimitsOfShapeUnop _ _

Depends on / 依赖: createsLimitsOfShapeUnop
-/
def createsLimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} F.unop where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeUnop _ _

/-- If `F : C ⥤ D` creates limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeOp` / `createsColimitsOfSizeOp` 的定义

English:
definition createsColimitsOfSizeOp
  signature: (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F]
  body: createsColimitsOfShapeOp _ _

中文:
定义 createsColimitsOfSizeOp
  签名: (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F]
  定义体: createsColimitsOfShapeOp _ _

Depends on / 依赖: createsColimitsOfShapeOp
-/
def createsColimitsOfSizeOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.op where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOp _ _

/-- If `F : C ⥤ Dᵒᵖ` creates limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeLeftOp` / `createsColimitsOfSizeLeftOp` 的定义

English:
definition createsColimitsOfSizeLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F]
  body: createsColimitsOfShapeLeftOp _ _

中文:
定义 createsColimitsOfSizeLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F]
  定义体: createsColimitsOfShapeLeftOp _ _

Depends on / 依赖: createsColimitsOfShapeLeftOp
-/
def createsColimitsOfSizeLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.leftOp where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeLeftOp _ _

/-- If `F : Cᵒᵖ ⥤ D` creates limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeRightOp` / `createsColimitsOfSizeRightOp` 的定义

English:
definition createsColimitsOfSizeRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F]
  body: createsColimitsOfShapeRightOp _ _

中文:
定义 createsColimitsOfSizeRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F]
  定义体: createsColimitsOfShapeRightOp _ _

Depends on / 依赖: createsColimitsOfShapeRightOp
-/
def createsColimitsOfSizeRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.rightOp where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeRightOp _ _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F.unop : C ⥤ D` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeUnop` / `createsColimitsOfSizeUnop` 的定义

English:
definition createsColimitsOfSizeUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F]
  body: createsColimitsOfShapeUnop _ _

中文:
定义 createsColimitsOfSizeUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F]
  定义体: createsColimitsOfShapeUnop _ _

Depends on / 依赖: createsColimitsOfShapeUnop
-/
def createsColimitsOfSizeUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} F.unop where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits, then `F : C ⥤ D` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeOfOp` / `createsLimitsOfSizeOfOp` 的定义

English:
definition createsLimitsOfSizeOfOp
  signature: (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op]
  body: createsLimitsOfShapeOfOp _ _

中文:
定义 createsLimitsOfSizeOfOp
  签名: (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op]
  定义体: createsLimitsOfShapeOfOp _ _

Depends on / 依赖: createsLimitsOfShapeOfOp
-/
def createsLimitsOfSizeOfOp (F : C ⥤ D) [CreatesColimitsOfSize.{w, w'} F.op] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates colimits, then `F : C ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeOfLeftOp` / `createsLimitsOfSizeOfLeftOp` 的定义

English:
definition createsLimitsOfSizeOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.leftOp]
  body: createsLimitsOfShapeOfLeftOp _ _

中文:
定义 createsLimitsOfSizeOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.leftOp]
  定义体: createsLimitsOfShapeOfLeftOp _ _

Depends on / 依赖: createsLimitsOfShapeOfLeftOp
-/
def createsLimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.leftOp] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates colimits, then `F : Cᵒᵖ ⥤ D` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeOfRightOp` / `createsLimitsOfSizeOfRightOp` 的定义

English:
definition createsLimitsOfSizeOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F.rightOp]
  body: createsLimitsOfShapeOfRightOp _ _

中文:
定义 createsLimitsOfSizeOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F.rightOp]
  定义体: createsLimitsOfShapeOfRightOp _ _

Depends on / 依赖: createsLimitsOfShapeOfRightOp
-/
def createsLimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimitsOfSize.{w, w'} F.rightOp] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` creates colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates limits. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeOfUnop` / `createsLimitsOfSizeOfUnop` 的定义

English:
definition createsLimitsOfSizeOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.unop]
  body: createsLimitsOfShapeOfUnop _ _

中文:
定义 createsLimitsOfSizeOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.unop]
  定义体: createsLimitsOfShapeOfUnop _ _

Depends on / 依赖: createsLimitsOfShapeOfUnop
-/
def createsLimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimitsOfSize.{w, w'} F.unop] :
    CreatesLimitsOfSize.{w, w'} F where
  CreatesLimitsOfShape {_} _ := createsLimitsOfShapeOfUnop _ _

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates limits, then `F : C ⥤ D` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeOfOp` / `createsColimitsOfSizeOfOp` 的定义

English:
definition createsColimitsOfSizeOfOp
  signature: (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op]
  body: createsColimitsOfShapeOfOp _ _

中文:
定义 createsColimitsOfSizeOfOp
  签名: (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op]
  定义体: createsColimitsOfShapeOfOp _ _

Depends on / 依赖: createsColimitsOfShapeOfOp
-/
def createsColimitsOfSizeOfOp (F : C ⥤ D) [CreatesLimitsOfSize.{w, w'} F.op] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfOp _ _

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates limits, then `F : C ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeOfLeftOp` / `createsColimitsOfSizeOfLeftOp` 的定义

English:
definition createsColimitsOfSizeOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.leftOp]
  body: createsColimitsOfShapeOfLeftOp _ _

中文:
定义 createsColimitsOfSizeOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.leftOp]
  定义体: createsColimitsOfShapeOfLeftOp _ _

Depends on / 依赖: createsColimitsOfShapeOfLeftOp
-/
def createsColimitsOfSizeOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.leftOp] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfLeftOp _ _

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates limits, then `F : Cᵒᵖ ⥤ D` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeOfRightOp` / `createsColimitsOfSizeOfRightOp` 的定义

English:
definition createsColimitsOfSizeOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F.rightOp]
  body: createsColimitsOfShapeOfRightOp _ _

中文:
定义 createsColimitsOfSizeOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F.rightOp]
  定义体: createsColimitsOfShapeOfRightOp _ _

Depends on / 依赖: createsColimitsOfShapeOfRightOp
-/
def createsColimitsOfSizeOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimitsOfSize.{w, w'} F.rightOp] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfRightOp _ _

/-- If `F.unop : C ⥤ D` creates limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeOfUnop` / `createsColimitsOfSizeOfUnop` 的定义

English:
definition createsColimitsOfSizeOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.unop]
  body: createsColimitsOfShapeOfUnop _ _

中文:
定义 createsColimitsOfSizeOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.unop]
  定义体: createsColimitsOfShapeOfUnop _ _

Depends on / 依赖: createsColimitsOfShapeOfUnop
-/
def createsColimitsOfSizeOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimitsOfSize.{w, w'} F.unop] :
    CreatesColimitsOfSize.{w, w'} F where
  CreatesColimitsOfShape {_} _ := createsColimitsOfShapeOfUnop _ _

/--
Definition of `createsLimitsOp` / `createsLimitsOp` 的定义

English:
abbreviation createsLimitsOp
  signature: (F : C ⥤ D) [CreatesColimits F]
  body: createsLimitsOfSizeOp F

中文:
缩写 createsLimitsOp
  签名: (F : C ⥤ D) [CreatesColimits F]
  定义体: createsLimitsOfSizeOp F

Depends on / 依赖: createsLimitsOfSizeOp
-/
abbrev createsLimitsOp (F : C ⥤ D) [CreatesColimits F] : CreatesLimits F.op :=
  createsLimitsOfSizeOp F

/--
Definition of `createsLimitsLeftOp` / `createsLimitsLeftOp` 的定义

English:
abbreviation createsLimitsLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesColimits F]
  body: createsLimitsOfSizeLeftOp F

中文:
缩写 createsLimitsLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesColimits F]
  定义体: createsLimitsOfSizeLeftOp F

Depends on / 依赖: createsLimitsOfSizeLeftOp
-/
abbrev createsLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.leftOp :=
  createsLimitsOfSizeLeftOp F

/--
Definition of `createsLimitsRightOp` / `createsLimitsRightOp` 的定义

English:
abbreviation createsLimitsRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesColimits F]
  body: createsLimitsOfSizeRightOp F

中文:
缩写 createsLimitsRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesColimits F]
  定义体: createsLimitsOfSizeRightOp F

Depends on / 依赖: createsLimitsOfSizeRightOp
-/
abbrev createsLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F] : CreatesLimits F.rightOp :=
  createsLimitsOfSizeRightOp F

/--
Definition of `createsLimitsUnop` / `createsLimitsUnop` 的定义

English:
abbreviation createsLimitsUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F]
  body: createsLimitsOfSizeUnop F

中文:
缩写 createsLimitsUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F]
  定义体: createsLimitsOfSizeUnop F

Depends on / 依赖: createsLimitsOfSizeUnop
-/
abbrev createsLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F] : CreatesLimits F.unop :=
  createsLimitsOfSizeUnop F

/--
Definition of `createsColimitsOp` / `createsColimitsOp` 的定义

English:
abbreviation createsColimitsOp
  signature: (F : C ⥤ D) [CreatesLimits F]
  body: createsColimitsOfSizeOp F

中文:
缩写 createsColimitsOp
  签名: (F : C ⥤ D) [CreatesLimits F]
  定义体: createsColimitsOfSizeOp F

Depends on / 依赖: createsColimitsOfSizeOp
-/
abbrev createsColimitsOp (F : C ⥤ D) [CreatesLimits F] : CreatesColimits F.op :=
  createsColimitsOfSizeOp F

/--
Definition of `createsColimitsLeftOp` / `createsColimitsLeftOp` 的定义

English:
abbreviation createsColimitsLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesLimits F]
  body: createsColimitsOfSizeLeftOp F

中文:
缩写 createsColimitsLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesLimits F]
  定义体: createsColimitsOfSizeLeftOp F

Depends on / 依赖: createsColimitsOfSizeLeftOp
-/
abbrev createsColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.leftOp :=
  createsColimitsOfSizeLeftOp F

/--
Definition of `createsColimitsRightOp` / `createsColimitsRightOp` 的定义

English:
abbreviation createsColimitsRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesLimits F]
  body: createsColimitsOfSizeRightOp F

中文:
缩写 createsColimitsRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesLimits F]
  定义体: createsColimitsOfSizeRightOp F

Depends on / 依赖: createsColimitsOfSizeRightOp
-/
abbrev createsColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F] : CreatesColimits F.rightOp :=
  createsColimitsOfSizeRightOp F

/--
Definition of `createsColimitsUnop` / `createsColimitsUnop` 的定义

English:
abbreviation createsColimitsUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F]
  body: createsColimitsOfSizeUnop F

中文:
缩写 createsColimitsUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F]
  定义体: createsColimitsOfSizeUnop F

Depends on / 依赖: createsColimitsOfSizeUnop
-/
abbrev createsColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F] : CreatesColimits F.unop :=
  createsColimitsOfSizeUnop F

/--
Definition of `createsLimitsOfOp` / `createsLimitsOfOp` 的定义

English:
abbreviation createsLimitsOfOp
  signature: (F : C ⥤ D) [CreatesColimits F.op]
  body: createsLimitsOfSizeOfOp F

中文:
缩写 createsLimitsOfOp
  签名: (F : C ⥤ D) [CreatesColimits F.op]
  定义体: createsLimitsOfSizeOfOp F

Depends on / 依赖: createsLimitsOfSizeOfOp
-/
abbrev createsLimitsOfOp (F : C ⥤ D) [CreatesColimits F.op] : CreatesLimits F :=
  createsLimitsOfSizeOfOp F

/--
Definition of `createsLimitsOfLeftOp` / `createsLimitsOfLeftOp` 的定义

English:
abbreviation createsLimitsOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp]
  body: createsLimitsOfSizeOfLeftOp F

中文:
缩写 createsLimitsOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp]
  定义体: createsLimitsOfSizeOfLeftOp F

Depends on / 依赖: createsLimitsOfSizeOfLeftOp
-/
abbrev createsLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesColimits F.leftOp] : CreatesLimits F :=
  createsLimitsOfSizeOfLeftOp F

/--
Definition of `createsLimitsOfRightOp` / `createsLimitsOfRightOp` 的定义

English:
abbreviation createsLimitsOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp]
  body: createsLimitsOfSizeOfRightOp F

中文:
缩写 createsLimitsOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp]
  定义体: createsLimitsOfSizeOfRightOp F

Depends on / 依赖: createsLimitsOfSizeOfRightOp
-/
abbrev createsLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesColimits F.rightOp] : CreatesLimits F :=
  createsLimitsOfSizeOfRightOp F

/--
Definition of `createsLimitsOfUnop` / `createsLimitsOfUnop` 的定义

English:
abbreviation createsLimitsOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop]
  body: createsLimitsOfSizeOfUnop F

中文:
缩写 createsLimitsOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop]
  定义体: createsLimitsOfSizeOfUnop F

Depends on / 依赖: createsLimitsOfSizeOfUnop
-/
abbrev createsLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesColimits F.unop] : CreatesLimits F :=
  createsLimitsOfSizeOfUnop F

/--
Definition of `createsColimitsOfOp` / `createsColimitsOfOp` 的定义

English:
abbreviation createsColimitsOfOp
  signature: (F : C ⥤ D) [CreatesLimits F.op]
  body: createsColimitsOfSizeOfOp F

中文:
缩写 createsColimitsOfOp
  签名: (F : C ⥤ D) [CreatesLimits F.op]
  定义体: createsColimitsOfSizeOfOp F

Depends on / 依赖: createsColimitsOfSizeOfOp
-/
abbrev createsColimitsOfOp (F : C ⥤ D) [CreatesLimits F.op] : CreatesColimits F :=
  createsColimitsOfSizeOfOp F

/--
Definition of `createsColimitsOfLeftOp` / `createsColimitsOfLeftOp` 的定义

English:
abbreviation createsColimitsOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp]
  body: createsColimitsOfSizeOfLeftOp F

中文:
缩写 createsColimitsOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp]
  定义体: createsColimitsOfSizeOfLeftOp F

Depends on / 依赖: createsColimitsOfSizeOfLeftOp
-/
abbrev createsColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesLimits F.leftOp] : CreatesColimits F :=
  createsColimitsOfSizeOfLeftOp F

/--
Definition of `createsColimitsOfRightOp` / `createsColimitsOfRightOp` 的定义

English:
abbreviation createsColimitsOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp]
  body: createsColimitsOfSizeOfRightOp F

中文:
缩写 createsColimitsOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp]
  定义体: createsColimitsOfSizeOfRightOp F

Depends on / 依赖: createsColimitsOfSizeOfRightOp
-/
abbrev createsColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesLimits F.rightOp] : CreatesColimits F :=
  createsColimitsOfSizeOfRightOp F

/--
Definition of `createsColimitsOfUnop` / `createsColimitsOfUnop` 的定义

English:
abbreviation createsColimitsOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop]
  body: createsColimitsOfSizeOfUnop F

中文:
缩写 createsColimitsOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop]
  定义体: createsColimitsOfSizeOfUnop F

Depends on / 依赖: createsColimitsOfSizeOfUnop
-/
abbrev createsColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesLimits F.unop] : CreatesColimits F :=
  createsColimitsOfSizeOfUnop F

/-- If `F : C ⥤ D` creates finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOp` / `createsFiniteLimitsOp` 的定义

English:
definition createsFiniteLimitsOp
  signature: (F : C ⥤ D) [CreatesFiniteColimits F]
  body: createsLimitsOfShapeOp J F

中文:
定义 createsFiniteLimitsOp
  签名: (F : C ⥤ D) [创造有限余极限 F]
  定义体: createsLimitsOfShapeOp J F

Depends on / 依赖: createsLimitsOfShapeOp
-/
def createsFiniteLimitsOp (F : C ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.op where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` creates finite colimits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsLeftOp` / `createsFiniteLimitsLeftOp` 的定义

English:
definition createsFiniteLimitsLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F]
  body: createsLimitsOfShapeLeftOp J F

中文:
定义 createsFiniteLimitsLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造有限余极限 F]
  定义体: createsLimitsOfShapeLeftOp J F

Depends on / 依赖: createsLimitsOfShapeLeftOp
-/
def createsFiniteLimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.leftOp where
  createsFiniteLimits J _ _ := createsLimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` creates finite colimits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsRightOp` / `createsFiniteLimitsRightOp` 的定义

English:
definition createsFiniteLimitsRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F]
  body: createsLimitsOfShapeRightOp J F

中文:
定义 createsFiniteLimitsRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造有限余极限 F]
  定义体: createsLimitsOfShapeRightOp J F

Depends on / 依赖: createsLimitsOfShapeRightOp
-/
def createsFiniteLimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.rightOp where
  createsFiniteLimits J _ _ := createsLimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F.unop : C ⥤ D` creates finite
limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsUnop` / `createsFiniteLimitsUnop` 的定义

English:
definition createsFiniteLimitsUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F]
  body: createsLimitsOfShapeUnop J F

中文:
定义 createsFiniteLimitsUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造有限余极限 F]
  定义体: createsLimitsOfShapeUnop J F

Depends on / 依赖: createsLimitsOfShapeUnop
-/
def createsFiniteLimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F] :
    CreatesFiniteLimits F.unop where
  createsFiniteLimits J _ _ := createsLimitsOfShapeUnop J F

/-- If `F : C ⥤ D` creates finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOp` / `createsFiniteColimitsOp` 的定义

English:
definition createsFiniteColimitsOp
  signature: (F : C ⥤ D) [CreatesFiniteLimits F]
  body: createsColimitsOfShapeOp J F

中文:
定义 createsFiniteColimitsOp
  签名: (F : C ⥤ D) [创造有限极限 F]
  定义体: createsColimitsOfShapeOp J F

Depends on / 依赖: createsColimitsOfShapeOp
-/
def createsFiniteColimitsOp (F : C ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.op where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOp J F

/-- If `F : C ⥤ Dᵒᵖ` creates finite limits, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsLeftOp` / `createsFiniteColimitsLeftOp` 的定义

English:
definition createsFiniteColimitsLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F]
  body: createsColimitsOfShapeLeftOp J F

中文:
定义 createsFiniteColimitsLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造有限极限 F]
  定义体: createsColimitsOfShapeLeftOp J F

Depends on / 依赖: createsColimitsOfShapeLeftOp
-/
def createsFiniteColimitsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.leftOp where
  createsFiniteColimits J _ _ := createsColimitsOfShapeLeftOp J F

/-- If `F : Cᵒᵖ ⥤ D` creates finite limits, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsRightOp` / `createsFiniteColimitsRightOp` 的定义

English:
definition createsFiniteColimitsRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F]
  body: createsColimitsOfShapeRightOp J F

中文:
定义 createsFiniteColimitsRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造有限极限 F]
  定义体: createsColimitsOfShapeRightOp J F

Depends on / 依赖: createsColimitsOfShapeRightOp
-/
def createsFiniteColimitsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.rightOp where
  createsFiniteColimits J _ _ := createsColimitsOfShapeRightOp J F

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F.unop : C ⥤ D` creates finite
colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsUnop` / `createsFiniteColimitsUnop` 的定义

English:
definition createsFiniteColimitsUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F]
  body: createsColimitsOfShapeUnop J F

中文:
定义 createsFiniteColimitsUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造有限极限 F]
  定义体: createsColimitsOfShapeUnop J F

Depends on / 依赖: createsColimitsOfShapeUnop
-/
def createsFiniteColimitsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F] :
    CreatesFiniteColimits F.unop where
  createsFiniteColimits J _ _ := createsColimitsOfShapeUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits, then `F : C ⥤ D` creates finite limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfOp` / `createsFiniteLimitsOfOp` 的定义

English:
definition createsFiniteLimitsOfOp
  signature: (F : C ⥤ D) [CreatesFiniteColimits F.op]
  body: createsLimitsOfShapeOfOp J F

中文:
定义 createsFiniteLimitsOfOp
  签名: (F : C ⥤ D) [创造有限余极限 F.op]
  定义体: createsLimitsOfShapeOfOp J F

Depends on / 依赖: createsLimitsOfShapeOfOp
-/
def createsFiniteLimitsOfOp (F : C ⥤ D) [CreatesFiniteColimits F.op] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates finite colimits, then `F : C ⥤ Dᵒᵖ` creates finite
limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfLeftOp` / `createsFiniteLimitsOfLeftOp` 的定义

English:
definition createsFiniteLimitsOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F.leftOp]
  body: createsLimitsOfShapeOfLeftOp J F

中文:
定义 createsFiniteLimitsOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造有限余极限 F.leftOp]
  定义体: createsLimitsOfShapeOfLeftOp J F

Depends on / 依赖: createsLimitsOfShapeOfLeftOp
-/
def createsFiniteLimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteColimits F.leftOp] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates finite colimits, then `F : Cᵒᵖ ⥤ D` creates finite
limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfRightOp` / `createsFiniteLimitsOfRightOp` 的定义

English:
definition createsFiniteLimitsOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F.rightOp]
  body: createsLimitsOfShapeOfRightOp J F

中文:
定义 createsFiniteLimitsOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造有限余极限 F.rightOp]
  定义体: createsLimitsOfShapeOfRightOp J F

Depends on / 依赖: createsLimitsOfShapeOfRightOp
-/
def createsFiniteLimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteColimits F.rightOp] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` creates finite colimits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfUnop` / `createsFiniteLimitsOfUnop` 的定义

English:
definition createsFiniteLimitsOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop]
  body: createsLimitsOfShapeOfUnop J F

中文:
定义 createsFiniteLimitsOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造有限余极限 F.unop]
  定义体: createsLimitsOfShapeOfUnop J F

Depends on / 依赖: createsLimitsOfShapeOfUnop
-/
def createsFiniteLimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteColimits F.unop] :
    CreatesFiniteLimits F where
  createsFiniteLimits J _ _ := createsLimitsOfShapeOfUnop J F

/-- If `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite limits, then `F : C ⥤ D` creates finite colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfOp` / `createsFiniteColimitsOfOp` 的定义

English:
definition createsFiniteColimitsOfOp
  signature: (F : C ⥤ D) [CreatesFiniteLimits F.op]
  body: createsColimitsOfShapeOfOp J F

中文:
定义 createsFiniteColimitsOfOp
  签名: (F : C ⥤ D) [创造有限极限 F.op]
  定义体: createsColimitsOfShapeOfOp J F

Depends on / 依赖: createsColimitsOfShapeOfOp
-/
def createsFiniteColimitsOfOp (F : C ⥤ D) [CreatesFiniteLimits F.op] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfOp J F

/-- If `F.leftOp : Cᵒᵖ ⥤ D` creates finite limits, then `F : C ⥤ Dᵒᵖ` creates finite
colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfLeftOp` / `createsFiniteColimitsOfLeftOp` 的定义

English:
definition createsFiniteColimitsOfLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F.leftOp]
  body: createsColimitsOfShapeOfLeftOp J F

中文:
定义 createsFiniteColimitsOfLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [创造有限极限 F.leftOp]
  定义体: createsColimitsOfShapeOfLeftOp J F

Depends on / 依赖: createsColimitsOfShapeOfLeftOp
-/
def createsFiniteColimitsOfLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteLimits F.leftOp] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfLeftOp J F

/-- If `F.rightOp : C ⥤ Dᵒᵖ` creates finite limits, then `F : Cᵒᵖ ⥤ D` creates finite
colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfRightOp` / `createsFiniteColimitsOfRightOp` 的定义

English:
definition createsFiniteColimitsOfRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F.rightOp]
  body: createsColimitsOfShapeOfRightOp J F

中文:
定义 createsFiniteColimitsOfRightOp
  签名: (F : Cᵒᵖ ⥤ D) [创造有限极限 F.rightOp]
  定义体: createsColimitsOfShapeOfRightOp J F

Depends on / 依赖: createsColimitsOfShapeOfRightOp
-/
def createsFiniteColimitsOfRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteLimits F.rightOp] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfRightOp J F

/-- If `F.unop : C ⥤ D` creates finite limits, then `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite colimits. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfUnop` / `createsFiniteColimitsOfUnop` 的定义

English:
definition createsFiniteColimitsOfUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F.unop]
  body: createsColimitsOfShapeOfUnop J F

中文:
定义 createsFiniteColimitsOfUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [创造有限极限 F.unop]
  定义体: createsColimitsOfShapeOfUnop J F

Depends on / 依赖: createsColimitsOfShapeOfUnop
-/
def createsFiniteColimitsOfUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteLimits F.unop] :
    CreatesFiniteColimits F where
  createsFiniteColimits J _ _ := createsColimitsOfShapeOfUnop J F

/-- If `F : C ⥤ D` creates finite coproducts, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
products. -/
@[instance_reducible]
/--
Definition of `createsFiniteProductsOp` / `createsFiniteProductsOp` 的定义

English:
definition createsFiniteProductsOp
  signature: (F : C ⥤ D) [CreatesFiniteCoproducts F]
  body: by
    apply +allowSynthFailures createsLimitsOfShapeOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteProductsOp
  签名: (F : C ⥤ D) [CreatesFiniteCoproducts F]
  定义体: by
    apply +allowSynthFailures createsLimitsOfShapeOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeOfEquiv, createsLimitsOfShapeOp, opposite
-/
def createsFiniteProductsOp (F : C ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.op where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` creates finite coproducts, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
products. -/
@[instance_reducible]
/--
Definition of `createsFiniteProductsLeftOp` / `createsFiniteProductsLeftOp` 的定义

English:
definition createsFiniteProductsLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F]
  body: by
    apply +allowSynthFailures createsLimitsOfShapeLeftOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteProductsLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F]
  定义体: by
    apply +allowSynthFailures createsLimitsOfShapeLeftOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeOfEquiv, createsLimitsOfShapeLeftOp, opposite
-/
def createsFiniteProductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.leftOp where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeLeftOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` creates finite coproducts, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
products. -/
@[instance_reducible]
/--
Definition of `createsFiniteProductsRightOp` / `createsFiniteProductsRightOp` 的定义

English:
definition createsFiniteProductsRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F]
  body: by
    apply +allowSynthFailures createsLimitsOfShapeRightOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteProductsRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F]
  定义体: by
    apply +allowSynthFailures createsLimitsOfShapeRightOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeOfEquiv, createsLimitsOfShapeRightOp, opposite
-/
def createsFiniteProductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.rightOp where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeRightOp
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite coproducts, then `F.unop : C ⥤ D` creates finite
products. -/
@[instance_reducible]
/--
Definition of `createsFiniteProductsUnop` / `createsFiniteProductsUnop` 的定义

English:
definition createsFiniteProductsUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F]
  body: by
    apply +allowSynthFailures createsLimitsOfShapeUnop
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteProductsUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F]
  定义体: by
    apply +allowSynthFailures createsLimitsOfShapeUnop
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeOfEquiv, createsLimitsOfShapeUnop, opposite
-/
def createsFiniteProductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteCoproducts F] :
    CreatesFiniteProducts F.unop where
  creates _ _ := by
    apply +allowSynthFailures createsLimitsOfShapeUnop
    exact createsColimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ D` creates finite products, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` creates finite
coproducts. -/
@[instance_reducible]
/--
Definition of `createsFiniteCoproductsOp` / `createsFiniteCoproductsOp` 的定义

English:
definition createsFiniteCoproductsOp
  signature: (F : C ⥤ D) [CreatesFiniteProducts F]
  body: by
    apply +allowSynthFailures createsColimitsOfShapeOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteCoproductsOp
  签名: (F : C ⥤ D) [CreatesFiniteProducts F]
  定义体: by
    apply +allowSynthFailures createsColimitsOfShapeOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeOp, createsLimitsOfShapeOfEquiv, opposite
-/
def createsFiniteCoproductsOp (F : C ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.op where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : C ⥤ Dᵒᵖ` creates finite products, then `F.leftOp : Cᵒᵖ ⥤ D` creates finite
coproducts. -/
@[instance_reducible]
/--
Definition of `createsFiniteCoproductsLeftOp` / `createsFiniteCoproductsLeftOp` 的定义

English:
definition createsFiniteCoproductsLeftOp
  signature: (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F]
  body: by
    apply +allowSynthFailures createsColimitsOfShapeLeftOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteCoproductsLeftOp
  签名: (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F]
  定义体: by
    apply +allowSynthFailures createsColimitsOfShapeLeftOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeLeftOp, createsLimitsOfShapeOfEquiv, opposite
-/
def createsFiniteCoproductsLeftOp (F : C ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.leftOp where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeLeftOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ D` creates finite products, then `F.rightOp : C ⥤ Dᵒᵖ` creates finite
coproducts. -/
@[instance_reducible]
/--
Definition of `createsFiniteCoproductsRightOp` / `createsFiniteCoproductsRightOp` 的定义

English:
definition createsFiniteCoproductsRightOp
  signature: (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F]
  body: by
    apply +allowSynthFailures createsColimitsOfShapeRightOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteCoproductsRightOp
  签名: (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F]
  定义体: by
    apply +allowSynthFailures createsColimitsOfShapeRightOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeRightOp, createsLimitsOfShapeOfEquiv, opposite
-/
def createsFiniteCoproductsRightOp (F : Cᵒᵖ ⥤ D) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.rightOp where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeRightOp
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` creates finite products, then `F.unop : C ⥤ D` creates finite
coproducts. -/
@[instance_reducible]
/--
Definition of `createsFiniteCoproductsUnop` / `createsFiniteCoproductsUnop` 的定义

English:
definition createsFiniteCoproductsUnop
  signature: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F]
  body: by
    apply +allowSynthFailures createsColimitsOfShapeUnop
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

中文:
定义 createsFiniteCoproductsUnop
  签名: (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F]
  定义体: by
    apply +allowSynthFailures createsColimitsOfShapeUnop
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, createsColimitsOfShapeUnop, createsLimitsOfShapeOfEquiv, opposite
-/
def createsFiniteCoproductsUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) [CreatesFiniteProducts F] :
    CreatesFiniteCoproducts F.unop where
  creates _ _ := by
    apply +allowSynthFailures createsColimitsOfShapeUnop
    exact createsLimitsOfShapeOfEquiv (Discrete.opposite _).symm _

end CategoryTheory.Limits
