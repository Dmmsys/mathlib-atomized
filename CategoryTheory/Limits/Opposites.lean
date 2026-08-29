/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We construct limits and colimits in the opposite categories.

-/

@[expose] public section


universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps]
/--
Definition of `isLimitConeLeftOpOfCocone` / `isLimitConeLeftOpOfCocone` 的定义

English:
definition isLimitConeLeftOpOfCocone
  signature: (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c)
  body: (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
Quiver.Hom.op_inj by
      simp only [coneLeftOpOfCocone_π_app, op_comp, Quiver.Hom.op_unop, IsColimit.fac,
        coconeOfConeLeftOp_ι_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    s

中文:
定义 isLimitConeLeftOpOfCocone
  签名: (F : J ⥤ Cᵒᵖ) {c : 余锥 F} (hc : 是余极限 c)
  定义体: (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
Quiver.Hom.op_inj by
      simp only [coneLeftOpOfCocone_π_app, op_comp, Quiver.Hom.op_unop, IsColimit.fac,
        coconeOfConeLeftOp_ι_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    s

Depends on / 依赖: coconeOfConeLeftOp, hc.desc
-/
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneLeftOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
Quiver.Hom.op_inj by
      simp only [coneLeftOpOfCocone_π_app, op_comp, Quiver.Hom.op_unop, IsColimit.fac,
        coconeOfConeLeftOp_ι_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac, coconeOfConeLeftOp_ι_app] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps]
/--
Definition of `isColimitCoconeLeftOpOfCone` / `isColimitCoconeLeftOpOfCone` 的定义

English:
definition isColimitCoconeLeftOpOfCone
  signature: (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c)
  body: (hc.lift (coneOfCoconeLeftOp s)).unop
  fac s j :=
Quiver.Hom.op_inj by
      simp only [coconeLeftOpOfCone_ι_app, op_comp, Quiver.Hom.op_unop, IsLimit.fac,
        coneOfCoconeLeftOp_π_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    sim

中文:
定义 isColimitCoconeLeftOpOfCone
  签名: (F : J ⥤ Cᵒᵖ) {c : 锥 F} (hc : 是极限 c)
  定义体: (hc.lift (coneOfCoconeLeftOp s)).unop
  fac s j :=
Quiver.Hom.op_inj by
      simp only [coconeLeftOpOfCone_ι_app, op_comp, Quiver.Hom.op_unop, IsLimit.fac,
        coneOfCoconeLeftOp_π_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    sim

Depends on / 依赖: coneOfCoconeLeftOp, hc.lift
-/
def isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeLeftOpOfCone c) where
  desc s := (hc.lift (coneOfCoconeLeftOp s)).unop
  fac s j :=
Quiver.Hom.op_inj by
      simp only [coconeLeftOpOfCone_ι_app, op_comp, Quiver.Hom.op_unop, IsLimit.fac,
        coneOfCoconeLeftOp_π_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac, coneOfCoconeLeftOp_π_app] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps]
/--
Definition of `isLimitConeRightOpOfCocone` / `isLimitConeRightOpOfCocone` 的定义

English:
definition isLimitConeRightOpOfCocone
  signature: (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c)
  body: (hc.desc (coconeOfConeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (unop j)

中文:
定义 isLimitConeRightOpOfCocone
  签名: (F : Jᵒᵖ ⥤ C) {c : 余锥 F} (hc : 是余极限 c)
  定义体: (hc.desc (coconeOfConeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (unop j)

Depends on / 依赖: coconeOfConeRightOp, hc.desc
-/
def isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneRightOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps]
/--
Definition of `isColimitCoconeRightOpOfCone` / `isColimitCoconeRightOpOfCone` 的定义

English:
definition isColimitCoconeRightOpOfCone
  signature: (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c)
  body: (hc.lift (coneOfCoconeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using! w (unop j)

中文:
定义 isColimitCoconeRightOpOfCone
  签名: (F : Jᵒᵖ ⥤ C) {c : 锥 F} (hc : 是极限 c)
  定义体: (hc.lift (coneOfCoconeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using! w (unop j)

Depends on / 依赖: coneOfCoconeRightOp, hc.lift
-/
def isColimitCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeRightOpOfCone c) where
  desc s := (hc.lift (coneOfCoconeRightOp s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps]
/--
Definition of `isLimitConeUnopOfCocone` / `isLimitConeUnopOfCocone` 的定义

English:
definition isLimitConeUnopOfCocone
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c)
  body: (hc.desc (coconeOfConeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (unop j)

中文:
定义 isLimitConeUnopOfCocone
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 余锥 F} (hc : 是余极限 c)
  定义体: (hc.desc (coconeOfConeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (unop j)

Depends on / 依赖: coconeOfConeUnop, hc.desc
-/
def isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneUnopOfCocone c) where
  lift s := (hc.desc (coconeOfConeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/
@[simps]
/--
Definition of `isColimitCoconeUnopOfCone` / `isColimitCoconeUnopOfCone` 的定义

English:
definition isColimitCoconeUnopOfCone
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c)
  body: (hc.lift (coneOfCoconeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (unop j)

中文:
定义 isColimitCoconeUnopOfCone
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 锥 F} (hc : 是极限 c)
  定义体: (hc.lift (coneOfCoconeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (unop j)

Depends on / 依赖: coneOfCoconeUnop, hc.lift
-/
def isColimitCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeUnopOfCone c) where
  desc s := (hc.lift (coneOfCoconeUnop s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps]
/--
Definition of `isLimitConeOfCoconeLeftOp` / `isLimitConeOfCoconeLeftOp` 的定义

English:
definition isLimitConeOfCoconeLeftOp
  signature: (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c)
  body: (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
Quiver.Hom.unop_inj by
      simp only [coneOfCoconeLeftOp_π_app, unop_comp, Quiver.Hom.unop_op, IsColimit.fac,
        coconeLeftOpOfCone_ι_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
   

中文:
定义 isLimitConeOfCoconeLeftOp
  签名: (F : J ⥤ Cᵒᵖ) {c : 余锥 F.leftOp} (hc : 是余极限 c)
  定义体: (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
Quiver.Hom.unop_inj by
      simp only [coneOfCoconeLeftOp_π_app, unop_comp, Quiver.Hom.unop_op, IsColimit.fac,
        coconeLeftOpOfCone_ι_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
   

Depends on / 依赖: coconeLeftOpOfCone, hc.desc
-/
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c) where
  lift s := (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
Quiver.Hom.unop_inj by
      simp only [coneOfCoconeLeftOp_π_app, unop_comp, Quiver.Hom.unop_op, IsColimit.fac,
        coconeLeftOpOfCone_ι_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac, coneOfCoconeLeftOp_π_app] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit of `F.leftOp : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps]
/--
Definition of `isColimitCoconeOfConeLeftOp` / `isColimitCoconeOfConeLeftOp` 的定义

English:
definition isColimitCoconeOfConeLeftOp
  signature: (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c)
  body: (hc.lift (coneLeftOpOfCocone s)).op
  fac s j :=
Quiver.Hom.unop_inj by
      simp only [coconeOfConeLeftOp_ι_app, unop_comp, Quiver.Hom.unop_op, IsLimit.fac,
        coneLeftOpOfCocone_π_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    s

中文:
定义 isColimitCoconeOfConeLeftOp
  签名: (F : J ⥤ Cᵒᵖ) {c : 锥 F.leftOp} (hc : 是极限 c)
  定义体: (hc.lift (coneLeftOpOfCocone s)).op
  fac s j :=
Quiver.Hom.unop_inj by
      simp only [coconeOfConeLeftOp_ι_app, unop_comp, Quiver.Hom.unop_op, IsLimit.fac,
        coneLeftOpOfCocone_π_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    s

Depends on / 依赖: coneLeftOpOfCocone, hc.lift
-/
def isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeLeftOp c) where
  desc s := (hc.lift (coneLeftOpOfCocone s)).op
  fac s j :=
Quiver.Hom.unop_inj by
      simp only [coconeOfConeLeftOp_ι_app, unop_comp, Quiver.Hom.unop_op, IsLimit.fac,
        coneLeftOpOfCocone_π_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac, coconeOfConeLeftOp_ι_app] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
/--
Definition of `isLimitConeOfCoconeRightOp` / `isLimitConeOfCoconeRightOp` 的定义

English:
definition isLimitConeOfCoconeRightOp
  signature: (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c)
  body: (hc.desc (coconeRightOpOfCone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (op j)

中文:
定义 isLimitConeOfCoconeRightOp
  签名: (F : Jᵒᵖ ⥤ C) {c : 余锥 F.rightOp} (hc : 是余极限 c)
  定义体: (hc.desc (coconeRightOpOfCone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (op j)

Depends on / 依赖: coconeRightOpOfCone, hc.desc
-/
def isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeRightOp c) where
  lift s := (hc.desc (coconeRightOpOfCone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
/--
Definition of `isColimitCoconeOfConeRightOp` / `isColimitCoconeOfConeRightOp` 的定义

English:
definition isColimitCoconeOfConeRightOp
  signature: (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c)
  body: (hc.lift (coneRightOpOfCocone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (op j)

中文:
定义 isColimitCoconeOfConeRightOp
  签名: (F : Jᵒᵖ ⥤ C) {c : 锥 F.rightOp} (hc : 是极限 c)
  定义体: (hc.lift (coneRightOpOfCocone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (op j)

Depends on / 依赖: coneRightOpOfCocone, hc.lift
-/
def isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeRightOp c) where
  desc s := (hc.lift (coneRightOpOfCocone s)).unop
  fac s j := Quiver.Hom.op_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
/--
Definition of `isLimitConeOfCoconeUnop` / `isLimitConeOfCoconeUnop` 的定义

English:
definition isLimitConeOfCoconeUnop
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c)
  body: (hc.desc (coconeUnopOfCone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (op j)

中文:
定义 isLimitConeOfCoconeUnop
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 余锥 F.unop} (hc : 是余极限 c)
  定义体: (hc.desc (coconeUnopOfCone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (op j)

Depends on / 依赖: coconeUnopOfCone, hc.desc
-/
def isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c) :
    IsLimit (coneOfCoconeUnop c) where
  lift s := (hc.desc (coconeUnopOfCone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
/--
Definition of `isColimitCoconeOfConeUnop` / `isColimitCoconeOfConeUnop` 的定义

English:
definition isColimitCoconeOfConeUnop
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c)
  body: (hc.lift (coneUnopOfCocone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using! w (op j)

中文:
定义 isColimitCoconeOfConeUnop
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 锥 F.unop} (hc : 是极限 c)
  定义体: (hc.lift (coneUnopOfCocone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using! w (op j)

Depends on / 依赖: coneUnopOfCocone, hc.lift
-/
def isColimitCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c) :
    IsColimit (coconeOfConeUnop c) where
  desc s := (hc.lift (coneUnopOfCocone s)).op
  fac s j := Quiver.Hom.unop_inj (by simp)
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac] using! w (op j)

/-- Turn a limit for `F.leftOp : Jᵒᵖ ⥤ C` into a colimit for `F : J ⥤ Cᵒᵖ`. -/
@[simps!]
/--
Definition of `isColimitOfConeLeftOpOfCocone` / `isColimitOfConeLeftOpOfCocone` 的定义

English:
definition isColimitOfConeLeftOpOfCocone
  signature: (F : J ⥤ Cᵒᵖ) {c : Cocone F}
  body: isColimitCoconeOfConeLeftOp F hc

中文:
定义 isColimitOfConeLeftOpOfCocone
  签名: (F : J ⥤ Cᵒᵖ) {c : 余锥 F}
  定义体: isColimitCoconeOfConeLeftOp F hc

Depends on / 依赖: isColimitCoconeOfConeLeftOp
-/
def isColimitOfConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneLeftOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeLeftOp F hc

/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps!]
/--
Definition of `isLimitOfCoconeLeftOpOfCone` / `isLimitOfCoconeLeftOpOfCone` 的定义

English:
definition isLimitOfCoconeLeftOpOfCone
  signature: (F : J ⥤ Cᵒᵖ) {c : Cone F}
  body: isLimitConeOfCoconeLeftOp F hc

中文:
定义 isLimitOfCoconeLeftOpOfCone
  签名: (F : J ⥤ Cᵒᵖ) {c : 锥 F}
  定义体: isLimitConeOfCoconeLeftOp F hc

Depends on / 依赖: isLimitConeOfCoconeLeftOp
-/
def isLimitOfCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F}
    (hc : IsColimit (coconeLeftOpOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeLeftOp F hc

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
@[simps!]
/--
Definition of `isColimitOfConeRightOpOfCocone` / `isColimitOfConeRightOpOfCocone` 的定义

English:
definition isColimitOfConeRightOpOfCocone
  signature: (F : Jᵒᵖ ⥤ C) {c : Cocone F}
  body: isColimitCoconeOfConeRightOp F hc

中文:
定义 isColimitOfConeRightOpOfCocone
  签名: (F : Jᵒᵖ ⥤ C) {c : 余锥 F}
  定义体: isColimitCoconeOfConeRightOp F hc

Depends on / 依赖: isColimitCoconeOfConeRightOp
-/
def isColimitOfConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F}
    (hc : IsLimit (coneRightOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeRightOp F hc

/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps!]
/--
Definition of `isLimitOfCoconeRightOpOfCone` / `isLimitOfCoconeRightOpOfCone` 的定义

English:
definition isLimitOfCoconeRightOpOfCone
  signature: (F : Jᵒᵖ ⥤ C) {c : Cone F}
  body: isLimitConeOfCoconeRightOp F hc

中文:
定义 isLimitOfCoconeRightOpOfCone
  签名: (F : Jᵒᵖ ⥤ C) {c : 锥 F}
  定义体: isLimitConeOfCoconeRightOp F hc

Depends on / 依赖: isLimitConeOfCoconeRightOp
-/
def isLimitOfCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F}
    (hc : IsColimit (coconeRightOpOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeRightOp F hc

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps!]
/--
Definition of `isColimitOfConeUnopOfCocone` / `isColimitOfConeUnopOfCocone` 的定义

English:
definition isColimitOfConeUnopOfCocone
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F}
  body: isColimitCoconeOfConeUnop F hc

中文:
定义 isColimitOfConeUnopOfCocone
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 余锥 F}
  定义体: isColimitCoconeOfConeUnop F hc

Depends on / 依赖: isColimitCoconeOfConeUnop
-/
def isColimitOfConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneUnopOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeUnop F hc

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps!]
/--
Definition of `isLimitOfCoconeUnopOfCone` / `isLimitOfCoconeUnopOfCone` 的定义

English:
definition isLimitOfCoconeUnopOfCone
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F}
  body: isLimitConeOfCoconeUnop F hc

中文:
定义 isLimitOfCoconeUnopOfCone
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 锥 F}
  定义体: isLimitConeOfCoconeUnop F hc

Depends on / 依赖: isLimitConeOfCoconeUnop
-/
def isLimitOfCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F}
    (hc : IsColimit (coconeUnopOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeUnop F hc

/-- Turn a limit for `F : J ⥤ Cᵒᵖ` into a colimit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
/--
Definition of `isColimitOfConeOfCoconeLeftOp` / `isColimitOfConeOfCoconeLeftOp` 的定义

English:
definition isColimitOfConeOfCoconeLeftOp
  signature: (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp}
  body: isColimitCoconeLeftOpOfCone F hc

中文:
定义 isColimitOfConeOfCoconeLeftOp
  签名: (F : J ⥤ Cᵒᵖ) {c : 余锥 F.leftOp}
  定义体: isColimitCoconeLeftOpOfCone F hc

Depends on / 依赖: isColimitCoconeLeftOpOfCone
-/
def isColimitOfConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp}
    (hc : IsLimit (coneOfCoconeLeftOp c)) : IsColimit c :=
  isColimitCoconeLeftOpOfCone F hc

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
/--
Definition of `isLimitOfCoconeOfConeLeftOp` / `isLimitOfCoconeOfConeLeftOp` 的定义

English:
definition isLimitOfCoconeOfConeLeftOp
  signature: (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp}
  body: isLimitConeLeftOpOfCocone F hc

中文:
定义 isLimitOfCoconeOfConeLeftOp
  签名: (F : J ⥤ Cᵒᵖ) {c : 锥 F.leftOp}
  定义体: isLimitConeLeftOpOfCocone F hc

Depends on / 依赖: isLimitConeLeftOpOfCocone
-/
def isLimitOfCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp}
    (hc : IsColimit (coconeOfConeLeftOp c)) : IsLimit c :=
  isLimitConeLeftOpOfCocone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ.` -/
@[simps!]
/--
Definition of `isColimitOfConeOfCoconeRightOp` / `isColimitOfConeOfCoconeRightOp` 的定义

English:
definition isColimitOfConeOfCoconeRightOp
  signature: (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp}
  body: isColimitCoconeRightOpOfCone F hc

中文:
定义 isColimitOfConeOfCoconeRightOp
  签名: (F : Jᵒᵖ ⥤ C) {c : 余锥 F.rightOp}
  定义体: isColimitCoconeRightOpOfCone F hc

Depends on / 依赖: isColimitCoconeRightOpOfCone
-/
def isColimitOfConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp}
    (hc : IsLimit (coneOfCoconeRightOp c)) : IsColimit c :=
  isColimitCoconeRightOpOfCone F hc

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps!]
/--
Definition of `isLimitOfCoconeOfConeRightOp` / `isLimitOfCoconeOfConeRightOp` 的定义

English:
definition isLimitOfCoconeOfConeRightOp
  signature: (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp}
  body: isLimitConeRightOpOfCocone F hc

中文:
定义 isLimitOfCoconeOfConeRightOp
  签名: (F : Jᵒᵖ ⥤ C) {c : 锥 F.rightOp}
  定义体: isLimitConeRightOpOfCocone F hc

Depends on / 依赖: isLimitConeRightOpOfCocone
-/
def isLimitOfCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp}
    (hc : IsColimit (coconeOfConeRightOp c)) : IsLimit c :=
  isLimitConeRightOpOfCocone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F.unop : J ⥤ C`. -/
@[simps!]
/--
Definition of `isColimitOfConeOfCoconeUnop` / `isColimitOfConeOfCoconeUnop` 的定义

English:
definition isColimitOfConeOfCoconeUnop
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop}
  body: isColimitCoconeUnopOfCone F hc

中文:
定义 isColimitOfConeOfCoconeUnop
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 余锥 F.unop}
  定义体: isColimitCoconeUnopOfCone F hc

Depends on / 依赖: isColimitCoconeUnopOfCone
-/
def isColimitOfConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop}
    (hc : IsLimit (coneOfCoconeUnop c)) : IsColimit c :=
  isColimitCoconeUnopOfCone F hc

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps!]
/--
Definition of `isLimitOfCoconeOfConeUnop` / `isLimitOfCoconeOfConeUnop` 的定义

English:
definition isLimitOfCoconeOfConeUnop
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop}
  body: isLimitConeUnopOfCocone F hc

中文:
定义 isLimitOfCoconeOfConeUnop
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : 锥 F.unop}
  定义体: isLimitConeUnopOfCocone F hc

Depends on / 依赖: isLimitConeUnopOfCocone
-/
def isLimitOfCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop}
    (hc : IsColimit (coconeOfConeUnop c)) : IsLimit c :=
  isLimitConeUnopOfCocone F hc

/--
theorem `hasLimit_of_hasColimit_leftOp` / 定理 `hasLimit_of_hasColimit_leftOp`

English:
theorem hasLimit_of_hasColimit_leftOp
  given: (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp]
  statement: HasLimit F
  proof: HasLimit.mk
    { cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      isLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

中文:
定理 hasLimit_of_hasColimit_leftOp
  条件: (F : J ⥤ Cᵒᵖ) [有余极限 F.leftOp]
  结论: 有极限 F
  证明: HasLimit.mk
    { cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      isLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

Depends on / 依赖: F.leftOp, HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, coneOfCoconeLeftOp, isColimit, isLimit, isLimitConeOfCoconeLeftOp, leftOp
-/
theorem hasLimit_of_hasColimit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      isLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

/--
theorem `hasLimit_of_hasColimit_op` / 定理 `hasLimit_of_hasColimit_op`

English:
theorem hasLimit_of_hasColimit_op
  given: (F : J ⥤ C) [HasColimit F.op]
  statement: HasLimit F
  proof: HasLimit.mk
    { cone := (colimit.cocone F.op).unop
      isLimit := (colimit.isColimit _).unop }

中文:
定理 hasLimit_of_hasColimit_op
  条件: (F : J ⥤ C) [有余极限 F.op]
  结论: 有极限 F
  证明: HasLimit.mk
    { cone := (colimit.cocone F.op).unop
      isLimit := (colimit.isColimit _).unop }

Depends on / 依赖: F.op, HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, isColimit, isLimit
-/
theorem hasLimit_of_hasColimit_op (F : J ⥤ C) [HasColimit F.op] : HasLimit F :=
  HasLimit.mk
    { cone := (colimit.cocone F.op).unop
      isLimit := (colimit.isColimit _).unop }

/--
theorem `hasLimit_of_hasColimit_rightOp` / 定理 `hasLimit_of_hasColimit_rightOp`

English:
theorem hasLimit_of_hasColimit_rightOp
  given: (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp]
  statement: HasLimit F
  proof: HasLimit.mk
    { cone := coneOfCoconeRightOp (colimit.cocone F.rightOp)
      isLimit := isLimitConeOfCoconeRightOp _ (colimit.isColimit _) }

中文:
定理 hasLimit_of_hasColimit_rightOp
  条件: (F : Jᵒᵖ ⥤ C) [有余极限 F.rightOp]
  结论: 有极限 F
  证明: HasLimit.mk
    { cone := coneOfCoconeRightOp (colimit.cocone F.rightOp)
      isLimit := isLimitConeOfCoconeRightOp _ (colimit.isColimit _) }

Depends on / 依赖: F.rightOp, HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, coneOfCoconeRightOp, isColimit, isLimit, isLimitConeOfCoconeRightOp, rightOp
-/
theorem hasLimit_of_hasColimit_rightOp (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeRightOp (colimit.cocone F.rightOp)
      isLimit := isLimitConeOfCoconeRightOp _ (colimit.isColimit _) }

/--
theorem `hasLimit_of_hasColimit_unop` / 定理 `hasLimit_of_hasColimit_unop`

English:
theorem hasLimit_of_hasColimit_unop
  given: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F.unop]
  statement: HasLimit F
  proof: HasLimit.mk
    { cone := coneOfCoconeUnop (colimit.cocone F.unop)
      isLimit := isLimitConeOfCoconeUnop _ (colimit.isColimit _) }

中文:
定理 hasLimit_of_hasColimit_unop
  条件: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有余极限 F.unop]
  结论: 有极限 F
  证明: HasLimit.mk
    { cone := coneOfCoconeUnop (colimit.cocone F.unop)
      isLimit := isLimitConeOfCoconeUnop _ (colimit.isColimit _) }

Depends on / 依赖: F.unop, HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, coneOfCoconeUnop, isColimit, isLimit, isLimitConeOfCoconeUnop
-/
theorem hasLimit_of_hasColimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F.unop] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeUnop (colimit.cocone F.unop)
      isLimit := isLimitConeOfCoconeUnop _ (colimit.isColimit _) }

/--
Instance `hasLimit_op_of_hasColimit` / 实例 `hasLimit_op_of_hasColimit`

English:
instance hasLimit_op_of_hasColimit
  signature: (F : J ⥤ C) [HasColimit F]
  body: HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }

中文:
实例 hasLimit_op_of_hasColimit
  签名: (F : J ⥤ C) [有余极限 F]
  定义体: HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }

Depends on / 依赖: HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, isColimit, isLimit
-/
instance hasLimit_op_of_hasColimit (F : J ⥤ C) [HasColimit F] : HasLimit F.op :=
  HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }

/--
Instance `hasLimit_leftOp_of_hasColimit` / 实例 `hasLimit_leftOp_of_hasColimit`

English:
instance hasLimit_leftOp_of_hasColimit
  signature: (F : J ⥤ Cᵒᵖ) [HasColimit F]
  body: HasLimit.mk
    { cone := coneLeftOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeLeftOpOfCocone _ (colimit.isColimit _) }

中文:
实例 hasLimit_leftOp_of_hasColimit
  签名: (F : J ⥤ Cᵒᵖ) [有余极限 F]
  定义体: HasLimit.mk
    { cone := coneLeftOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeLeftOpOfCocone _ (colimit.isColimit _) }

Depends on / 依赖: HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, coneLeftOpOfCocone, isColimit, isLimit, isLimitConeLeftOpOfCocone
-/
instance hasLimit_leftOp_of_hasColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.leftOp :=
  HasLimit.mk
    { cone := coneLeftOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeLeftOpOfCocone _ (colimit.isColimit _) }

/--
Instance `hasLimit_rightOp_of_hasColimit` / 实例 `hasLimit_rightOp_of_hasColimit`

English:
instance hasLimit_rightOp_of_hasColimit
  signature: (F : Jᵒᵖ ⥤ C) [HasColimit F]
  body: HasLimit.mk
    { cone := coneRightOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeRightOpOfCocone _ (colimit.isColimit _) }

中文:
实例 hasLimit_rightOp_of_hasColimit
  签名: (F : Jᵒᵖ ⥤ C) [有余极限 F]
  定义体: HasLimit.mk
    { cone := coneRightOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeRightOpOfCocone _ (colimit.isColimit _) }

Depends on / 依赖: HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, coneRightOpOfCocone, isColimit, isLimit, isLimitConeRightOpOfCocone
-/
instance hasLimit_rightOp_of_hasColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] : HasLimit F.rightOp :=
  HasLimit.mk
    { cone := coneRightOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeRightOpOfCocone _ (colimit.isColimit _) }

/--
Instance `hasLimit_unop_of_hasColimit` / 实例 `hasLimit_unop_of_hasColimit`

English:
instance hasLimit_unop_of_hasColimit
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F]
  body: HasLimit.mk
    { cone := coneUnopOfCocone (colimit.cocone F)
      isLimit := isLimitConeUnopOfCocone _ (colimit.isColimit _) }

中文:
实例 hasLimit_unop_of_hasColimit
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有余极限 F]
  定义体: HasLimit.mk
    { cone := coneUnopOfCocone (colimit.cocone F)
      isLimit := isLimitConeUnopOfCocone _ (colimit.isColimit _) }

Depends on / 依赖: HasLimit, HasLimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, coneUnopOfCocone, isColimit, isLimit, isLimitConeUnopOfCocone
-/
instance hasLimit_unop_of_hasColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.unop :=
  HasLimit.mk
    { cone := coneUnopOfCocone (colimit.cocone F)
      isLimit := isLimitConeUnopOfCocone _ (colimit.isColimit _) }

/--
Definition of `limitOpIsoOpColimit` / `limitOpIsoOpColimit` 的定义

English:
definition limitOpIsoOpColimit
  signature: (F : J ⥤ C) [HasColimit F]
  body: limit.isoLimitCone ⟨_, (colimit.isColimit _).op⟩

中文:
定义 limitOpIsoOpColimit
  签名: (F : J ⥤ C) [有余极限 F]
  定义体: limit.isoLimitCone ⟨_, (colimit.isColimit _).op⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isoLimitCone, limit.isoLimitCone
-/
def limitOpIsoOpColimit (F : J ⥤ C) [HasColimit F] :
    limit F.op ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, (colimit.isColimit _).op⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitOpIsoOpColimit_inv_comp_π` / 引理 `limitOpIsoOpColimit_inv_comp_π`

English:
lemma limitOpIsoOpColimit_inv_comp_π
  given: (F : J ⥤ C) [HasColimit F] (j : Jᵒᵖ)
  proof: by
  simp [limitOpIsoOpColimit]

中文:
引理 limitOpIsoOpColimit_inv_comp_π
  条件: (F : J ⥤ C) [有余极限 F] (j : Jᵒᵖ)
  证明: by
  simp [limitOpIsoOpColimit]

Depends on / 依赖: limitOpIsoOpColimit
-/
lemma limitOpIsoOpColimit_inv_comp_π (F : J ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitOpIsoOpColimit F).inv ≫ limit.π F.op j = (colimit.ι F j.unop).op := by
  simp [limitOpIsoOpColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitOpIsoOpColimit_hom_comp_ι` / 引理 `limitOpIsoOpColimit_hom_comp_ι`

English:
lemma limitOpIsoOpColimit_hom_comp_ι
  given: (F : J ⥤ C) [HasColimit F] (j : J)
  proof: by
  simp [← Iso.eq_inv_comp]

中文:
引理 limitOpIsoOpColimit_hom_comp_ι
  条件: (F : J ⥤ C) [有余极限 F] (j : J)
  证明: by
  simp [← Iso.eq_inv_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
lemma limitOpIsoOpColimit_hom_comp_ι (F : J ⥤ C) [HasColimit F] (j : J) :
    (limitOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.op (op j) := by
  simp [← Iso.eq_inv_comp]

/--
Definition of `limitLeftOpIsoUnopColimit` / `limitLeftOpIsoUnopColimit` 的定义

English:
definition limitLeftOpIsoUnopColimit
  signature: (F : J ⥤ Cᵒᵖ) [HasColimit F]
  body: limit.isoLimitCone ⟨_, isLimitConeLeftOpOfCocone _ (colimit.isColimit _)⟩

中文:
定义 limitLeftOpIsoUnopColimit
  签名: (F : J ⥤ Cᵒᵖ) [有余极限 F]
  定义体: limit.isoLimitCone ⟨_, isLimitConeLeftOpOfCocone _ (colimit.isColimit _)⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isLimitConeLeftOpOfCocone, isoLimitCone, limit.isoLimitCone
-/
def limitLeftOpIsoUnopColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.leftOp ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeLeftOpOfCocone _ (colimit.isColimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitLeftOpIsoUnopColimit_inv_comp_π` / 引理 `limitLeftOpIsoUnopColimit_inv_comp_π`

English:
lemma limitLeftOpIsoUnopColimit_inv_comp_π
  given: (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ)
  proof: by
  simp [limitLeftOpIsoUnopColimit]

中文:
引理 limitLeftOpIsoUnopColimit_inv_comp_π
  条件: (F : J ⥤ Cᵒᵖ) [有余极限 F] (j : Jᵒᵖ)
  证明: by
  simp [limitLeftOpIsoUnopColimit]

Depends on / 依赖: limitLeftOpIsoUnopColimit
-/
lemma limitLeftOpIsoUnopColimit_inv_comp_π (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitLeftOpIsoUnopColimit F).inv ≫ limit.π F.leftOp j = (colimit.ι F j.unop).unop := by
  simp [limitLeftOpIsoUnopColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitLeftOpIsoUnopColimit_hom_comp_ι` / 引理 `limitLeftOpIsoUnopColimit_hom_comp_ι`

English:
lemma limitLeftOpIsoUnopColimit_hom_comp_ι
  given: (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : J)
  proof: by
  simp [← Iso.eq_inv_comp]

中文:
引理 limitLeftOpIsoUnopColimit_hom_comp_ι
  条件: (F : J ⥤ Cᵒᵖ) [有余极限 F] (j : J)
  证明: by
  simp [← Iso.eq_inv_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
lemma limitLeftOpIsoUnopColimit_hom_comp_ι (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitLeftOpIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.leftOp (op j) := by
  simp [← Iso.eq_inv_comp]

/--
Definition of `limitRightOpIsoOpColimit` / `limitRightOpIsoOpColimit` 的定义

English:
definition limitRightOpIsoOpColimit
  signature: (F : Jᵒᵖ ⥤ C) [HasColimit F]
  body: limit.isoLimitCone ⟨_, isLimitConeRightOpOfCocone _ (colimit.isColimit _)⟩

中文:
定义 limitRightOpIsoOpColimit
  签名: (F : Jᵒᵖ ⥤ C) [有余极限 F]
  定义体: limit.isoLimitCone ⟨_, isLimitConeRightOpOfCocone _ (colimit.isColimit _)⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isLimitConeRightOpOfCocone, isoLimitCone, limit.isoLimitCone
-/
def limitRightOpIsoOpColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] :
    limit F.rightOp ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeRightOpOfCocone _ (colimit.isColimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitRightOpIsoOpColimit_inv_comp_π` / 引理 `limitRightOpIsoOpColimit_inv_comp_π`

English:
lemma limitRightOpIsoOpColimit_inv_comp_π
  given: (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : J)
  proof: by
  simp [limitRightOpIsoOpColimit]

中文:
引理 limitRightOpIsoOpColimit_inv_comp_π
  条件: (F : Jᵒᵖ ⥤ C) [有余极限 F] (j : J)
  证明: by
  simp [limitRightOpIsoOpColimit]

Depends on / 依赖: limitRightOpIsoOpColimit
-/
lemma limitRightOpIsoOpColimit_inv_comp_π (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : J) :
    (limitRightOpIsoOpColimit F).inv ≫ limit.π F.rightOp j = (colimit.ι F (op j)).op := by
  simp [limitRightOpIsoOpColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitRightOpIsoOpColimit_hom_comp_ι` / 引理 `limitRightOpIsoOpColimit_hom_comp_ι`

English:
lemma limitRightOpIsoOpColimit_hom_comp_ι
  given: (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : Jᵒᵖ)
  proof: by
  simp [← Iso.eq_inv_comp]

中文:
引理 limitRightOpIsoOpColimit_hom_comp_ι
  条件: (F : Jᵒᵖ ⥤ C) [有余极限 F] (j : Jᵒᵖ)
  证明: by
  simp [← Iso.eq_inv_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
lemma limitRightOpIsoOpColimit_hom_comp_ι (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitRightOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.rightOp j.unop := by
  simp [← Iso.eq_inv_comp]

/--
Definition of `limitUnopIsoUnopColimit` / `limitUnopIsoUnopColimit` 的定义

English:
definition limitUnopIsoUnopColimit
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F]
  body: limit.isoLimitCone ⟨_, isLimitConeUnopOfCocone _ (colimit.isColimit _)⟩

中文:
定义 limitUnopIsoUnopColimit
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有余极限 F]
  定义体: limit.isoLimitCone ⟨_, isLimitConeUnopOfCocone _ (colimit.isColimit _)⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isLimitConeUnopOfCocone, isoLimitCone, limit.isoLimitCone
-/
def limitUnopIsoUnopColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.unop ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeUnopOfCocone _ (colimit.isColimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitUnopIsoUnopColimit_inv_comp_π` / 引理 `limitUnopIsoUnopColimit_inv_comp_π`

English:
lemma limitUnopIsoUnopColimit_inv_comp_π
  given: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : J)
  proof: by
  simp [limitUnopIsoUnopColimit]

中文:
引理 limitUnopIsoUnopColimit_inv_comp_π
  条件: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有余极限 F] (j : J)
  证明: by
  simp [limitUnopIsoUnopColimit]

Depends on / 依赖: limitUnopIsoUnopColimit
-/
lemma limitUnopIsoUnopColimit_inv_comp_π (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitUnopIsoUnopColimit F).inv ≫ limit.π F.unop j = (colimit.ι F (op j)).unop := by
  simp [limitUnopIsoUnopColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `limitUnopIsoUnopColimit_hom_comp_ι` / 引理 `limitUnopIsoUnopColimit_hom_comp_ι`

English:
lemma limitUnopIsoUnopColimit_hom_comp_ι
  given: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ)
  proof: by
  simp [← Iso.eq_inv_comp]

中文:
引理 limitUnopIsoUnopColimit_hom_comp_ι
  条件: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有余极限 F] (j : Jᵒᵖ)
  证明: by
  simp [← Iso.eq_inv_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
lemma limitUnopIsoUnopColimit_hom_comp_ι (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitUnopIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.unop j.unop := by
  simp [← Iso.eq_inv_comp]

/--
theorem `hasLimitsOfShape_op_of_hasColimitsOfShape` / 定理 `hasLimitsOfShape_op_of_hasColimitsOfShape`

English:
theorem hasLimitsOfShape_op_of_hasColimitsOfShape
  given: [HasColimitsOfShape Jᵒᵖ C]
  proof: { has_limit := fun F => hasLimit_of_hasColimit_leftOp F }

中文:
定理 hasLimitsOfShape_op_of_hasColimitsOfShape
  条件: [有形状余极限 Jᵒᵖ C]
  证明: { has_limit := fun F => hasLimit_of_hasColimit_leftOp F }

Depends on / 依赖: hasLimit_of_hasColimit_leftOp, has_limit
-/
theorem hasLimitsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] :
    HasLimitsOfShape J Cᵒᵖ :=
  { has_limit := fun F => hasLimit_of_hasColimit_leftOp F }

/--
theorem `hasLimitsOfShape_of_hasColimitsOfShape_op` / 定理 `hasLimitsOfShape_of_hasColimitsOfShape_op`

English:
theorem hasLimitsOfShape_of_hasColimitsOfShape_op
  given: [HasColimitsOfShape Jᵒᵖ Cᵒᵖ]
  proof: { has_limit := fun F => hasLimit_of_hasColimit_op F }

中文:
定理 hasLimitsOfShape_of_hasColimitsOfShape_op
  条件: [有形状余极限 Jᵒᵖ Cᵒᵖ]
  证明: { has_limit := fun F => hasLimit_of_hasColimit_op F }

Depends on / 依赖: hasLimit_of_hasColimit_op, has_limit
-/
theorem hasLimitsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasLimitsOfShape J C :=
  { has_limit := fun F => hasLimit_of_hasColimit_op F }

attribute [local instance] hasLimitsOfShape_op_of_hasColimitsOfShape

/--
Instance `hasLimits_op_of_hasColimits` / 实例 `hasLimits_op_of_hasColimits`

English:
instance hasLimits_op_of_hasColimits
  signature: [HasColimitsOfSize.{v₂, u₂} C]
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasLimits_op_of_hasColimits
  签名: [有余limitsOfSize.{v₂, u₂} C]
  定义体: ⟨fun _ => inferInstance⟩
-/
instance hasLimits_op_of_hasColimits [HasColimitsOfSize.{v₂, u₂} C] :
    HasLimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

/--
theorem `hasLimits_of_hasColimits_op` / 定理 `hasLimits_of_hasColimits_op`

English:
theorem hasLimits_of_hasColimits_op
  given: [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ]
  proof: { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

中文:
定理 hasLimits_of_hasColimits_op
  条件: [有余limitsOfSize.{v₂, u₂} Cᵒᵖ]
  证明: { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

Depends on / 依赖: hasLimitsOfShape_of_hasColimitsOfShape_op, has_limits_of_shape
-/
theorem hasLimits_of_hasColimits_op [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasLimitsOfSize.{v₂, u₂} C :=
  { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

/--
theorem `hasColimit_of_hasLimit_leftOp` / 定理 `hasColimit_of_hasLimit_leftOp`

English:
theorem hasColimit_of_hasLimit_leftOp
  given: (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp]
  statement: HasColimit F
  proof: HasColimit.mk
    { cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      isColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

中文:
定理 hasColimit_of_hasLimit_leftOp
  条件: (F : J ⥤ Cᵒᵖ) [有极限 F.leftOp]
  结论: 有余极限 F
  证明: HasColimit.mk
    { cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      isColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

Depends on / 依赖: F.leftOp, HasColimit, HasColimit.mk, cocone, coconeOfConeLeftOp, isColimit, isColimitCoconeOfConeLeftOp, isLimit, leftOp, limit.cone, limit.isLimit
-/
theorem hasColimit_of_hasLimit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      isColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

/--
theorem `hasColimit_of_hasLimit_op` / 定理 `hasColimit_of_hasLimit_op`

English:
theorem hasColimit_of_hasLimit_op
  given: (F : J ⥤ C) [HasLimit F.op]
  statement: HasColimit F
  proof: HasColimit.mk
    { cocone := (limit.cone F.op).unop
      isColimit := (limit.isLimit _).unop }

中文:
定理 hasColimit_of_hasLimit_op
  条件: (F : J ⥤ C) [有极限 F.op]
  结论: 有余极限 F
  证明: HasColimit.mk
    { cocone := (limit.cone F.op).unop
      isColimit := (limit.isLimit _).unop }

Depends on / 依赖: F.op, HasColimit, HasColimit.mk, cocone, isColimit, isLimit, limit.cone, limit.isLimit
-/
theorem hasColimit_of_hasLimit_op (F : J ⥤ C) [HasLimit F.op] : HasColimit F :=
  HasColimit.mk
    { cocone := (limit.cone F.op).unop
      isColimit := (limit.isLimit _).unop }

/--
theorem `hasColimit_of_hasLimit_rightOp` / 定理 `hasColimit_of_hasLimit_rightOp`

English:
theorem hasColimit_of_hasLimit_rightOp
  given: (F : Jᵒᵖ ⥤ C) [HasLimit F.rightOp]
  statement: HasColimit F
  proof: HasColimit.mk
    { cocone := coconeOfConeRightOp (limit.cone F.rightOp)
      isColimit := isColimitCoconeOfConeRightOp _ (limit.isLimit _) }

中文:
定理 hasColimit_of_hasLimit_rightOp
  条件: (F : Jᵒᵖ ⥤ C) [有极限 F.rightOp]
  结论: 有余极限 F
  证明: HasColimit.mk
    { cocone := coconeOfConeRightOp (limit.cone F.rightOp)
      isColimit := isColimitCoconeOfConeRightOp _ (limit.isLimit _) }

Depends on / 依赖: F.rightOp, HasColimit, HasColimit.mk, cocone, coconeOfConeRightOp, isColimit, isColimitCoconeOfConeRightOp, isLimit, limit.cone, limit.isLimit, rightOp
-/
theorem hasColimit_of_hasLimit_rightOp (F : Jᵒᵖ ⥤ C) [HasLimit F.rightOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeRightOp (limit.cone F.rightOp)
      isColimit := isColimitCoconeOfConeRightOp _ (limit.isLimit _) }

/--
theorem `hasColimit_of_hasLimit_unop` / 定理 `hasColimit_of_hasLimit_unop`

English:
theorem hasColimit_of_hasLimit_unop
  given: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F.unop]
  statement: HasColimit F
  proof: HasColimit.mk
    { cocone := coconeOfConeUnop (limit.cone F.unop)
      isColimit := isColimitCoconeOfConeUnop _ (limit.isLimit _) }

中文:
定理 hasColimit_of_hasLimit_unop
  条件: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有极限 F.unop]
  结论: 有余极限 F
  证明: HasColimit.mk
    { cocone := coconeOfConeUnop (limit.cone F.unop)
      isColimit := isColimitCoconeOfConeUnop _ (limit.isLimit _) }

Depends on / 依赖: F.unop, HasColimit, HasColimit.mk, cocone, coconeOfConeUnop, isColimit, isColimitCoconeOfConeUnop, isLimit, limit.cone, limit.isLimit
-/
theorem hasColimit_of_hasLimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F.unop] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeUnop (limit.cone F.unop)
      isColimit := isColimitCoconeOfConeUnop _ (limit.isLimit _) }

/--
Instance `hasColimit_op_of_hasLimit` / 实例 `hasColimit_op_of_hasLimit`

English:
instance hasColimit_op_of_hasLimit
  signature: (F : J ⥤ C) [HasLimit F]
  body: HasColimit.mk
    { cocone := (limit.cone F).op
      isColimit := (limit.isLimit _).op }

中文:
实例 hasColimit_op_of_hasLimit
  签名: (F : J ⥤ C) [有极限 F]
  定义体: HasColimit.mk
    { cocone := (limit.cone F).op
      isColimit := (limit.isLimit _).op }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, isColimit, isLimit, limit.cone, limit.isLimit
-/
instance hasColimit_op_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasColimit F.op :=
  HasColimit.mk
    { cocone := (limit.cone F).op
      isColimit := (limit.isLimit _).op }

/--
Instance `hasColimit_leftOp_of_hasLimit` / 实例 `hasColimit_leftOp_of_hasLimit`

English:
instance hasColimit_leftOp_of_hasLimit
  signature: (F : J ⥤ Cᵒᵖ) [HasLimit F]
  body: HasColimit.mk
    { cocone := coconeLeftOpOfCone (limit.cone F)
      isColimit := isColimitCoconeLeftOpOfCone _ (limit.isLimit _) }

中文:
实例 hasColimit_leftOp_of_hasLimit
  签名: (F : J ⥤ Cᵒᵖ) [有极限 F]
  定义体: HasColimit.mk
    { cocone := coconeLeftOpOfCone (limit.cone F)
      isColimit := isColimitCoconeLeftOpOfCone _ (limit.isLimit _) }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coconeLeftOpOfCone, isColimit, isColimitCoconeLeftOpOfCone, isLimit, limit.cone, limit.isLimit
-/
instance hasColimit_leftOp_of_hasLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.leftOp :=
  HasColimit.mk
    { cocone := coconeLeftOpOfCone (limit.cone F)
      isColimit := isColimitCoconeLeftOpOfCone _ (limit.isLimit _) }

/--
Instance `hasColimit_rightOp_of_hasLimit` / 实例 `hasColimit_rightOp_of_hasLimit`

English:
instance hasColimit_rightOp_of_hasLimit
  signature: (F : Jᵒᵖ ⥤ C) [HasLimit F]
  body: HasColimit.mk
    { cocone := coconeRightOpOfCone (limit.cone F)
      isColimit := isColimitCoconeRightOpOfCone _ (limit.isLimit _) }

中文:
实例 hasColimit_rightOp_of_hasLimit
  签名: (F : Jᵒᵖ ⥤ C) [有极限 F]
  定义体: HasColimit.mk
    { cocone := coconeRightOpOfCone (limit.cone F)
      isColimit := isColimitCoconeRightOpOfCone _ (limit.isLimit _) }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coconeRightOpOfCone, isColimit, isColimitCoconeRightOpOfCone, isLimit, limit.cone, limit.isLimit
-/
instance hasColimit_rightOp_of_hasLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] : HasColimit F.rightOp :=
  HasColimit.mk
    { cocone := coconeRightOpOfCone (limit.cone F)
      isColimit := isColimitCoconeRightOpOfCone _ (limit.isLimit _) }

/--
Instance `hasColimit_unop_of_hasLimit` / 实例 `hasColimit_unop_of_hasLimit`

English:
instance hasColimit_unop_of_hasLimit
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F]
  body: HasColimit.mk
    { cocone := coconeUnopOfCone (limit.cone F)
      isColimit := isColimitCoconeUnopOfCone _ (limit.isLimit _) }

中文:
实例 hasColimit_unop_of_hasLimit
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有极限 F]
  定义体: HasColimit.mk
    { cocone := coconeUnopOfCone (limit.cone F)
      isColimit := isColimitCoconeUnopOfCone _ (limit.isLimit _) }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coconeUnopOfCone, isColimit, isColimitCoconeUnopOfCone, isLimit, limit.cone, limit.isLimit
-/
instance hasColimit_unop_of_hasLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.unop :=
  HasColimit.mk
    { cocone := coconeUnopOfCone (limit.cone F)
      isColimit := isColimitCoconeUnopOfCone _ (limit.isLimit _) }

/--
Definition of `colimitOpIsoOpLimit` / `colimitOpIsoOpLimit` 的定义

English:
definition colimitOpIsoOpLimit
  signature: (F : J ⥤ C) [HasLimit F]
  body: colimit.isoColimitCocone ⟨_, (limit.isLimit _).op⟩

中文:
定义 colimitOpIsoOpLimit
  签名: (F : J ⥤ C) [有极限 F]
  定义体: colimit.isoColimitCocone ⟨_, (limit.isLimit _).op⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isLimit, isoColimitCocone, limit.isLimit
-/
def colimitOpIsoOpLimit (F : J ⥤ C) [HasLimit F] :
    colimit F.op ≅ op (limit F) :=
  colimit.isoColimitCocone ⟨_, (limit.isLimit _).op⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_comp_colimitOpIsoOpLimit_hom` / 引理 `ι_comp_colimitOpIsoOpLimit_hom`

English:
lemma ι_comp_colimitOpIsoOpLimit_hom
  given: (F : J ⥤ C) [HasLimit F] (j : Jᵒᵖ)
  proof: by
  simp [colimitOpIsoOpLimit]

中文:
引理 ι_comp_colimitOpIsoOpLimit_hom
  条件: (F : J ⥤ C) [有极限 F] (j : Jᵒᵖ)
  证明: by
  simp [colimitOpIsoOpLimit]

Depends on / 依赖: colimitOpIsoOpLimit
-/
lemma ι_comp_colimitOpIsoOpLimit_hom (F : J ⥤ C) [HasLimit F] (j : Jᵒᵖ) :
    colimit.ι F.op j ≫ (colimitOpIsoOpLimit F).hom = (limit.π F j.unop).op := by
  simp [colimitOpIsoOpLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π_comp_colimitOpIsoOpLimit_inv` / 引理 `π_comp_colimitOpIsoOpLimit_inv`

English:
lemma π_comp_colimitOpIsoOpLimit_inv
  given: (F : J ⥤ C) [HasLimit F] (j : J)
  proof: by
  simp [Iso.comp_inv_eq]

中文:
引理 π_comp_colimitOpIsoOpLimit_inv
  条件: (F : J ⥤ C) [有极限 F] (j : J)
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
lemma π_comp_colimitOpIsoOpLimit_inv (F : J ⥤ C) [HasLimit F] (j : J) :
    (limit.π F j).op ≫ (colimitOpIsoOpLimit F).inv = colimit.ι F.op (op j) := by
  simp [Iso.comp_inv_eq]

/--
Definition of `colimitLeftOpIsoUnopLimit` / `colimitLeftOpIsoUnopLimit` 的定义

English:
definition colimitLeftOpIsoUnopLimit
  signature: (F : J ⥤ Cᵒᵖ) [HasLimit F]
  body: colimit.isoColimitCocone ⟨_, isColimitCoconeLeftOpOfCone _ (limit.isLimit _)⟩

中文:
定义 colimitLeftOpIsoUnopLimit
  签名: (F : J ⥤ Cᵒᵖ) [有极限 F]
  定义体: colimit.isoColimitCocone ⟨_, isColimitCoconeLeftOpOfCone _ (limit.isLimit _)⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isColimitCoconeLeftOpOfCone, isLimit, isoColimitCocone, limit.isLimit
-/
def colimitLeftOpIsoUnopLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.leftOp ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeLeftOpOfCone _ (limit.isLimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_comp_colimitLeftOpIsoUnopLimit_hom` / 引理 `ι_comp_colimitLeftOpIsoUnopLimit_hom`

English:
lemma ι_comp_colimitLeftOpIsoUnopLimit_hom
  given: (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ)
  proof: by
  simp [colimitLeftOpIsoUnopLimit]

中文:
引理 ι_comp_colimitLeftOpIsoUnopLimit_hom
  条件: (F : J ⥤ Cᵒᵖ) [有极限 F] (j : Jᵒᵖ)
  证明: by
  simp [colimitLeftOpIsoUnopLimit]

Depends on / 依赖: colimitLeftOpIsoUnopLimit
-/
lemma ι_comp_colimitLeftOpIsoUnopLimit_hom (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ) :
    colimit.ι F.leftOp j ≫ (colimitLeftOpIsoUnopLimit F).hom = (limit.π F j.unop).unop := by
  simp [colimitLeftOpIsoUnopLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π_comp_colimitLeftOpIsoUnopLimit_inv` / 引理 `π_comp_colimitLeftOpIsoUnopLimit_inv`

English:
lemma π_comp_colimitLeftOpIsoUnopLimit_inv
  given: (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : J)
  proof: by
  simp [Iso.comp_inv_eq]

中文:
引理 π_comp_colimitLeftOpIsoUnopLimit_inv
  条件: (F : J ⥤ Cᵒᵖ) [有极限 F] (j : J)
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
lemma π_comp_colimitLeftOpIsoUnopLimit_inv (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : J) :
    (limit.π F j).unop ≫ (colimitLeftOpIsoUnopLimit F).inv = colimit.ι F.leftOp (op j) := by
  simp [Iso.comp_inv_eq]

/--
Definition of `colimitRightOpIsoUnopLimit` / `colimitRightOpIsoUnopLimit` 的定义

English:
definition colimitRightOpIsoUnopLimit
  signature: (F : Jᵒᵖ ⥤ C) [HasLimit F]
  body: colimit.isoColimitCocone ⟨_, isColimitCoconeRightOpOfCone _ (limit.isLimit _)⟩

中文:
定义 colimitRightOpIsoUnopLimit
  签名: (F : Jᵒᵖ ⥤ C) [有极限 F]
  定义体: colimit.isoColimitCocone ⟨_, isColimitCoconeRightOpOfCone _ (limit.isLimit _)⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isColimitCoconeRightOpOfCone, isLimit, isoColimitCocone, limit.isLimit
-/
def colimitRightOpIsoUnopLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] :
    colimit F.rightOp ≅ op (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeRightOpOfCone _ (limit.isLimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_comp_colimitRightOpIsoUnopLimit_hom` / 引理 `ι_comp_colimitRightOpIsoUnopLimit_hom`

English:
lemma ι_comp_colimitRightOpIsoUnopLimit_hom
  given: (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : J)
  proof: by
  simp [colimitRightOpIsoUnopLimit]

中文:
引理 ι_comp_colimitRightOpIsoUnopLimit_hom
  条件: (F : Jᵒᵖ ⥤ C) [有极限 F] (j : J)
  证明: by
  simp [colimitRightOpIsoUnopLimit]

Depends on / 依赖: colimitRightOpIsoUnopLimit
-/
lemma ι_comp_colimitRightOpIsoUnopLimit_hom (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : J) :
    colimit.ι F.rightOp j ≫ (colimitRightOpIsoUnopLimit F).hom = (limit.π F (op j)).op := by
  simp [colimitRightOpIsoUnopLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π_comp_colimitRightOpIsoUnopLimit_inv` / 引理 `π_comp_colimitRightOpIsoUnopLimit_inv`

English:
lemma π_comp_colimitRightOpIsoUnopLimit_inv
  given: (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : Jᵒᵖ)
  proof: by
  simp [Iso.comp_inv_eq]

中文:
引理 π_comp_colimitRightOpIsoUnopLimit_inv
  条件: (F : Jᵒᵖ ⥤ C) [有极限 F] (j : Jᵒᵖ)
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
lemma π_comp_colimitRightOpIsoUnopLimit_inv (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : Jᵒᵖ) :
    (limit.π F j).op ≫ (colimitRightOpIsoUnopLimit F).inv = colimit.ι F.rightOp j.unop := by
  simp [Iso.comp_inv_eq]

/--
Definition of `colimitUnopIsoOpLimit` / `colimitUnopIsoOpLimit` 的定义

English:
definition colimitUnopIsoOpLimit
  signature: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F]
  body: colimit.isoColimitCocone ⟨_, isColimitCoconeUnopOfCone _ (limit.isLimit _)⟩

中文:
定义 colimitUnopIsoOpLimit
  签名: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有极限 F]
  定义体: colimit.isoColimitCocone ⟨_, isColimitCoconeUnopOfCone _ (limit.isLimit _)⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isColimitCoconeUnopOfCone, isLimit, isoColimitCocone, limit.isLimit
-/
def colimitUnopIsoOpLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.unop ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeUnopOfCone _ (limit.isLimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_comp_colimitUnopIsoOpLimit_hom` / 引理 `ι_comp_colimitUnopIsoOpLimit_hom`

English:
lemma ι_comp_colimitUnopIsoOpLimit_hom
  given: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : J)
  proof: by
  simp [colimitUnopIsoOpLimit]

中文:
引理 ι_comp_colimitUnopIsoOpLimit_hom
  条件: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有极限 F] (j : J)
  证明: by
  simp [colimitUnopIsoOpLimit]

Depends on / 依赖: colimitUnopIsoOpLimit
-/
lemma ι_comp_colimitUnopIsoOpLimit_hom (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : J) :
    colimit.ι F.unop j ≫ (colimitUnopIsoOpLimit F).hom = (limit.π F (op j)).unop := by
  simp [colimitUnopIsoOpLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π_comp_colimitUnopIsoOpLimit_inv` / 引理 `π_comp_colimitUnopIsoOpLimit_inv`

English:
lemma π_comp_colimitUnopIsoOpLimit_inv
  given: (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ)
  proof: by
  simp [Iso.comp_inv_eq]

中文:
引理 π_comp_colimitUnopIsoOpLimit_inv
  条件: (F : Jᵒᵖ ⥤ Cᵒᵖ) [有极限 F] (j : Jᵒᵖ)
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
lemma π_comp_colimitUnopIsoOpLimit_inv (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ) :
    (limit.π F j).unop ≫ (colimitUnopIsoOpLimit F).inv = colimit.ι F.unop j.unop := by
  simp [Iso.comp_inv_eq]

/--
Instance `hasColimitsOfShape_op_of_hasLimitsOfShape` / 实例 `hasColimitsOfShape_op_of_hasLimitsOfShape`

English:
instance hasColimitsOfShape_op_of_hasLimitsOfShape
  signature: [HasLimitsOfShape Jᵒᵖ C]
  body: hasColimit_of_hasLimit_leftOp F

中文:
实例 hasColimitsOfShape_op_of_hasLimitsOfShape
  签名: [有形状极限 Jᵒᵖ C]
  定义体: hasColimit_of_hasLimit_leftOp F

Depends on / 依赖: hasColimit_of_hasLimit_leftOp
-/
instance hasColimitsOfShape_op_of_hasLimitsOfShape [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J Cᵒᵖ where has_colimit F := hasColimit_of_hasLimit_leftOp F

/--
theorem `hasColimitsOfShape_of_hasLimitsOfShape_op` / 定理 `hasColimitsOfShape_of_hasLimitsOfShape_op`

English:
theorem hasColimitsOfShape_of_hasLimitsOfShape_op
  given: [HasLimitsOfShape Jᵒᵖ Cᵒᵖ]
  proof: { has_colimit := fun F => hasColimit_of_hasLimit_op F }

中文:
定理 hasColimitsOfShape_of_hasLimitsOfShape_op
  条件: [有形状极限 Jᵒᵖ Cᵒᵖ]
  证明: { has_colimit := fun F => hasColimit_of_hasLimit_op F }

Depends on / 依赖: hasColimit_of_hasLimit_op, has_colimit
-/
theorem hasColimitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasColimitsOfShape J C :=
  { has_colimit := fun F => hasColimit_of_hasLimit_op F }

/--
Instance `hasColimits_op_of_hasLimits` / 实例 `hasColimits_op_of_hasLimits`

English:
instance hasColimits_op_of_hasLimits
  signature: [HasLimitsOfSize.{v₂, u₂} C]
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasColimits_op_of_hasLimits
  签名: [有LimitsOfSize.{v₂, u₂} C]
  定义体: ⟨fun _ => inferInstance⟩
-/
instance hasColimits_op_of_hasLimits [HasLimitsOfSize.{v₂, u₂} C] :
    HasColimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩

/--
theorem `hasColimits_of_hasLimits_op` / 定理 `hasColimits_of_hasLimits_op`

English:
theorem hasColimits_of_hasLimits_op
  given: [HasLimitsOfSize.{v₂, u₂} Cᵒᵖ]
  proof: { has_colimits_of_shape := fun _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

中文:
定理 hasColimits_of_hasLimits_op
  条件: [有LimitsOfSize.{v₂, u₂} Cᵒᵖ]
  证明: { has_colimits_of_shape := fun _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

Depends on / 依赖: hasColimitsOfShape_of_hasLimitsOfShape_op, has_colimits_of_shape
-/
theorem hasColimits_of_hasLimits_op [HasLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasColimitsOfSize.{v₂, u₂} C :=
  { has_colimits_of_shape := fun _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

/--
lemma `hasColimitsOfSize_opposite_iff` / 引理 `hasColimitsOfSize_opposite_iff`

English:
lemma hasColimitsOfSize_opposite_iff
  proof: ⟨fun _ => hasLimits_of_hasColimits_op, fun _ => inferInstance⟩

中文:
引理 hasColimitsOfSize_opposite_iff
  证明: ⟨fun _ => hasLimits_of_hasColimits_op, fun _ => inferInstance⟩

Depends on / 依赖: hasLimits_of_hasColimits_op
-/
lemma hasColimitsOfSize_opposite_iff :
    HasColimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasLimitsOfSize.{v₂, u₂} C :=
  ⟨fun _ => hasLimits_of_hasColimits_op, fun _ => inferInstance⟩

/--
lemma `hasLimitsOfSize_opposite_iff` / 引理 `hasLimitsOfSize_opposite_iff`

English:
lemma hasLimitsOfSize_opposite_iff
  proof: ⟨fun _ => hasColimits_of_hasLimits_op, fun _ => inferInstance⟩

中文:
引理 hasLimitsOfSize_opposite_iff
  证明: ⟨fun _ => hasColimits_of_hasLimits_op, fun _ => inferInstance⟩

Depends on / 依赖: hasColimits_of_hasLimits_op
-/
lemma hasLimitsOfSize_opposite_iff :
    HasLimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasColimitsOfSize.{v₂, u₂} C :=
  ⟨fun _ => hasColimits_of_hasLimits_op, fun _ => inferInstance⟩

/--
Instance `hasFiniteColimits_opposite` / 实例 `hasFiniteColimits_opposite`

English:
instance hasFiniteColimits_opposite
  signature: [HasFiniteLimits C]
  body: ⟨fun _ _ _ => hasColimitsOfShape_op_of_hasLimitsOfShape⟩

中文:
实例 hasFiniteColimits_opposite
  签名: [有有限极限 C]
  定义体: ⟨fun _ _ _ => hasColimitsOfShape_op_of_hasLimitsOfShape⟩

Depends on / 依赖: hasColimitsOfShape_op_of_hasLimitsOfShape
-/
instance hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasColimitsOfShape_op_of_hasLimitsOfShape⟩

/--
Instance `hasFiniteLimits_opposite` / 实例 `hasFiniteLimits_opposite`

English:
instance hasFiniteLimits_opposite
  signature: [HasFiniteColimits C]
  body: ⟨fun _ _ _ => hasLimitsOfShape_op_of_hasColimitsOfShape⟩

中文:
实例 hasFiniteLimits_opposite
  签名: [有有限余极限 C]
  定义体: ⟨fun _ _ _ => hasLimitsOfShape_op_of_hasColimitsOfShape⟩

Depends on / 依赖: hasLimitsOfShape_op_of_hasColimitsOfShape
-/
instance hasFiniteLimits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasLimitsOfShape_op_of_hasColimitsOfShape⟩

/--
lemma `hasFiniteLimits_opposite_iff` / 引理 `hasFiniteLimits_opposite_iff`

English:
lemma hasFiniteLimits_opposite_iff
  statement: HasFiniteLimits Cᵒᵖ ↔ HasFiniteColimits C
  proof: ⟨fun _ => ⟨fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op⟩, fun _ => inferInstance⟩

中文:
引理 hasFiniteLimits_opposite_iff
  结论: 有有限极限 Cᵒᵖ ↔ 有有限余极限 C
  证明: ⟨fun _ => ⟨fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op⟩, fun _ => inferInstance⟩

Depends on / 依赖: hasColimitsOfShape_of_hasLimitsOfShape_op
-/
lemma hasFiniteLimits_opposite_iff : HasFiniteLimits Cᵒᵖ ↔ HasFiniteColimits C :=
  ⟨fun _ => ⟨fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op⟩, fun _ => inferInstance⟩

/--
lemma `hasFiniteColimits_opposite_iff` / 引理 `hasFiniteColimits_opposite_iff`

English:
lemma hasFiniteColimits_opposite_iff
  statement: HasFiniteColimits Cᵒᵖ ↔ HasFiniteLimits C
  proof: ⟨fun _ => ⟨fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op⟩, fun _ => inferInstance⟩

中文:
引理 hasFiniteColimits_opposite_iff
  结论: 有有限余极限 Cᵒᵖ ↔ 有有限极限 C
  证明: ⟨fun _ => ⟨fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op⟩, fun _ => inferInstance⟩

Depends on / 依赖: hasLimitsOfShape_of_hasColimitsOfShape_op
-/
lemma hasFiniteColimits_opposite_iff : HasFiniteColimits Cᵒᵖ ↔ HasFiniteLimits C :=
  ⟨fun _ => ⟨fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op⟩, fun _ => inferInstance⟩

/--
lemma `hasColimit_op_iff_hasLimit` / 引理 `hasColimit_op_iff_hasLimit`

English:
lemma hasColimit_op_iff_hasLimit
  given: {F : J ⥤ C}
  statement: HasColimit F.op ↔ HasLimit F
  proof: ⟨fun _ => hasLimit_of_hasColimit_op F, fun _ => inferInstance⟩

中文:
引理 hasColimit_op_iff_hasLimit
  条件: {F : J ⥤ C}
  结论: 有余极限 F.op ↔ 有极限 F
  证明: ⟨fun _ => hasLimit_of_hasColimit_op F, fun _ => inferInstance⟩

Depends on / 依赖: hasLimit_of_hasColimit_op
-/
lemma hasColimit_op_iff_hasLimit {F : J ⥤ C} : HasColimit F.op ↔ HasLimit F :=
  ⟨fun _ => hasLimit_of_hasColimit_op F, fun _ => inferInstance⟩

/--
lemma `hasColimit_leftOp_iff_hasLimit` / 引理 `hasColimit_leftOp_iff_hasLimit`

English:
lemma hasColimit_leftOp_iff_hasLimit
  given: {F : J ⥤ Cᵒᵖ}
  statement: HasColimit F.leftOp ↔ HasLimit F
  proof: ⟨fun _ => hasLimit_of_hasColimit_leftOp F, fun _ => inferInstance⟩

中文:
引理 hasColimit_leftOp_iff_hasLimit
  条件: {F : J ⥤ Cᵒᵖ}
  结论: 有余极限 F.leftOp ↔ 有极限 F
  证明: ⟨fun _ => hasLimit_of_hasColimit_leftOp F, fun _ => inferInstance⟩

Depends on / 依赖: hasLimit_of_hasColimit_leftOp
-/
lemma hasColimit_leftOp_iff_hasLimit {F : J ⥤ Cᵒᵖ} : HasColimit F.leftOp ↔ HasLimit F :=
  ⟨fun _ => hasLimit_of_hasColimit_leftOp F, fun _ => inferInstance⟩

/--
lemma `hasColimit_rightOp_iff_hasLimit` / 引理 `hasColimit_rightOp_iff_hasLimit`

English:
lemma hasColimit_rightOp_iff_hasLimit
  given: {F : Jᵒᵖ ⥤ C}
  statement: HasColimit F.rightOp ↔ HasLimit F
  proof: ⟨fun _ => hasLimit_of_hasColimit_rightOp F, fun _ => inferInstance⟩

中文:
引理 hasColimit_rightOp_iff_hasLimit
  条件: {F : Jᵒᵖ ⥤ C}
  结论: 有余极限 F.rightOp ↔ 有极限 F
  证明: ⟨fun _ => hasLimit_of_hasColimit_rightOp F, fun _ => inferInstance⟩

Depends on / 依赖: hasLimit_of_hasColimit_rightOp
-/
lemma hasColimit_rightOp_iff_hasLimit {F : Jᵒᵖ ⥤ C} : HasColimit F.rightOp ↔ HasLimit F :=
  ⟨fun _ => hasLimit_of_hasColimit_rightOp F, fun _ => inferInstance⟩

/--
lemma `hasLimit_op_iff_hasColimit` / 引理 `hasLimit_op_iff_hasColimit`

English:
lemma hasLimit_op_iff_hasColimit
  given: {F : J ⥤ C}
  statement: HasLimit F.op ↔ HasColimit F
  proof: ⟨fun _ => hasColimit_of_hasLimit_op F, fun _ => inferInstance⟩

中文:
引理 hasLimit_op_iff_hasColimit
  条件: {F : J ⥤ C}
  结论: 有极限 F.op ↔ 有余极限 F
  证明: ⟨fun _ => hasColimit_of_hasLimit_op F, fun _ => inferInstance⟩

Depends on / 依赖: hasColimit_of_hasLimit_op
-/
lemma hasLimit_op_iff_hasColimit {F : J ⥤ C} : HasLimit F.op ↔ HasColimit F :=
  ⟨fun _ => hasColimit_of_hasLimit_op F, fun _ => inferInstance⟩

/--
lemma `hasLimit_leftOp_iff_hasColimit` / 引理 `hasLimit_leftOp_iff_hasColimit`

English:
lemma hasLimit_leftOp_iff_hasColimit
  given: {F : J ⥤ Cᵒᵖ}
  statement: HasLimit F.leftOp ↔ HasColimit F
  proof: ⟨fun _ => hasColimit_of_hasLimit_leftOp F, fun _ => inferInstance⟩

中文:
引理 hasLimit_leftOp_iff_hasColimit
  条件: {F : J ⥤ Cᵒᵖ}
  结论: 有极限 F.leftOp ↔ 有余极限 F
  证明: ⟨fun _ => hasColimit_of_hasLimit_leftOp F, fun _ => inferInstance⟩

Depends on / 依赖: hasColimit_of_hasLimit_leftOp
-/
lemma hasLimit_leftOp_iff_hasColimit {F : J ⥤ Cᵒᵖ} : HasLimit F.leftOp ↔ HasColimit F :=
  ⟨fun _ => hasColimit_of_hasLimit_leftOp F, fun _ => inferInstance⟩

/--
lemma `hasLimit_rightOp_iff_hasColimit` / 引理 `hasLimit_rightOp_iff_hasColimit`

English:
lemma hasLimit_rightOp_iff_hasColimit
  given: {F : Jᵒᵖ ⥤ C}
  statement: HasLimit F.rightOp ↔ HasColimit F
  proof: ⟨fun _ => hasColimit_of_hasLimit_rightOp F, fun _ => inferInstance⟩

中文:
引理 hasLimit_rightOp_iff_hasColimit
  条件: {F : Jᵒᵖ ⥤ C}
  结论: 有极限 F.rightOp ↔ 有余极限 F
  证明: ⟨fun _ => hasColimit_of_hasLimit_rightOp F, fun _ => inferInstance⟩

Depends on / 依赖: hasColimit_of_hasLimit_rightOp
-/
lemma hasLimit_rightOp_iff_hasColimit {F : Jᵒᵖ ⥤ C} : HasLimit F.rightOp ↔ HasColimit F :=
  ⟨fun _ => hasColimit_of_hasLimit_rightOp F, fun _ => inferInstance⟩

/--
lemma `hasLimitsOfShape_opposite_iff` / 引理 `hasLimitsOfShape_opposite_iff`

English:
lemma hasLimitsOfShape_opposite_iff
  statement: HasLimitsOfShape J Cᵒᵖ ↔ HasColimitsOfShape Jᵒᵖ C
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

中文:
引理 hasLimitsOfShape_opposite_iff
  结论: 有形状极限 J Cᵒᵖ ↔ 有形状余极限 Jᵒᵖ C
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

Depends on / 依赖: HasLimitsOfShape, hasColimitsOfShape_of_hasLimitsOfShape_op, hasLimitsOfShape_of_equivalence, opOpEquivalence
-/
lemma hasLimitsOfShape_opposite_iff : HasLimitsOfShape J Cᵒᵖ ↔ HasColimitsOfShape Jᵒᵖ C := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

/--
lemma `hasColimitsOfShape_opposite_iff` / 引理 `hasColimitsOfShape_opposite_iff`

English:
lemma hasColimitsOfShape_opposite_iff
  statement: HasColimitsOfShape J Cᵒᵖ ↔ HasLimitsOfShape Jᵒᵖ C
  proof: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_of_hasColimitsOfShape_op

中文:
引理 hasColimitsOfShape_opposite_iff
  结论: 有形状余极限 J Cᵒᵖ ↔ 有形状极限 Jᵒᵖ C
  证明: by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_of_hasColimitsOfShape_op

Depends on / 依赖: HasColimitsOfShape, hasColimitsOfShape_of_equivalence, hasLimitsOfShape_of_hasColimitsOfShape_op, opOpEquivalence
-/
lemma hasColimitsOfShape_opposite_iff : HasColimitsOfShape J Cᵒᵖ ↔ HasLimitsOfShape Jᵒᵖ C := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_of_hasColimitsOfShape_op

/--
lemma `hasLimitsOfShape_opposite_opposite_iff` / 引理 `hasLimitsOfShape_opposite_opposite_iff`

English:
lemma hasLimitsOfShape_opposite_opposite_iff
  proof: by
  refine ⟨fun _ => hasColimitsOfShape_of_hasLimitsOfShape_op, fun _ => ?_⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ C := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape

中文:
引理 hasLimitsOfShape_opposite_opposite_iff
  证明: by
  refine ⟨fun _ => hasColimitsOfShape_of_hasLimitsOfShape_op, fun _ => ?_⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ C := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape

Depends on / 依赖: HasColimitsOfShape, hasColimitsOfShape_of_equivalence, hasColimitsOfShape_of_hasLimitsOfShape_op, hasLimitsOfShape_op_of_hasColimitsOfShape, opOpEquivalence
-/
lemma hasLimitsOfShape_opposite_opposite_iff :
    HasLimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasColimitsOfShape J C := by
  refine ⟨fun _ => hasColimitsOfShape_of_hasLimitsOfShape_op, fun _ => ?_⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ C := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape

/--
lemma `hasColimitsOfShape_opposite_opposite_iff` / 引理 `hasColimitsOfShape_opposite_opposite_iff`

English:
lemma hasColimitsOfShape_opposite_opposite_iff
  proof: by
  refine ⟨fun _ => hasLimitsOfShape_of_hasColimitsOfShape_op, fun _ => ?_⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ C := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_op_of_hasLimitsOfShape

中文:
引理 hasColimitsOfShape_opposite_opposite_iff
  证明: by
  refine ⟨fun _ => hasLimitsOfShape_of_hasColimitsOfShape_op, fun _ => ?_⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ C := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_op_of_hasLimitsOfShape

Depends on / 依赖: HasLimitsOfShape, hasColimitsOfShape_op_of_hasLimitsOfShape, hasLimitsOfShape_of_equivalence, hasLimitsOfShape_of_hasColimitsOfShape_op, opOpEquivalence
-/
lemma hasColimitsOfShape_opposite_opposite_iff :
    HasColimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasLimitsOfShape J C := by
  refine ⟨fun _ => hasLimitsOfShape_of_hasColimitsOfShape_op, fun _ => ?_⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ C := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_op_of_hasLimitsOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWidePullbacks.{w}
  signature: C] : HasWidePushouts.{w} Cᵒᵖ
  body: by
  intro ι
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

中文:
实例 [HasWidePullbacks.{w}
  签名: C] : HasWidePushouts.{w} Cᵒᵖ
  定义体: by
  intro ι
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

Depends on / 依赖: hasColimitsOfShape_opposite_iff, hasLimitsOfShape_of_equivalence, widePushoutShapeOpEquiv
-/
instance [HasWidePullbacks.{w} C] : HasWidePushouts.{w} Cᵒᵖ := by
  intro ι
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWidePushouts.{w}
  signature: C] : HasWidePullbacks.{w} Cᵒᵖ
  body: by
  intro ι
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

中文:
实例 [HasWidePushouts.{w}
  签名: C] : HasWidePullbacks.{w} Cᵒᵖ
  定义体: by
  intro ι
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

Depends on / 依赖: hasColimitsOfShape_of_equivalence, hasLimitsOfShape_opposite_iff, widePullbackShapeOpEquiv
-/
instance [HasWidePushouts.{w} C] : HasWidePullbacks.{w} Cᵒᵖ := by
  intro ι
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

/--
lemma `hasWidePullbacks_opposite_iff` / 引理 `hasWidePullbacks_opposite_iff`

English:
lemma hasWidePullbacks_opposite_iff
  proof: by
  refine ⟨fun h ι => ?_, fun _ => inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

中文:
引理 hasWidePullbacks_opposite_iff
  证明: by
  refine ⟨fun h ι => ?_, fun _ => inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

Depends on / 依赖: hasLimitsOfShape_of_equivalence, hasLimitsOfShape_opposite_opposite_iff, widePushoutShapeOpEquiv
-/
lemma hasWidePullbacks_opposite_iff :
    HasWidePullbacks.{w} Cᵒᵖ ↔ HasWidePushouts.{w} C := by
  refine ⟨fun h ι => ?_, fun _ => inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

/--
lemma `hasWidePushouts_opposite_iff` / 引理 `hasWidePushouts_opposite_iff`

English:
lemma hasWidePushouts_opposite_iff
  proof: by
  refine ⟨fun h ι => ?_, fun _ => inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

中文:
引理 hasWidePushouts_opposite_iff
  证明: by
  refine ⟨fun h ι => ?_, fun _ => inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

Depends on / 依赖: hasColimitsOfShape_of_equivalence, hasColimitsOfShape_opposite_opposite_iff, widePullbackShapeOpEquiv
-/
lemma hasWidePushouts_opposite_iff :
    HasWidePushouts.{w} Cᵒᵖ ↔ HasWidePullbacks.{w} C := by
  refine ⟨fun h ι => ?_, fun _ => inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteWidePullbacks
  signature: C] : HasFiniteWidePushouts Cᵒᵖ
  body: by
  refine ⟨fun J _ => ?_⟩
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

中文:
实例 [有FiniteWidePullbacks
  签名: C] : 有FiniteWidePushouts Cᵒᵖ
  定义体: by
  refine ⟨fun J _ => ?_⟩
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

Depends on / 依赖: hasColimitsOfShape_opposite_iff, hasLimitsOfShape_of_equivalence, widePushoutShapeOpEquiv
-/
instance [HasFiniteWidePullbacks C] : HasFiniteWidePushouts Cᵒᵖ := by
  refine ⟨fun J _ => ?_⟩
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteWidePushouts
  signature: C] : HasFiniteWidePullbacks Cᵒᵖ
  body: by
  refine ⟨fun J _ => ?_⟩
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

中文:
实例 [有FiniteWidePushouts
  签名: C] : 有FiniteWidePullbacks Cᵒᵖ
  定义体: by
  refine ⟨fun J _ => ?_⟩
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

Depends on / 依赖: hasColimitsOfShape_of_equivalence, hasLimitsOfShape_opposite_iff, widePullbackShapeOpEquiv
-/
instance [HasFiniteWidePushouts C] : HasFiniteWidePullbacks Cᵒᵖ := by
  refine ⟨fun J _ => ?_⟩
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

/--
lemma `hasFiniteWidePullbacks_opposite_iff` / 引理 `hasFiniteWidePullbacks_opposite_iff`

English:
lemma hasFiniteWidePullbacks_opposite_iff
  proof: by
  refine ⟨fun h => ⟨fun J _ => ?_⟩, fun _ => inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

中文:
引理 hasFiniteWidePullbacks_opposite_iff
  证明: by
  refine ⟨fun h => ⟨fun J _ => ?_⟩, fun _ => inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

Depends on / 依赖: hasLimitsOfShape_of_equivalence, hasLimitsOfShape_opposite_opposite_iff, widePushoutShapeOpEquiv
-/
lemma hasFiniteWidePullbacks_opposite_iff :
    HasFiniteWidePullbacks Cᵒᵖ ↔ HasFiniteWidePushouts C := by
  refine ⟨fun h => ⟨fun J _ => ?_⟩, fun _ => inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm

/--
lemma `hasFiniteWidePushouts_opposite_iff` / 引理 `hasFiniteWidePushouts_opposite_iff`

English:
lemma hasFiniteWidePushouts_opposite_iff
  proof: by
  refine ⟨fun h => ⟨fun J _ => ?_⟩, fun _ => inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

中文:
引理 hasFiniteWidePushouts_opposite_iff
  证明: by
  refine ⟨fun h => ⟨fun J _ => ?_⟩, fun _ => inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

Depends on / 依赖: hasColimitsOfShape_of_equivalence, hasColimitsOfShape_opposite_opposite_iff, widePullbackShapeOpEquiv
-/
lemma hasFiniteWidePushouts_opposite_iff :
    HasFiniteWidePushouts Cᵒᵖ ↔ HasFiniteWidePullbacks C := by
  refine ⟨fun h => ⟨fun J _ => ?_⟩, fun _ => inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

end CategoryTheory.Limits
