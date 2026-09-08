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
/-
**CategoryTheory.Limits.isLimitConeLeftOpOfCocone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) 
: IsLimit (coneLeftOpOfCocone c) where lift s
参数：F : J ⥤ Cᵒᵖ；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`.
-/
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) :
    IsLimit (coneLeftOpOfCocone c) where
  lift s := (hc.desc (coconeOfConeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simp only [coneLeftOpOfCocone_π_app, op_comp, Quiver.Hom.op_unop, IsColimit.fac,
        coconeOfConeLeftOp_ι_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsColimit.fac, coconeOfConeLeftOp_ι_app] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Limits.isColimitCoconeLeftOpOfCone** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) : 
IsColimit (coconeLeftOpOfCone c) where desc s
参数：F : J ⥤ Cᵒᵖ；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.leftOp : Jᵒᵖ ⥤ C`.
-/
def isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) :
    IsColimit (coconeLeftOpOfCone c) where
  desc s := (hc.lift (coneOfCoconeLeftOp s)).unop
  fac s j :=
    Quiver.Hom.op_inj <| by
      simp only [coconeLeftOpOfCone_ι_app, op_comp, Quiver.Hom.op_unop, IsLimit.fac,
        coneOfCoconeLeftOp_π_app, op_unop]
  uniq s m w := by
    refine Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj ?_)
    simpa only [Quiver.Hom.op_unop, IsLimit.fac, coneOfCoconeLeftOp_π_app] using! w (op j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.Limits.isLimitConeRightOpOfCocone** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c)
 : IsLimit (coneRightOpOfCocone c) where lift s
参数：F : Jᵒᵖ ⥤ C；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`.
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
/-
**CategoryTheory.Limits.isColimitCoconeRightOpOfCone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：isColimitCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c) :
 IsColimit (coconeRightOpOfCone c) where desc s
参数：F : Jᵒᵖ ⥤ C；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ`.
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
/-
**CategoryTheory.Limits.isLimitConeUnopOfCocone** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) 
: IsLimit (coneUnopOfCocone c) where lift s
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`.
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
/-
**CategoryTheory.Limits.isColimitCoconeUnopOfCone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isColimitCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) : 
IsColimit (coconeUnopOfCone c) where desc s
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`.
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
/-
**CategoryTheory.Limits.isLimitConeOfCoconeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColi
mit c) : IsLimit (coneOfCoconeLeftOp c) where lift s
参数：F : J ⥤ Cᵒᵖ；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`.
-/
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c) where
  lift s := (hc.desc (coconeLeftOpOfCone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simp only [coneOfCoconeLeftOp_π_app, unop_comp, Quiver.Hom.unop_op, IsColimit.fac,
        coconeLeftOpOfCone_ι_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsColimit.fac, coneOfCoconeLeftOp_π_app] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a limit of `F.leftOp : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.Limits.isColimitCoconeOfConeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimi
t c) : IsColimit (coconeOfConeLeftOp c) where desc s
参数：F : J ⥤ Cᵒᵖ；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit of `F.leftOp : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`.
-/
def isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeLeftOp c) where
  desc s := (hc.lift (coneLeftOpOfCocone s)).op
  fac s j :=
    Quiver.Hom.unop_inj <| by
      simp only [coconeOfConeLeftOp_ι_app, unop_comp, Quiver.Hom.unop_op, IsLimit.fac,
        coneLeftOpOfCocone_π_app, unop_op]
  uniq s m w := by
    refine Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj ?_)
    simpa only [Quiver.Hom.unop_op, IsLimit.fac, coconeOfConeLeftOp_ι_app] using! w (unop j)

set_option backward.isDefEq.respectTransparency false in
/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Limits.isLimitConeOfCoconeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsCo
limit c) : IsLimit (coneOfCoconeRightOp c) where lift s
参数：F : Jᵒᵖ ⥤ C；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`.
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
/-
**CategoryTheory.Limits.isColimitCoconeOfConeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLi
mit c) : IsColimit (coconeOfConeRightOp c) where desc s
参数：F : Jᵒᵖ ⥤ C；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`.
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
/-
**CategoryTheory.Limits.isLimitConeOfCoconeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimi
t c) : IsLimit (coneOfCoconeUnop c) where lift s
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`.
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
/-
**CategoryTheory.Limits.isColimitCoconeOfConeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isColimitCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit 
c) : IsColimit (coconeOfConeUnop c) where desc s
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`.
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
/-
**CategoryTheory.Limits.isColimitOfConeLeftOpOfCocone** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isColimitOfConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsLimit (
coneLeftOpOfCocone c)) : IsColimit c
参数：F : J ⥤ Cᵒᵖ；hc : IsLimit (coneLeftOpOfCocone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F.leftOp : Jᵒᵖ ⥤ C` into a colimit for `F : J ⥤ Cᵒᵖ`.
-/
def isColimitOfConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneLeftOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeLeftOp F hc

/-- Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.Limits.isLimitOfCoconeLeftOpOfCone** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isLimitOfCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsColimit (co
coneLeftOpOfCone c)) : IsLimit c
参数：F : J ⥤ Cᵒᵖ；hc : IsColimit (coconeLeftOpOfCone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F.leftOp : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`.
-/
def isLimitOfCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F}
    (hc : IsColimit (coconeLeftOpOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeLeftOp F hc

/-- Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.Limits.isColimitOfConeRightOpOfCocone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitOfConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsLimit 
(coneRightOpOfCocone c)) : IsColimit c
参数：F : Jᵒᵖ ⥤ C；hc : IsLimit (coneRightOpOfCocone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F.rightOp : J ⥤ Cᵒᵖ` into a colimit for `F : Jᵒᵖ ⥤ C`.
-/
def isColimitOfConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F}
    (hc : IsLimit (coneRightOpOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeRightOp F hc

/-- Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.Limits.isLimitOfCoconeRightOpOfCone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：isLimitOfCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsColimit (c
oconeRightOpOfCone c)) : IsLimit c
参数：F : Jᵒᵖ ⥤ C；hc : IsColimit (coconeRightOpOfCone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F.rightOp : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`.
-/
def isLimitOfCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F}
    (hc : IsColimit (coconeRightOpOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeRightOp F hc

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.Limits.isColimitOfConeUnopOfCocone** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isColimitOfConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsLimit (
coneUnopOfCocone c)) : IsColimit c
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsLimit (coneUnopOfCocone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`.
-/
def isColimitOfConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F}
    (hc : IsLimit (coneUnopOfCocone c)) : IsColimit c :=
  isColimitCoconeOfConeUnop F hc

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.Limits.isLimitOfCoconeUnopOfCone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isLimitOfCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsColimit (co
coneUnopOfCone c)) : IsLimit c
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsColimit (coconeUnopOfCone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`.
-/
def isLimitOfCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F}
    (hc : IsColimit (coconeUnopOfCone c)) : IsLimit c :=
  isLimitConeOfCoconeUnop F hc

/-- Turn a limit for `F : J ⥤ Cᵒᵖ` into a colimit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.Limits.isColimitOfConeOfCoconeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isColimitOfConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : Is
Limit (coneOfCoconeLeftOp c)) : IsColimit c
参数：F : J ⥤ Cᵒᵖ；hc : IsLimit (coneOfCoconeLeftOp c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F : J ⥤ Cᵒᵖ` into a colimit for `F.leftOp : Jᵒᵖ ⥤ C`.
-/
def isColimitOfConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp}
    (hc : IsLimit (coneOfCoconeLeftOp c)) : IsColimit c :=
  isColimitCoconeLeftOpOfCone F hc

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.Limits.isLimitOfCoconeOfConeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isLimitOfCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsColi
mit (coconeOfConeLeftOp c)) : IsLimit c
参数：F : J ⥤ Cᵒᵖ；hc : IsColimit (coconeOfConeLeftOp c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.leftOp : Jᵒᵖ ⥤ C`.
-/
def isLimitOfCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp}
    (hc : IsColimit (coconeOfConeLeftOp c)) : IsLimit c :=
  isLimitConeLeftOpOfCocone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ.` -/
@[simps!]
/-
**CategoryTheory.Limits.isColimitOfConeOfCoconeRightOp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：isColimitOfConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : 
IsLimit (coneOfCoconeRightOp c)) : IsColimit c
参数：F : Jᵒᵖ ⥤ C；hc : IsLimit (coneOfCoconeRightOp c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.rightOp : J ⥤ Cᵒᵖ.`
-/
def isColimitOfConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp}
    (hc : IsLimit (coneOfCoconeRightOp c)) : IsColimit c :=
  isColimitCoconeRightOpOfCone F hc

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.Limits.isLimitOfCoconeOfConeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：isLimitOfCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsCo
limit (coconeOfConeRightOp c)) : IsLimit c
参数：F : Jᵒᵖ ⥤ C；hc : IsColimit (coconeOfConeRightOp c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.rightOp : J ⥤ Cᵒᵖ`.
-/
def isLimitOfCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp}
    (hc : IsColimit (coconeOfConeRightOp c)) : IsLimit c :=
  isLimitConeRightOpOfCocone F hc

/-- Turn a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F.unop : J ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.Limits.isColimitOfConeOfCoconeUnop** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isColimitOfConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsLi
mit (coneOfCoconeUnop c)) : IsColimit c
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsLimit (coneOfCoconeUnop c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F.unop : J ⥤ C`.
-/
def isColimitOfConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop}
    (hc : IsLimit (coneOfCoconeUnop c)) : IsColimit c :=
  isColimitCoconeUnopOfCone F hc

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.Limits.isLimitOfCoconeOfConeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isLimitOfCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsColimi
t (coconeOfConeUnop c)) : IsLimit c
参数：F : Jᵒᵖ ⥤ Cᵒᵖ；hc : IsColimit (coconeOfConeUnop c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`.
-/
def isLimitOfCoconeOfConeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop}
    (hc : IsColimit (coconeOfConeUnop c)) : IsLimit c :=
  isLimitConeUnopOfCocone F hc

/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
/-
**CategoryTheory.Limits.hasLimit_of_hasColimit_leftOp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_of_hasColimit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLim
it F
参数：F : J ⥤ Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If `F.leftOp : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ
`.
-/
theorem hasLimit_of_hasColimit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeLeftOp (colimit.cocone F.leftOp)
      isLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }
/-
**CategoryTheory.Limits.hasLimit_of_hasColimit_op** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasLimit_of_hasColimit_op (F : J ⥤ C) [HasColimit F.op] : HasLimit F
参数：F : J ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
theorem hasLimit_of_hasColimit_op (F : J ⥤ C) [HasColimit F.op] : HasLimit F :=
  HasLimit.mk
    { cone := (colimit.cocone F.op).unop
      isLimit := (colimit.isColimit _).unop }
/-
**CategoryTheory.Limits.hasLimit_of_hasColimit_rightOp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasLimit_of_hasColimit_rightOp (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp] : HasL
imit F
参数：F : Jᵒᵖ ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
theorem hasLimit_of_hasColimit_rightOp (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeRightOp (colimit.cocone F.rightOp)
      isLimit := isLimitConeOfCoconeRightOp _ (colimit.isColimit _) }
/-
**CategoryTheory.Limits.hasLimit_of_hasColimit_unop** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasLimit_of_hasColimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F.unop] : HasLimit
 F
参数：F : Jᵒᵖ ⥤ Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
theorem hasLimit_of_hasColimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F.unop] : HasLimit F :=
  HasLimit.mk
    { cone := coneOfCoconeUnop (colimit.cocone F.unop)
      isLimit := isLimitConeOfCoconeUnop _ (colimit.isColimit _) }
/-
**CategoryTheory.Limits.hasLimit_op_of_hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasLimit_op_of_hasColimit (F : J ⥤ C) [HasColimit F] : HasLimit F.op
参数：F : J ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_op_of_hasColimit (F : J ⥤ C) [HasColimit F] : HasLimit F.op :=
  HasLimit.mk
    { cone := (colimit.cocone F).op
      isLimit := (colimit.isColimit _).op }
/-
**CategoryTheory.Limits.hasLimit_leftOp_of_hasColimit** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_leftOp_of_hasColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.le
ftOp
参数：F : J ⥤ Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_leftOp_of_hasColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.leftOp :=
  HasLimit.mk
    { cone := coneLeftOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeLeftOpOfCocone _ (colimit.isColimit _) }
/-
**CategoryTheory.Limits.hasLimit_rightOp_of_hasColimit** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasLimit_rightOp_of_hasColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] : HasLimit F.r
ightOp
参数：F : Jᵒᵖ ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_rightOp_of_hasColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] : HasLimit F.rightOp :=
  HasLimit.mk
    { cone := coneRightOpOfCocone (colimit.cocone F)
      isLimit := isLimitConeRightOpOfCocone _ (colimit.isColimit _) }
/-
**CategoryTheory.Limits.hasLimit_unop_of_hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasLimit_unop_of_hasColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.un
op
参数：F : Jᵒᵖ ⥤ Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_unop_of_hasColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] : HasLimit F.unop :=
  HasLimit.mk
    { cone := coneUnopOfCocone (colimit.cocone F)
      isLimit := isLimitConeUnopOfCocone _ (colimit.isColimit _) }

/-- The limit of `F.op` is the opposite of `colimit F`. -/
/-
**CategoryTheory.Limits.limitOpIsoOpColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：limitOpIsoOpColimit (F : J ⥤ C) [HasColimit F] : limit F.op ≅ op (colimit 
F)
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of `F.op` is the opposite of `colimit F`.
-/
def limitOpIsoOpColimit (F : J ⥤ C) [HasColimit F] :
    limit F.op ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, (colimit.isColimit _).op⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitOpIsoOpColimit_inv_comp_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitOpIsoOpColimit_inv_comp_π (F : J ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitOpIsoOpColimit F).inv ≫ limit.π F.op j = (colimit.ι F j.unop).op := by
  simp [limitOpIsoOpColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitOpIsoOpColimit_hom_comp_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitOpIsoOpColimit_hom_comp_ι (F : J ⥤ C) [HasColimit F] (j : J) :
    (limitOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.op (op j) := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.leftOp` is the unopposite of `colimit F`. -/
/-
**CategoryTheory.Limits.limitLeftOpIsoUnopColimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：limitLeftOpIsoUnopColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] : limit F.leftOp ≅ 
unop (colimit F)
参数：F : J ⥤ Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of `F.leftOp` is the unopposite of `colimit F`.
-/
def limitLeftOpIsoUnopColimit (F : J ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.leftOp ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeLeftOpOfCocone _ (colimit.isColimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitLeftOpIsoUnopColimit_inv_comp_** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitLeftOpIsoUnopColimit_inv_comp_π (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitLeftOpIsoUnopColimit F).inv ≫ limit.π F.leftOp j = (colimit.ι F j.unop).unop := by
  simp [limitLeftOpIsoUnopColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitLeftOpIsoUnopColimit_hom_comp_** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitLeftOpIsoUnopColimit_hom_comp_ι (F : J ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitLeftOpIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.leftOp (op j) := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.rightOp` is the opposite of `colimit F`. -/
/-
**CategoryTheory.Limits.limitRightOpIsoOpColimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：limitRightOpIsoOpColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] : limit F.rightOp ≅ 
op (colimit F)
参数：F : Jᵒᵖ ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of `F.rightOp` is the opposite of `colimit F`.
-/
def limitRightOpIsoOpColimit (F : Jᵒᵖ ⥤ C) [HasColimit F] :
    limit F.rightOp ≅ op (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeRightOpOfCocone _ (colimit.isColimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitRightOpIsoOpColimit_inv_comp_** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitRightOpIsoOpColimit_inv_comp_π (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : J) :
    (limitRightOpIsoOpColimit F).inv ≫ limit.π F.rightOp j = (colimit.ι F (op j)).op := by
  simp [limitRightOpIsoOpColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitRightOpIsoOpColimit_hom_comp_** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitRightOpIsoOpColimit_hom_comp_ι (F : Jᵒᵖ ⥤ C) [HasColimit F] (j : Jᵒᵖ) :
    (limitRightOpIsoOpColimit F).hom ≫ (colimit.ι F j).op = limit.π F.rightOp j.unop := by
  simp [← Iso.eq_inv_comp]

/-- The limit of `F.unop` is the unopposite of `colimit F`. -/
/-
**CategoryTheory.Limits.limitUnopIsoUnopColimit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：limitUnopIsoUnopColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] : limit F.unop ≅ un
op (colimit F)
参数：F : Jᵒᵖ ⥤ Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of `F.unop` is the unopposite of `colimit F`.
-/
def limitUnopIsoUnopColimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] :
    limit F.unop ≅ unop (colimit F) :=
  limit.isoLimitCone ⟨_, isLimitConeUnopOfCocone _ (colimit.isColimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitUnopIsoUnopColimit_inv_comp_** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitUnopIsoUnopColimit_inv_comp_π (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : J) :
    (limitUnopIsoUnopColimit F).inv ≫ limit.π F.unop j = (colimit.ι F (op j)).unop := by
  simp [limitUnopIsoUnopColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitUnopIsoUnopColimit_hom_comp_** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limitUnopIsoUnopColimit_hom_comp_ι (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasColimit F] (j : Jᵒᵖ) :
    (limitUnopIsoUnopColimit F).hom ≫ (colimit.ι F j).unop = limit.π F.unop j.unop := by
  simp [← Iso.eq_inv_comp]

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
/-
**CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : Has
LimitsOfShape J Cᵒᵖ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_hasColimit_leftOp`：hasLimit_of_hasColi
mit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J
`.
-/
theorem hasLimitsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] :
    HasLimitsOfShape J Cᵒᵖ :=
  { has_limit := fun F => hasLimit_of_hasColimit_leftOp F }
/-
**CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : H
asLimitsOfShape J C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_hasColimit_op`：hasLimit_of_hasColimit_
op (F : J ⥤ C) [HasColimit F.op] : HasLimit F
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasLimitsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasLimitsOfShape J C :=
  { has_limit := fun F => hasLimit_of_hasColimit_op F }

attribute [local instance] hasLimitsOfShape_op_of_hasColimitsOfShape

/-- If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
/-
**CategoryTheory.Limits.hasLimits_op_of_hasColimits** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasLimits_op_of_hasColimits [HasColimitsOfSize.{v₂, u₂} C] : HasLimitsOfSi
ze.{v₂, u₂} Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
instance hasLimits_op_of_hasColimits [HasColimitsOfSize.{v₂, u₂} C] :
    HasLimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩
/-
**CategoryTheory.Limits.hasLimits_of_hasColimits_op** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasLimits_of_hasColimits_op [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ] : HasLimitsOf
Size.{v₂, u₂} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op`：hasLimi
tsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : HasLimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasLimits_of_hasColimits_op [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasLimitsOfSize.{v₂, u₂} C :=
  { has_limits_of_shape := fun _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

/-- If `F.leftOp : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.hasColimit_of_hasLimit_leftOp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasColimit_of_hasLimit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColim
it F
参数：F : J ⥤ Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
If `F.leftOp : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ
`.
-/
theorem hasColimit_of_hasLimit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeLeftOp (limit.cone F.leftOp)
      isColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }
/-
**CategoryTheory.Limits.hasColimit_of_hasLimit_op** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasColimit_of_hasLimit_op (F : J ⥤ C) [HasLimit F.op] : HasColimit F
参数：F : J ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem hasColimit_of_hasLimit_op (F : J ⥤ C) [HasLimit F.op] : HasColimit F :=
  HasColimit.mk
    { cocone := (limit.cone F.op).unop
      isColimit := (limit.isLimit _).unop }
/-
**CategoryTheory.Limits.hasColimit_of_hasLimit_rightOp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasColimit_of_hasLimit_rightOp (F : Jᵒᵖ ⥤ C) [HasLimit F.rightOp] : HasCol
imit F
参数：F : Jᵒᵖ ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem hasColimit_of_hasLimit_rightOp (F : Jᵒᵖ ⥤ C) [HasLimit F.rightOp] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeRightOp (limit.cone F.rightOp)
      isColimit := isColimitCoconeOfConeRightOp _ (limit.isLimit _) }
/-
**CategoryTheory.Limits.hasColimit_of_hasLimit_unop** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimit_of_hasLimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F.unop] : HasColimit
 F
参数：F : Jᵒᵖ ⥤ Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem hasColimit_of_hasLimit_unop (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F.unop] : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfConeUnop (limit.cone F.unop)
      isColimit := isColimitCoconeOfConeUnop _ (limit.isLimit _) }
/-
**CategoryTheory.Limits.hasColimit_op_of_hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasColimit_op_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasColimit F.op
参数：F : J ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_op_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasColimit F.op :=
  HasColimit.mk
    { cocone := (limit.cone F).op
      isColimit := (limit.isLimit _).op }
/-
**CategoryTheory.Limits.hasColimit_leftOp_of_hasLimit** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasColimit_leftOp_of_hasLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.le
ftOp
参数：F : J ⥤ Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_leftOp_of_hasLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.leftOp :=
  HasColimit.mk
    { cocone := coconeLeftOpOfCone (limit.cone F)
      isColimit := isColimitCoconeLeftOpOfCone _ (limit.isLimit _) }
/-
**CategoryTheory.Limits.hasColimit_rightOp_of_hasLimit** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasColimit_rightOp_of_hasLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] : HasColimit F.r
ightOp
参数：F : Jᵒᵖ ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_rightOp_of_hasLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] : HasColimit F.rightOp :=
  HasColimit.mk
    { cocone := coconeRightOpOfCone (limit.cone F)
      isColimit := isColimitCoconeRightOpOfCone _ (limit.isLimit _) }
/-
**CategoryTheory.Limits.hasColimit_unop_of_hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimit_unop_of_hasLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.un
op
参数：F : Jᵒᵖ ⥤ Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_unop_of_hasLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] : HasColimit F.unop :=
  HasColimit.mk
    { cocone := coconeUnopOfCone (limit.cone F)
      isColimit := isColimitCoconeUnopOfCone _ (limit.isLimit _) }

/-- The colimit of `F.op` is the opposite of `limit F`. -/
/-
**CategoryTheory.Limits.colimitOpIsoOpLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：colimitOpIsoOpLimit (F : J ⥤ C) [HasLimit F] : colimit F.op ≅ op (limit F)
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F.op` is the opposite of `limit F`.
-/
def colimitOpIsoOpLimit (F : J ⥤ C) [HasLimit F] :
    colimit F.op ≅ op (limit F) :=
  colimit.isoColimitCocone ⟨_, (limit.isLimit _).op⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_colimitOpIsoOpLimit_hom (F : J ⥤ C) [HasLimit F] (j : Jᵒᵖ) :
    colimit.ι F.op j ≫ (colimitOpIsoOpLimit F).hom = (limit.π F j.unop).op := by
  simp [colimitOpIsoOpLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_colimitOpIsoOpLimit_inv (F : J ⥤ C) [HasLimit F] (j : J) :
    (limit.π F j).op ≫ (colimitOpIsoOpLimit F).inv = colimit.ι F.op (op j) := by
  simp [Iso.comp_inv_eq]

/-- The colimit of `F.leftOp` is the unopposite of `limit F`. -/
/-
**CategoryTheory.Limits.colimitLeftOpIsoUnopLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：colimitLeftOpIsoUnopLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] : colimit F.leftOp ≅ 
unop (limit F)
参数：F : J ⥤ Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F.leftOp` is the unopposite of `limit F`.
-/
def colimitLeftOpIsoUnopLimit (F : J ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.leftOp ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeLeftOpOfCone _ (limit.isLimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_colimitLeftOpIsoUnopLimit_hom (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ) :
    colimit.ι F.leftOp j ≫ (colimitLeftOpIsoUnopLimit F).hom = (limit.π F j.unop).unop := by
  simp [colimitLeftOpIsoUnopLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_colimitLeftOpIsoUnopLimit_inv (F : J ⥤ Cᵒᵖ) [HasLimit F] (j : J) :
    (limit.π F j).unop ≫ (colimitLeftOpIsoUnopLimit F).inv = colimit.ι F.leftOp (op j) := by
  simp [Iso.comp_inv_eq]

/-- The colimit of `F.rightOp` is the opposite of `limit F`. -/
/-
**CategoryTheory.Limits.colimitRightOpIsoUnopLimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：colimitRightOpIsoUnopLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] : colimit F.rightOp 
≅ op (limit F)
参数：F : Jᵒᵖ ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F.rightOp` is the opposite of `limit F`.
-/
def colimitRightOpIsoUnopLimit (F : Jᵒᵖ ⥤ C) [HasLimit F] :
    colimit F.rightOp ≅ op (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeRightOpOfCone _ (limit.isLimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_colimitRightOpIsoUnopLimit_hom (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : J) :
    colimit.ι F.rightOp j ≫ (colimitRightOpIsoUnopLimit F).hom = (limit.π F (op j)).op := by
  simp [colimitRightOpIsoUnopLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_colimitRightOpIsoUnopLimit_inv (F : Jᵒᵖ ⥤ C) [HasLimit F] (j : Jᵒᵖ) :
    (limit.π F j).op ≫ (colimitRightOpIsoUnopLimit F).inv = colimit.ι F.rightOp j.unop := by
  simp [Iso.comp_inv_eq]

/-- The colimit of `F.unop` is the unopposite of `limit F`. -/
/-
**CategoryTheory.Limits.colimitUnopIsoOpLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：colimitUnopIsoOpLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] : colimit F.unop ≅ unop
 (limit F)
参数：F : Jᵒᵖ ⥤ Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F.unop` is the unopposite of `limit F`.
-/
def colimitUnopIsoOpLimit (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] :
    colimit F.unop ≅ unop (limit F) :=
  colimit.isoColimitCocone ⟨_, isColimitCoconeUnopOfCone _ (limit.isLimit _)⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_colimitUnopIsoOpLimit_hom (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : J) :
    colimit.ι F.unop j ≫ (colimitUnopIsoOpLimit F).hom = (limit.π F (op j)).unop := by
  simp [colimitUnopIsoOpLimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_colimitUnopIsoOpLimit_inv (F : Jᵒᵖ ⥤ Cᵒᵖ) [HasLimit F] (j : Jᵒᵖ) :
    (limit.π F j).unop ≫ (colimitUnopIsoOpLimit F).inv = colimit.ι F.unop j.unop := by
  simp [Iso.comp_inv_eq]

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
/-
**CategoryTheory.Limits.hasColimitsOfShape_op_of_hasLimitsOfShape** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_op_of_hasLimitsOfShape [HasLimitsOfShape Jᵒᵖ C] : HasCo
limitsOfShape J Cᵒᵖ where has_colimit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_hasLimit_leftOp`：hasColimit_of_hasLi
mit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J
`.
-/
instance hasColimitsOfShape_op_of_hasLimitsOfShape [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J Cᵒᵖ where has_colimit F := hasColimit_of_hasLimit_leftOp F
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : Has
ColimitsOfShape J C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_hasLimit_op`：hasColimit_of_hasLimit_
op (F : J ⥤ C) [HasLimit F.op] : HasColimit F
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasColimitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] :
    HasColimitsOfShape J C :=
  { has_colimit := fun F => hasColimit_of_hasLimit_op F }

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
/-
**CategoryTheory.Limits.hasColimits_op_of_hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimits_op_of_hasLimits [HasLimitsOfSize.{v₂, u₂} C] : HasColimitsOfSi
ze.{v₂, u₂} Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
instance hasColimits_op_of_hasLimits [HasLimitsOfSize.{v₂, u₂} C] :
    HasColimitsOfSize.{v₂, u₂} Cᵒᵖ :=
  ⟨fun _ => inferInstance⟩
/-
**CategoryTheory.Limits.hasColimits_of_hasLimits_op** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimits_of_hasLimits_op [HasLimitsOfSize.{v₂, u₂} Cᵒᵖ] : HasColimitsOf
Size.{v₂, u₂} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op`：hasColi
mitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : HasColimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasColimits_of_hasLimits_op [HasLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasColimitsOfSize.{v₂, u₂} C :=
  { has_colimits_of_shape := fun _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }
/-
**CategoryTheory.Limits.hasColimitsOfSize_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfSize_opposite_iff : HasColimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasLimit
sOfSize.{v₂, u₂} C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimits_of_hasColimits_op`：hasLimits_of_hasColim
its_op [HasColimitsOfSize.{v₂, u₂} Cᵒᵖ] : HasLimitsOfSize.{v₂, u₂} C
-/
lemma hasColimitsOfSize_opposite_iff :
    HasColimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasLimitsOfSize.{v₂, u₂} C :=
  ⟨fun _ ↦ hasLimits_of_hasColimits_op, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasLimitsOfSize_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasLimitsOfSize_opposite_iff : HasLimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasColimitsO
fSize.{v₂, u₂} C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimits_of_hasLimits_op`：hasColimits_of_hasLim
its_op [HasLimitsOfSize.{v₂, u₂} Cᵒᵖ] : HasColimitsOfSize.{v₂, u₂} C
-/
lemma hasLimitsOfSize_opposite_iff :
    HasLimitsOfSize.{v₂, u₂} Cᵒᵖ ↔ HasColimitsOfSize.{v₂, u₂} C :=
  ⟨fun _ ↦ hasColimits_of_hasLimits_op, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasFiniteColimits_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteColimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasColimitsOfShape_op_of_hasLimitsOfShape⟩
/-
**CategoryTheory.Limits.hasFiniteLimits_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasFiniteLimits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
-/
instance hasFiniteLimits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  ⟨fun _ _ _ => hasLimitsOfShape_op_of_hasColimitsOfShape⟩
/-
**CategoryTheory.Limits.hasFiniteLimits_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasFiniteLimits_opposite_iff : HasFiniteLimits Cᵒᵖ ↔ HasFiniteColimits C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op`：hasColi
mitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : HasColimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
lemma hasFiniteLimits_opposite_iff : HasFiniteLimits Cᵒᵖ ↔ HasFiniteColimits C :=
  ⟨fun _ ↦ ⟨fun _ _ _ ↦ hasColimitsOfShape_of_hasLimitsOfShape_op⟩, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasFiniteColimits_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasFiniteColimits_opposite_iff : HasFiniteColimits Cᵒᵖ ↔ HasFiniteLimits C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op`：hasLimi
tsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : HasLimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
-/
lemma hasFiniteColimits_opposite_iff : HasFiniteColimits Cᵒᵖ ↔ HasFiniteLimits C :=
  ⟨fun _ ↦ ⟨fun _ _ _ ↦ hasLimitsOfShape_of_hasColimitsOfShape_op⟩, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasColimit_op_iff_hasLimit** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasColimit_op_iff_hasLimit {F : J ⥤ C} : HasColimit F.op ↔ HasLimit F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_hasColimit_op`：hasLimit_of_hasColimit_
op (F : J ⥤ C) [HasColimit F.op] : HasLimit F
-/
lemma hasColimit_op_iff_hasLimit {F : J ⥤ C} : HasColimit F.op ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_op F, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasColimit_leftOp_iff_hasLimit** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasColimit_leftOp_iff_hasLimit {F : J ⥤ Cᵒᵖ} : HasColimit F.leftOp ↔ HasLi
mit F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_hasColimit_leftOp`：hasLimit_of_hasColi
mit_leftOp (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F
-/
lemma hasColimit_leftOp_iff_hasLimit {F : J ⥤ Cᵒᵖ} : HasColimit F.leftOp ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_leftOp F, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasColimit_rightOp_iff_hasLimit** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_rightOp_iff_hasLimit {F : Jᵒᵖ ⥤ C} : HasColimit F.rightOp ↔ Has
Limit F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_hasColimit_rightOp`：hasLimit_of_hasCol
imit_rightOp (F : Jᵒᵖ ⥤ C) [HasColimit F.rightOp] : HasLimit F
-/
lemma hasColimit_rightOp_iff_hasLimit {F : Jᵒᵖ ⥤ C} : HasColimit F.rightOp ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_rightOp F, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasLimit_op_iff_hasColimit** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasLimit_op_iff_hasColimit {F : J ⥤ C} : HasLimit F.op ↔ HasColimit F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_hasLimit_op`：hasColimit_of_hasLimit_
op (F : J ⥤ C) [HasLimit F.op] : HasColimit F
-/
lemma hasLimit_op_iff_hasColimit {F : J ⥤ C} : HasLimit F.op ↔ HasColimit F :=
  ⟨fun _ ↦ hasColimit_of_hasLimit_op F, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasLimit_leftOp_iff_hasColimit** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasLimit_leftOp_iff_hasColimit {F : J ⥤ Cᵒᵖ} : HasLimit F.leftOp ↔ HasColi
mit F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_hasLimit_leftOp`：hasColimit_of_hasLi
mit_leftOp (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F
-/
lemma hasLimit_leftOp_iff_hasColimit {F : J ⥤ Cᵒᵖ} : HasLimit F.leftOp ↔ HasColimit F :=
  ⟨fun _ ↦ hasColimit_of_hasLimit_leftOp F, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasLimit_rightOp_iff_hasColimit** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasLimit_rightOp_iff_hasColimit {F : Jᵒᵖ ⥤ C} : HasLimit F.rightOp ↔ HasCo
limit F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_hasLimit_rightOp`：hasColimit_of_hasL
imit_rightOp (F : Jᵒᵖ ⥤ C) [HasLimit F.rightOp] : HasColimit F
-/
lemma hasLimit_rightOp_iff_hasColimit {F : Jᵒᵖ ⥤ C} : HasLimit F.rightOp ↔ HasColimit F :=
  ⟨fun _ ↦ hasColimit_of_hasLimit_rightOp F, fun _ ↦ inferInstance⟩
/-
**CategoryTheory.Limits.hasLimitsOfShape_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_opposite_iff : HasLimitsOfShape J Cᵒᵖ ↔ HasColimitsOfShap
e Jᵒᵖ C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op`：hasColi
mitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : HasColimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
-/
lemma hasLimitsOfShape_opposite_iff : HasLimitsOfShape J Cᵒᵖ ↔ HasColimitsOfShape Jᵒᵖ C := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_of_hasLimitsOfShape_op
/-
**CategoryTheory.Limits.hasColimitsOfShape_opposite_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_opposite_iff : HasColimitsOfShape J Cᵒᵖ ↔ HasLimitsOfSh
ape Jᵒᵖ C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op`：hasLimi
tsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : HasLimitsOfSha
pe J C
-/
lemma hasColimitsOfShape_opposite_iff : HasColimitsOfShape J Cᵒᵖ ↔ HasLimitsOfShape Jᵒᵖ C := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ Cᵒᵖ := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_of_hasColimitsOfShape_op
/-
**CategoryTheory.Limits.hasLimitsOfShape_opposite_opposite_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_opposite_opposite_iff : HasLimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasCol
imitsOfShape J C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op`：hasColi
mitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : HasColimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
-/
lemma hasLimitsOfShape_opposite_opposite_iff :
    HasLimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasColimitsOfShape J C := by
  refine ⟨fun _ ↦ hasColimitsOfShape_of_hasLimitsOfShape_op, fun _ ↦ ?_⟩
  have : HasColimitsOfShape Jᵒᵖᵒᵖ C := hasColimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape
/-
**CategoryTheory.Limits.hasColimitsOfShape_opposite_opposite_iff** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_opposite_opposite_iff : HasColimitsOfShape Jᵒᵖ Cᵒᵖ ↔ Ha
sLimitsOfShape J C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op`：hasLimi
tsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : HasLimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
lemma hasColimitsOfShape_opposite_opposite_iff :
    HasColimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasLimitsOfShape J C := by
  refine ⟨fun _ ↦ hasLimitsOfShape_of_hasColimitsOfShape_op, fun _ ↦ ?_⟩
  have : HasLimitsOfShape Jᵒᵖᵒᵖ C := hasLimitsOfShape_of_equivalence (opOpEquivalence J).symm
  exact hasColimitsOfShape_op_of_hasLimitsOfShape
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasWidePullbacks.{w} C] : HasWidePushouts.{w} Cᵒᵖ := by
  intro ι
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasWidePushouts.{w} C] : HasWidePullbacks.{w} Cᵒᵖ := by
  intro ι
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.hasWidePullbacks_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasWidePullbacks_opposite_iff : HasWidePullbacks.{w} Cᵒᵖ ↔ HasWidePushouts
.{w} C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.hasLimitsOfShape_opposite_opposite_iff`：hasLimitsO
fShape_opposite_opposite_iff : HasLimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasColimitsOfShape J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasWidePullbacksOppositeOfHasWidePushouts`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.
HasWidePushouts C],   CategoryTheory.Limits.HasWidePullba…
-/
lemma hasWidePullbacks_opposite_iff :
    HasWidePullbacks.{w} Cᵒᵖ ↔ HasWidePushouts.{w} C := by
  refine ⟨fun h ι ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.hasWidePushouts_opposite_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasWidePushouts_opposite_iff : HasWidePushouts.{w} Cᵒᵖ ↔ HasWidePullbacks.
{w} C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.hasColimitsOfShape_opposite_opposite_iff`：hasColim
itsOfShape_opposite_opposite_iff : HasColimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasLimitsOfShape
 J C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasWidePushoutsOppositeOfHasWidePullbacks`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.
HasWidePullbacks C],   CategoryTheory.Limits.HasWidePusho…
-/
lemma hasWidePushouts_opposite_iff :
    HasWidePushouts.{w} Cᵒᵖ ↔ HasWidePullbacks.{w} C := by
  refine ⟨fun h ι ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteWidePullbacks C] : HasFiniteWidePushouts Cᵒᵖ := by
  refine ⟨fun J _ ↦ ?_⟩
  rw [hasColimitsOfShape_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteWidePushouts C] : HasFiniteWidePullbacks Cᵒᵖ := by
  refine ⟨fun J _ ↦ ?_⟩
  rw [hasLimitsOfShape_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.hasFiniteWidePullbacks_opposite_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteWidePullbacks_opposite_iff : HasFiniteWidePullbacks Cᵒᵖ ↔ HasFini
teWidePushouts C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.hasLimitsOfShape_opposite_opposite_iff`：hasLimitsO
fShape_opposite_opposite_iff : HasLimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasColimitsOfShape J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasFiniteWidePullbacksOppositeOfHasFiniteWideP
ushouts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTh
eory.Limits.HasFiniteWidePushouts C],   CategoryTheory.Limits.HasFini…
-/
lemma hasFiniteWidePullbacks_opposite_iff :
    HasFiniteWidePullbacks Cᵒᵖ ↔ HasFiniteWidePushouts C := by
  refine ⟨fun h ↦ ⟨fun J _ ↦ ?_⟩, fun _ ↦ inferInstance⟩
  rw [← hasLimitsOfShape_opposite_opposite_iff]
  exact hasLimitsOfShape_of_equivalence (widePushoutShapeOpEquiv _).symm
/-
**CategoryTheory.Limits.hasFiniteWidePushouts_opposite_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteWidePushouts_opposite_iff : HasFiniteWidePushouts Cᵒᵖ ↔ HasFinite
WidePullbacks C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.hasColimitsOfShape_opposite_opposite_iff`：hasColim
itsOfShape_opposite_opposite_iff : HasColimitsOfShape Jᵒᵖ Cᵒᵖ ↔ HasLimitsOfShape
 J C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasFiniteWidePushoutsOppositeOfHasFiniteWidePu
llbacks`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTh
eory.Limits.HasFiniteWidePullbacks C],   CategoryTheory.Limits.HasFin…
-/
lemma hasFiniteWidePushouts_opposite_iff :
    HasFiniteWidePushouts Cᵒᵖ ↔ HasFiniteWidePullbacks C := by
  refine ⟨fun h ↦ ⟨fun J _ ↦ ?_⟩, fun _ ↦ inferInstance⟩
  rw [← hasColimitsOfShape_opposite_opposite_iff]
  exact hasColimitsOfShape_of_equivalence (widePullbackShapeOpEquiv _).symm

end CategoryTheory.Limits

