/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
# `Over X` when `C` has strict initial objects

In this file we define the canonical equivalence of `Over X` with `Discrete PUnit` when
`C` has strict initial objects. We also provide the variants for `P.Over Q X`
and the dual versions.
-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict initial objects and `X` is an initial object, the category
`Over X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/-
**CategoryTheory.overEquivOfIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X)
 : Over X ≌ Discrete PUnit.{w + 1} where functor
参数：X : C；h : IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X) :
    Over X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `C` has strict terminal objects and `X` is a terminal object, the category
`Under X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/-
**CategoryTheory.underEquivOfIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：underEquivOfIsTerminal [HasStrictTerminalObjects C] (X : C) (h : IsTermina
l X) : Under X ≌ Discrete PUnit.{w + 1} where functor
参数：X : C；h : IsTerminal X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def underEquivOfIsTerminal [HasStrictTerminalObjects C] (X : C) (h : IsTerminal X) :
    Under X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk (𝟙 X))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

variable (P Q : MorphismProperty C) [P.ContainsIdentities] [Q.IsMultiplicative] [Q.RespectsIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict initial objects and `X` is an initial object, the category
`P.Over Q X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/-
**CategoryTheory.MorphismProperty.overEquivOfIsInitial** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     (P 
Q : CategoryTheory.MorphismProperty C) →       [P.ContainsIdentities] →         
[inst_2 : Q.IsMultiplicative] →           [Q.RespectsIso] →             [Categor
yTheory.Limits.HasStrictInitialObjects C] →               (X : C) → CategoryTheo
ry.Limits.IsInitial X → (P.Over Q X ≌ CategoryTheory.Discrete PUnit.{w + 1})
参数：P Q : CategoryTheory.MorphismProperty C；X : C；P.Over Q X ≌ CategoryTheory.Dis
crete PUnit.{w + 1}。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
def MorphismProperty.overEquivOfIsInitial [HasStrictInitialObjects C] (X : C) (h : IsInitial X) :
    P.Over Q X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_to A.hom
    Over.isoMk (asIso A.hom)
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has strict terminal objects and `X` is a terminal object, the category
`P.Under Q X` is equivalent to a point. -/
@[simps, pp_with_univ]
noncomputable
/-
**CategoryTheory.MorphismProperty.underEquivOfIsTerminal** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     (P 
Q : CategoryTheory.MorphismProperty C) →       [P.ContainsIdentities] →         
[inst_2 : Q.IsMultiplicative] →           [Q.RespectsIso] →             [Categor
yTheory.Limits.HasStrictTerminalObjects C] →               (X : C) → CategoryThe
ory.Limits.IsTerminal X → (P.Under Q X ≌ CategoryTheory.Discrete PUnit.{w + 1})
参数：P Q : CategoryTheory.MorphismProperty C；X : C；P.Under Q X ≌ CategoryTheory.Di
screte PUnit.{w + 1}。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
def MorphismProperty.underEquivOfIsTerminal [HasStrictTerminalObjects C] (X : C)
    (h : IsTerminal X) :
    P.Under Q X ≌ Discrete PUnit.{w + 1} where
  functor := Functor.star _
  inverse := Functor.fromPUnit (.mk _ (𝟙 X) (P.id_mem _))
  counitIso := Iso.refl _
  unitIso := NatIso.ofComponents fun A ↦
    haveI := h.isIso_from A.hom
    Under.isoMk (asIso A.hom).symm

end CategoryTheory

