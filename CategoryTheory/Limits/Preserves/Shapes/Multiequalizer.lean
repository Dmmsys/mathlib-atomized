/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Preservation of multicoequalizers

Let `J : MultispanShape` and `d : MultispanIndex J C`.
If `F : C ⥤ D`, we define `d.map F : MultispanIndex J D` and
an isomorphism of functors `(d.map F).multispan ≅ d.multispan ⋙ F`
(see `MultispanIndex.multispanMapIso`).
If `c : Multicofork d`, we define `c.map F : Multicofork (d.map F)` and
obtain a bijection `IsColimit (F.mapCocone c) ≃ IsColimit (c.map F)`
(see `Multicofork.isColimitMapEquiv`). As a result, if `F` preserves
the colimit of `d.multispan`, we deduce that if `c` is a colimit,
then `c.map F` also is (see `Multicofork.isColimitMapOfPreserves`).

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

namespace Limits

section Multifork

variable {J : MulticospanShape.{w, w'}} (d : MulticospanIndex J C)
  (c : Multifork d) (F : C ⥤ D)

/-- The multicospan index obtained by applying a functor. -/
@[simps]
/-
**CategoryTheory.Limits.MulticospanIndex.map** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.MulticospanIndex`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MulticospanShape} →           CategoryTheory.Limits.Mul
ticospanIndex J C →             CategoryTheory.Functor C D → CategoryTheory.Limi
ts.MulticospanIndex J D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicospan index obtained by applying a functor.
-/
def MulticospanIndex.map : MulticospanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MulticospanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multicospan ≅ d.multicospan ⋙ F`. -/
@[simps!]
/-
**CategoryTheory.Limits.MulticospanIndex.multicospanMapIso** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MulticospanShape} →           (d : CategoryTheory.Limit
s.MulticospanIndex J C) →             (F : CategoryTheory.Functor C D) → (d.map 
F).multicospan ≅ d.multicospan.comp F
参数：d : CategoryTheory.Limits.MulticospanIndex J C；F : CategoryTheory.Functor C D
；d.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : MulticospanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multicospan ≅ d.multicospan ⋙ F`.
-/
def MulticospanIndex.multicospanMapIso : (d.map F).multicospan ≅ d.multicospan ⋙ F :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro a b (_ | _) <;> simp)

variable {d}

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
this is the induced multifork of `d.map F`. -/
@[simps!]
/-
**CategoryTheory.Limits.Multifork.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Multifork`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MulticospanShape} →           {d : CategoryTheory.Limit
s.MulticospanIndex J C} →             CategoryTheory.Limits.Multifork d →       
        (F : CategoryTheory.Functor C D) → CategoryTheory.Limits.Multifork (d.ma
p F)
参数：F : CategoryTheory.Functor C D；d.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
this is the induced multifork of `d.map F`.
-/
def Multifork.map : Multifork (d.map F) :=
  Multifork.ofι _ (F.obj c.pt) (fun i ↦ F.map (c.ι i)) (fun j ↦ by
    dsimp
    rw [← F.map_comp, ← F.map_comp, condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
the cone `F.mapCone c` is limiting iff the multifork `c.map F` is. -/
/-
**CategoryTheory.Limits.Multifork.isLimitMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Multifork`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MulticospanShape} →           {d : CategoryTheory.Limit
s.MulticospanIndex J C} →             (c : CategoryTheory.Limits.Multifork d) → 
              (F : CategoryTheory.Functor C D) →                 CategoryTheory.
Limits.IsLimit (F.mapCone c) ≃ CategoryTheory.Limits.IsLimit (c.map F)
参数：c : CategoryTheory.Limits.Multifork d；F : CategoryTheory.Functor C D；F.mapCon
e c；c.map F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
the cone `F.mapCone c` is limiting iff the multifork `c.map F` is.
-/
def Multifork.isLimitMapEquiv :
    IsLimit (F.mapCone c) ≃ IsLimit (c.map F) :=
  Equiv.trans (IsLimit.postcomposeInvEquiv (d.multicospanMapIso F) (F.mapCone c)).symm
    (IsLimit.equivIsoLimit
      (Multifork.ext (Iso.refl _) (fun i ↦ by dsimp only [Multifork.ι]; simp)))

/-- If `d : MulticospanIndex J C`, `c : Multifork d` is a limit multifork,
and `F : C ⥤ D` is a functor which preserves the limit of `d.multicospan`,
then the multifork `c.map F` is limiting. -/
/-
**CategoryTheory.Limits.Multifork.isLimitMapOfPreserves** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Multifork`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MulticospanShape} →           {d : CategoryTheory.Limit
s.MulticospanIndex J C} →             (c : CategoryTheory.Limits.Multifork d) → 
              (F : CategoryTheory.Functor C D) →                 [CategoryTheory
.Limits.PreservesLimit d.multicospan F] →                   CategoryTheory.Limit
s.IsLimit c → CategoryTheory.Limits.IsLimit (c.map F)
参数：c : CategoryTheory.Limits.Multifork d；F : CategoryTheory.Functor C D；c.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : MulticospanIndex J C`, `c : Multifork d` is a limit multifork,
and `F : C ⥤ D` is a functor which preserves the limit of `d.multicospan`,
then the multifork `c.map F` is limiting.
-/
noncomputable def Multifork.isLimitMapOfPreserves
    [PreservesLimit d.multicospan F] (hc : IsLimit c) : IsLimit (c.map F) :=
  (isLimitMapEquiv c F) (isLimitOfPreserves F hc)

end Multifork

section Multicofork

variable {J : MultispanShape.{w, w'}} (d : MultispanIndex J C)
  (c : Multicofork d) (F : C ⥤ D)

/-- The multispan index obtained by applying a functor. -/
@[simps]
/-
**CategoryTheory.Limits.MultispanIndex.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.MultispanIndex`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MultispanShape} →           CategoryTheory.Limits.Multi
spanIndex J C →             CategoryTheory.Functor C D → CategoryTheory.Limits.M
ultispanIndex J D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multispan index obtained by applying a functor.
-/
def MultispanIndex.map : MultispanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MultispanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multispan ≅ d.multispan ⋙ F`. -/
@[simps!]
/-
**CategoryTheory.Limits.MultispanIndex.multispanMapIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MultispanShape} →           (d : CategoryTheory.Limits.
MultispanIndex J C) →             (F : CategoryTheory.Functor C D) → (d.map F).m
ultispan ≅ d.multispan.comp F
参数：d : CategoryTheory.Limits.MultispanIndex J C；F : CategoryTheory.Functor C D；d
.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : MultispanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multispan ≅ d.multispan ⋙ F`.
-/
def MultispanIndex.multispanMapIso : (d.map F).multispan ≅ d.multispan ⋙ F :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

variable {d}

set_option backward.defeqAttrib.useBackward true in
/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
this is the induced multicofork of `d.map F`. -/
@[simps!]
/-
**CategoryTheory.Limits.Multicofork.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Multicofork`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MultispanShape} →           {d : CategoryTheory.Limits.
MultispanIndex J C} →             CategoryTheory.Limits.Multicofork d →         
      (F : CategoryTheory.Functor C D) → CategoryTheory.Limits.Multicofork (d.ma
p F)
参数：F : CategoryTheory.Functor C D；d.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
this is the induced multicofork of `d.map F`.
-/
def Multicofork.map : Multicofork (d.map F) :=
  Multicofork.ofπ _ (F.obj c.pt) (fun i ↦ F.map (c.π i)) (fun j ↦ by
    dsimp
    rw [← F.map_comp, ← F.map_comp, condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
the cocone `F.mapCocone c` is colimit iff the multicofork `c.map F` is. -/
/-
**CategoryTheory.Limits.Multicofork.isColimitMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.Multicofork`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MultispanShape} →           {d : CategoryTheory.Limits.
MultispanIndex J C} →             (c : CategoryTheory.Limits.Multicofork d) →   
            (F : CategoryTheory.Functor C D) →                 CategoryTheory.Li
mits.IsColimit (F.mapCocone c) ≃ CategoryTheory.Limits.IsColimit (c.map F)
参数：c : CategoryTheory.Limits.Multicofork d；F : CategoryTheory.Functor C D；F.mapC
ocone c；c.map F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
the cocone `F.mapCocone c` is colimit iff the multicofork `c.map F` is.
-/
def Multicofork.isColimitMapEquiv :
    IsColimit (F.mapCocone c) ≃ IsColimit (c.map F) :=
  (IsColimit.precomposeInvEquiv (d.multispanMapIso F).symm (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i ↦ by dsimp only [Multicofork.π]; simp)))

/-- If `d : MultispanIndex J C`, `c : Multicofork d` is a colimit multicofork,
and `F : C ⥤ D` is a functor which preserves the colimit of `d.multispan`,
then the multicofork `c.map F` is colimit. -/
/-
**CategoryTheory.Limits.Multicofork.isColimitMapOfPreserves** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.Multicofork`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {J
 : CategoryTheory.Limits.MultispanShape} →           {d : CategoryTheory.Limits.
MultispanIndex J C} →             (c : CategoryTheory.Limits.Multicofork d) →   
            (F : CategoryTheory.Functor C D) →                 [CategoryTheory.L
imits.PreservesColimit d.multispan F] →                   CategoryTheory.Limits.
IsColimit c → CategoryTheory.Limits.IsColimit (c.map F)
参数：c : CategoryTheory.Limits.Multicofork d；F : CategoryTheory.Functor C D；c.map 
F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : MultispanIndex J C`, `c : Multicofork d` is a colimit multicofork,
and `F : C ⥤ D` is a functor which preserves the colimit of `d.multispan`,
then the multicofork `c.map F` is colimit.
-/
noncomputable def Multicofork.isColimitMapOfPreserves
    [PreservesColimit d.multispan F] (hc : IsColimit c) : IsColimit (c.map F) :=
  (isColimitMapEquiv c F) (isColimitOfPreserves F hc)

end Multicofork

end Limits

end CategoryTheory

