/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The category of presheaves of modules over a scheme

In this file, given a scheme `X`, we define the category of presheaves
of modules over `X`. As categories of presheaves of modules are
defined for presheaves of rings (and not presheaves of commutative rings),
we also introduce a definition `X.ringCatSheaf` for the underlying sheaf
of rings of `X`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X Y : Scheme.{u})

/-- The underlying sheaf of rings of a scheme. -/
/-
**AlgebraicGeometry.Scheme.ringCatSheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：ringCatSheaf : TopCat.Sheaf RingCat.{u} X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying sheaf of rings of a scheme.
-/
abbrev ringCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of presheaves of modules over a scheme. -/
nonrec abbrev PresheafOfModules := PresheafOfModules.{u} X.ringCatSheaf.obj

variable {X Y} in
/-- The morphism of sheaves of rings corresponding to a morphism of schemes. -/
/-
**AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) →     Y.ringCatSheaf ⟶   
    ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous RingCat (Ope
ns.grothendieckTopology ↥Y)             (Opens.grothendieckTopology ↥X)).obj    
     X.ringCatSheaf
参数：f : X ⟶ Y；(TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous Ring
Cat (Opens.grothendieckTopology ↥Y)             (Opens.grothendieckTopology ↥X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of sheaves of rings corresponding to a morphism of schemes.
-/
def Hom.toRingCatSheafHom (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      _ _ _).obj X.ringCatSheaf where
  hom := Functor.whiskerRight f.c _

end AlgebraicGeometry.Scheme

