/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Tactic.ApplyFun

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : Arrow C`:
1. `f.cechNerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmentedCechNerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `SimplicialObject.cechNerve` and `SimplicialObject.augmentedCechNerve` are
  functorial versions of 1 resp. 2.

We end the file with a description of the Čech nerve of an arrow `X ⟶ ⊤_ C` to a terminal
object, when `C` has finite products. We call this `cechNerveTerminalFrom`. When `C` is
`G`-Set this gives us `EG` (the universal cover of the classifying space of `G`) as a simplicial
`G`-set, which is useful for group cohomology.

-/

@[expose] public section


open CategoryTheory Limits

open scoped Simplicial

noncomputable section

universe v u w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Arrow

variable (f : Arrow C)
variable [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The Čech nerve associated to an arrow. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Arrow.cechNerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：cechNerve : SimplicialObject C where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Čech nerve associated to an arrow.
-/
def cechNerve : SimplicialObject C where
  obj n := widePullback.{0} f.right (fun _ : Fin (n.unop.len + 1) => f.left) fun _ => f.hom
  map g := WidePullback.lift (WidePullback.base _)
    (fun i => WidePullback.π _ (g.unop.toOrderHom i)) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism between Čech nerves associated to a morphism of arrows. -/
@[simps]
/-
**CategoryTheory.Arrow.mapCechNerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ar
row`。
形式化陈述：mapCechNerve {f g : Arrow C} [forall n : Nat, HasWidePullback f.right (fun
 _ : Fin (n + 1) => f.left) fun _ => f.hom] [forall n : Nat, HasWidePullback g.r
ight (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) : f.cechNerve ⟶
 g.cechNerve where app n
参数：fun _ : Fin (n + 1) => f.left；fun _ : Fin (n + 1) => g.left；F : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between Čech nerves associated to a morphism of arrows.
-/
def mapCechNerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) :
    f.cechNerve ⟶ g.cechNerve where
  app n :=
    WidePullback.lift (WidePullback.base _ ≫ F.right) (fun i => WidePullback.π _ i ≫ F.left)
      fun j => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
/-
**CategoryTheory.Arrow.augmentedCechNerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Arrow`。
形式化陈述：augmentedCechNerve : SimplicialObject.Augmented C where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech nerve associated to an arrow.
-/
def augmentedCechNerve : SimplicialObject.Augmented C where
  left := f.cechNerve
  right := f.right
  hom := { app := fun _ => WidePullback.base _ }

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between augmented Čech nerve associated to a morphism of arrows. -/
@[simps]
/-
**CategoryTheory.Arrow.mapAugmentedCechNerve** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Arrow`。
形式化陈述：mapAugmentedCechNerve {f g : Arrow C} [forall n : Nat, HasWidePullback f.r
ight (fun _ : Fin (n + 1) => f.left) fun _ => f.hom] [forall n : Nat, HasWidePul
lback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) : f.au
gmentedCechNerve ⟶ g.augmentedCechNerve where left
参数：fun _ : Fin (n + 1) => f.left；fun _ : Fin (n + 1) => g.left；F : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between augmented Čech nerve associated to a morphism of arrows.
-/
def mapAugmentedCechNerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) => g.left) fun _ => g.hom] (F : f ⟶ g) :
    f.augmentedCechNerve ⟶ g.augmentedCechNerve where
  left := mapCechNerve F
  right := F.right

end CategoryTheory.Arrow

namespace CategoryTheory

namespace SimplicialObject

variable
  [∀ (n : ℕ) (f : Arrow C), HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Čech nerve construction, as a functor from `Arrow C`. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.cechNerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.SimplicialObject`。
形式化陈述：cechNerve : Arrow C ⥤ SimplicialObject C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Čech nerve construction, as a functor from `Arrow C`.
-/
def cechNerve : Arrow C ⥤ SimplicialObject C where
  obj f := f.cechNerve
  map F := Arrow.mapCechNerve F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve construction, as a functor from `Arrow C`. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.augmentedCechNerve** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SimplicialObject`。
形式化陈述：augmentedCechNerve : Arrow C ⥤ SimplicialObject.Augmented C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech nerve construction, as a functor from `Arrow C`.
-/
def augmentedCechNerve : Arrow C ⥤ SimplicialObject.Augmented C where
  obj f := f.augmentedCechNerve
  map F := Arrow.mapAugmentedCechNerve F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A helper function used in defining the Čech adjunction. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.equivalenceRightToLeft** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SimplicialObject`。
形式化陈述：equivalenceRightToLeft (X : SimplicialObject.Augmented C) (F : Arrow C) (G
 : X ⟶ F.augmentedCechNerve) : Augmented.toArrow.obj X ⟶ F where left
参数：X : SimplicialObject.Augmented C；F : Arrow C；G : X ⟶ F.augmentedCechNerve。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function used in defining the Čech adjunction.
-/
def equivalenceRightToLeft (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : X ⟶ F.augmentedCechNerve) : Augmented.toArrow.obj X ⟶ F where
  left := G.left.app _ ≫ WidePullback.π _ 0
  right := G.right
  w := by
    have := G.w
    apply_fun fun e => e.app (Opposite.op ⦋0⦌) at this
    simpa using this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech adjunction. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.equivalenceLeftToRight** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SimplicialObject`。
形式化陈述：equivalenceLeftToRight (X : SimplicialObject.Augmented C) (F : Arrow C) (G
 : Augmented.toArrow.obj X ⟶ F) : X ⟶ F.augmentedCechNerve where left
参数：X : SimplicialObject.Augmented C；F : Arrow C；G : Augmented.toArrow.obj X ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function used in defining the Čech adjunction.
-/
def equivalenceLeftToRight (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : Augmented.toArrow.obj X ⟶ F) : X ⟶ F.augmentedCechNerve where
  left :=
    { app := fun x =>
        Limits.WidePullback.lift (X.hom.app _ ≫ G.right)
          (fun i => X.left.map (SimplexCategory.const _ x.unop i).op ≫ G.left) fun i => by simp
      naturality := by
        intro x y f
        dsimp
        ext
        · simp only [WidePullback.lift_π, Category.assoc, ← X.left.map_comp_assoc]
          rfl
        · simp }
  right := G.right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech adjunction. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.cechNerveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SimplicialObject`。
形式化陈述：cechNerveEquiv (X : SimplicialObject.Augmented C) (F : Arrow C) : (Augment
ed.toArrow.obj X ⟶ F) ≃ (X ⟶ F.augmentedCechNerve) where toFun
参数：X : SimplicialObject.Augmented C；F : Arrow C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function used in defining the Čech adjunction.
-/
def cechNerveEquiv (X : SimplicialObject.Augmented C) (F : Arrow C) :
    (Augmented.toArrow.obj X ⟶ F) ≃ (X ⟶ F.augmentedCechNerve) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv A := by ext <;> simp
  right_inv := by
    intro A
    ext x : 2
    · refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
      · simp
      · simpa using congr_app A.w.symm x
    · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech nerve construction is right adjoint to the `toArrow` functor. -/
/-
**CategoryTheory.SimplicialObject.cechNerveAdjunction** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.SimplicialObject`。
形式化陈述：cechNerveAdjunction : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmentedCechNer
ve
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech nerve construction is right adjoint to the `toArrow` functor.
-/
abbrev cechNerveAdjunction : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmentedCechNerve :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv
      homEquiv_naturality_left_symm := by dsimp [cechNerveEquiv]; cat_disch
      homEquiv_naturality_right := by
        dsimp [cechNerveEquiv]
        -- The next three lines were not needed before https://github.com/leanprover/lean4/pull/2644
        intro X Y Y' f g
        change equivalenceLeftToRight X Y' (f ≫ g) =
          equivalenceLeftToRight X Y f ≫ augmentedCechNerve.map g
        cat_disch
    }

end SimplicialObject

end CategoryTheory

namespace CategoryTheory.Arrow

variable (f : Arrow C)
variable [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The Čech conerve associated to an arrow. -/
@[simps]
/-
**CategoryTheory.Arrow.cechConerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：cechConerve : CosimplicialObject C where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Čech conerve associated to an arrow.
-/
def cechConerve : CosimplicialObject C where
  obj n := widePushout f.left (fun _ : Fin (n.len + 1) => f.right) fun _ => f.hom
  map {x y} g := by
    refine WidePushout.desc (WidePushout.head _)
      (fun i => (@WidePushout.ι _ _ _ _ _ (fun _ => f.hom) (_) (g.toOrderHom i))) (fun j => ?_)
    rw [← WidePushout.arrow_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism between Čech conerves associated to a morphism of arrows. -/
@[simps]
/-
**CategoryTheory.Arrow.mapCechConerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Arrow`。
形式化陈述：mapCechConerve {f g : Arrow C} [forall n : Nat, HasWidePushout f.left (fun
 _ : Fin (n + 1) => f.right) fun _ => f.hom] [forall n : Nat, HasWidePushout g.l
eft (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) : f.cechConerve
 ⟶ g.cechConerve where app n
参数：fun _ : Fin (n + 1) => f.right；fun _ : Fin (n + 1) => g.right；F : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between Čech conerves associated to a morphism of arrows.
-/
def mapCechConerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [∀ n : ℕ, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.cechConerve ⟶ g.cechConerve where
  app n := WidePushout.desc (F.left ≫ WidePushout.head _)
    (fun i => F.right ≫ (by apply WidePushout.ι _ i))
    (fun i => (by rw [← Arrow.w_assoc F, ← WidePushout.arrow_ι]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech conerve associated to an arrow. -/
@[simps]
/-
**CategoryTheory.Arrow.augmentedCechConerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Arrow`。
形式化陈述：augmentedCechConerve : CosimplicialObject.Augmented C where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech conerve associated to an arrow.
-/
def augmentedCechConerve : CosimplicialObject.Augmented C where
  left := f.left
  right := f.cechConerve
  hom :=
    { app := fun _ => (WidePushout.head _ : f.left ⟶ _) }

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between augmented Čech conerves associated to a morphism of arrows. -/
@[simps]
/-
**CategoryTheory.Arrow.mapAugmentedCechConerve** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Arrow`。
形式化陈述：mapAugmentedCechConerve {f g : Arrow C} [forall n : Nat, HasWidePushout f.
left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom] [forall n : Nat, HasWidePu
shout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) : f.au
gmentedCechConerve ⟶ g.augmentedCechConerve where left
参数：fun _ : Fin (n + 1) => f.right；fun _ : Fin (n + 1) => g.right；F : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between augmented Čech conerves associated to a morphism of arrows.
-/
def mapAugmentedCechConerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    [∀ n : ℕ, HasWidePushout g.left (fun _ : Fin (n + 1) => g.right) fun _ => g.hom] (F : f ⟶ g) :
    f.augmentedCechConerve ⟶ g.augmentedCechConerve where
  left := F.left
  right := mapCechConerve F

end CategoryTheory.Arrow

namespace CategoryTheory

namespace CosimplicialObject

variable
  [∀ (n : ℕ) (f : Arrow C), HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Čech conerve construction, as a functor from `Arrow C`. -/
@[simps]
/-
**CategoryTheory.CosimplicialObject.cechConerve** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.CosimplicialObject`。
形式化陈述：cechConerve : Arrow C ⥤ CosimplicialObject C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Čech conerve construction, as a functor from `Arrow C`.
-/
def cechConerve : Arrow C ⥤ CosimplicialObject C where
  obj f := f.cechConerve
  map F := Arrow.mapCechConerve F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech conerve construction, as a functor from `Arrow C`. -/
@[simps]
/-
**CategoryTheory.CosimplicialObject.augmentedCechConerve** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.CosimplicialObject`。
形式化陈述：augmentedCechConerve : Arrow C ⥤ CosimplicialObject.Augmented C where obj 
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech conerve construction, as a functor from `Arrow C`.
-/
def augmentedCechConerve : Arrow C ⥤ CosimplicialObject.Augmented C where
  obj f := f.augmentedCechConerve
  map F := Arrow.mapAugmentedCechConerve F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.equivalenceLeftToRight** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.CosimplicialObject`。
形式化陈述：equivalenceLeftToRight (F : Arrow C) (X : CosimplicialObject.Augmented C) 
(G : F.augmentedCechConerve ⟶ X) : F ⟶ Augmented.toArrow.obj X
参数：F : Arrow C；X : CosimplicialObject.Augmented C；G : F.augmentedCechConerve ⟶ X
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function used in defining the Čech conerve adjunction.
-/
def equivalenceLeftToRight (F : Arrow C) (X : CosimplicialObject.Augmented C)
    (G : F.augmentedCechConerve ⟶ X) : F ⟶ Augmented.toArrow.obj X :=
  Arrow.homMk G.left (WidePushout.ι _ 0 ≫ G.right.app ⦋0⦌ :) (by
    dsimp
    rw [WidePushout.arrow_ι_assoc (fun (_ : Fin 1) => F.hom)]
    exact congr_app G.w ⦋0⦌)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.equivalenceRightToLeft** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.CosimplicialObject`。
形式化陈述：equivalenceRightToLeft (F : Arrow C) (X : CosimplicialObject.Augmented C) 
(G : F ⟶ Augmented.toArrow.obj X) : F.augmentedCechConerve ⟶ X where left
参数：F : Arrow C；X : CosimplicialObject.Augmented C；G : F ⟶ Augmented.toArrow.obj 
X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function used in defining the Čech conerve adjunction.
-/
def equivalenceRightToLeft (F : Arrow C) (X : CosimplicialObject.Augmented C)
    (G : F ⟶ Augmented.toArrow.obj X) : F.augmentedCechConerve ⟶ X where
  left := G.left
  right :=
    { app := fun x =>
        Limits.WidePushout.desc (G.left ≫ X.hom.app _)
          (fun i => G.right ≫ X.right.map (SimplexCategory.const _ x i))
          (by
            rintro j
            rw [← Arrow.w_assoc G]
            have t := X.hom.naturality (SimplexCategory.const ⦋0⦌ x j)
            dsimp at t ⊢
            simp only [Category.id_comp] at t
            rw [← t])
      naturality := by
        intro x y f
        dsimp
        ext
        · simp only [WidePushout.ι_desc_assoc, WidePushout.ι_desc]
          rw [Category.assoc, ← X.right.map_comp]
          rfl
        · simp [← NatTrans.naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
/-
**CategoryTheory.CosimplicialObject.cechConerveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.CosimplicialObject`。
形式化陈述：cechConerveEquiv (F : Arrow C) (X : CosimplicialObject.Augmented C) : (F.a
ugmentedCechConerve ⟶ X) ≃ (F ⟶ Augmented.toArrow.obj X) where toFun
参数：F : Arrow C；X : CosimplicialObject.Augmented C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function used in defining the Čech conerve adjunction.
-/
def cechConerveEquiv (F : Arrow C) (X : CosimplicialObject.Augmented C) :
    (F.augmentedCechConerve ⟶ X) ≃ (F ⟶ Augmented.toArrow.obj X) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    ext x : 2
    · rfl
    · refine WidePushout.hom_ext _ _ _ (fun j => ?_) ?_
      · dsimp
        simp only [Category.assoc, ← NatTrans.naturality A.right, Arrow.augmentedCechConerve_right,
          SimplexCategory.len_mk, Arrow.cechConerve_map, colimit.ι_desc,
          WidePushoutShape.mkCocone_ι_app, colimit.ι_desc_assoc]
        rfl
      · dsimp
        rw [colimit.ι_desc]
        exact congr_app A.w x
  right_inv := by
    intro A
    ext
    · rfl
    · dsimp
      rw [WidePushout.ι_desc]
      nth_rw 2 [← Category.comp_id A.right]
      congr 1
      convert! X.right.map_id _
      ext ⟨a, ha⟩
      simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmented Čech conerve construction is left adjoint to the `toArrow` functor. -/
/-
**CategoryTheory.CosimplicialObject.cechConerveAdjunction** 是 Mathlib 中的一个缩写定义，位
于命名空间 `CategoryTheory.CosimplicialObject`。
形式化陈述：cechConerveAdjunction : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ Ar
row C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented Čech conerve construction is left adjoint to the `toArrow` functor
.
-/
abbrev cechConerveAdjunction : augmentedCechConerve ⊣ (Augmented.toArrow : _ ⥤ Arrow C) :=
  Adjunction.mkOfHomEquiv { homEquiv := cechConerveEquiv }

end CosimplicialObject

set_option backward.isDefEq.respectTransparency false in
/-- Given an object `X : C`, the natural simplicial object sending `⦋n⦌` to `Xⁿ⁺¹`. -/
/-
**CategoryTheory.cechNerveTerminalFrom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：cechNerveTerminalFrom {C : Type u} [Category.{v} C] [HasFiniteProducts C] 
(X : C) : SimplicialObject C where obj n
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an object `X : C`, the natural simplicial object sending `⦋n⦌` to `Xⁿ⁺¹`.
-/
def cechNerveTerminalFrom {C : Type u} [Category.{v} C] [HasFiniteProducts C] (X : C) :
    SimplicialObject C where
  obj n := ∏ᶜ fun _ : Fin (n.unop.len + 1) => X
  map f := Limits.Pi.lift fun i => Limits.Pi.π _ (f.unop.toOrderHom i)

namespace CechNerveTerminalFrom

variable [HasTerminal C] (ι : Type w)

/-- The diagram `Option ι ⥤ C` sending `none` to the terminal object and `some j` to `X`. -/
@[implicit_reducible]
/-
**CategoryTheory.CechNerveTerminalFrom.wideCospan** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.CechNerveTerminalFrom`。
形式化陈述：wideCospan (X : C) : WidePullbackShape ι ⥤ C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram `Option ι ⥤ C` sending `none` to the terminal object and `some j` to
 `X`.
-/
def wideCospan (X : C) : WidePullbackShape ι ⥤ C :=
  WidePullbackShape.wideCospan (terminal C) (fun _ : ι => X) fun _ => terminal.from X

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CechNerveTerminalFrom.uniqueToWideCospanNone** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.CechNerveTerminalFrom`。
形式化陈述：uniqueToWideCospanNone (X Y : C) : Unique (Y ⟶ (wideCospan ι X).obj none)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueToWideCospanNone (X Y : C) : Unique (Y ⟶ (wideCospan ι X).obj none) := by
  dsimp [wideCospan]
  infer_instance

variable [HasFiniteProducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The product `Xᶥ` is the vertex of a limit cone on `wideCospan ι X`. -/
/-
**CategoryTheory.CechNerveTerminalFrom.wideCospan.limitCone** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.CechNerveTerminalFrom.wideCospan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasTerminal C] →       (ι : Type w) →         [CategoryTh
eory.Limits.HasFiniteProducts C] →           [Finite ι] → (X : C) → CategoryTheo
ry.Limits.LimitCone (CategoryTheory.CechNerveTerminalFrom.wideCospan ι X)
参数：ι : Type w；X : C；CategoryTheory.CechNerveTerminalFrom.wideCospan ι X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product `Xᶥ` is the vertex of a limit cone on `wideCospan ι X`.
-/
def wideCospan.limitCone [Finite ι] (X : C) : LimitCone (wideCospan ι X) where
  cone :=
    { pt := ∏ᶜ fun _ : ι => X
      π :=
        { app := fun X => Option.casesOn X (terminal.from _) fun i => limit.π _ ⟨i⟩
          naturality := fun i j f => by
            cases f
            · cases i
              all_goals simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_map, terminal.comp_from]
              subsingleton } }
  isLimit :=
    { lift := fun s => Limits.Pi.lift fun j => s.π.app (some j)
      fac := fun s j => Option.casesOn j (by subsingleton) fun _ => limit.lift_π _ _
      uniq := fun s f h => by
        dsimp
        ext j
        dsimp only [Limits.Pi.lift]
        rw [limit.lift_π]
        dsimp
        rw [← h (some j)] }
/-
**CategoryTheory.CechNerveTerminalFrom.hasWidePullback** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.CechNerveTerminalFrom`。
形式化陈述：hasWidePullback [Finite ι] (X : C) : HasWidePullback (Arrow.mk (terminal.f
rom X)).right (fun _ : ι => (Arrow.mk (terminal.from X)).left) (fun _ => (Arrow.
mk (terminal.from X)).hom)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
-/
instance hasWidePullback [Finite ι] (X : C) :
    HasWidePullback (Arrow.mk (terminal.from X)).right
      (fun _ : ι => (Arrow.mk (terminal.from X)).left)
      (fun _ => (Arrow.mk (terminal.from X)).hom) := by
  cases nonempty_fintype ι
  exact ⟨⟨wideCospan.limitCone ι X⟩⟩
/-
**CategoryTheory.CechNerveTerminalFrom.hasWidePullback'** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.CechNerveTerminalFrom`。
形式化陈述：hasWidePullback' [Finite ι] (X : C) : HasWidePullback (⊤_ C) (fun _ : ι =>
 X) (fun _ => terminal.from X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasWidePullback' [Finite ι] (X : C) :
    HasWidePullback (⊤_ C)
      (fun _ : ι => X)
      (fun _ => terminal.from X) :=
  hasWidePullback _ _
/-
**CategoryTheory.CechNerveTerminalFrom.hasLimit_wideCospan** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.CechNerveTerminalFrom`。
形式化陈述：hasLimit_wideCospan [Finite ι] (X : C) : HasLimit (wideCospan ι X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimit_wideCospan [Finite ι] (X : C) : HasLimit (wideCospan ι X) := hasWidePullback _ _

/-- the isomorphism to the product induced by the limit cone `wideCospan ι X` -/
/-
**CategoryTheory.CechNerveTerminalFrom.wideCospan.limitIsoPi** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CechNerveTerminalFrom.wideCospan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasTerminal C] →       (ι : Type w) →         [inst_2 : C
ategoryTheory.Limits.HasFiniteProducts C] →           [inst_3 : Finite ι] →     
        (X : C) → CategoryTheory.Limits.limit (CategoryTheory.CechNerveTerminalF
rom.wideCospan ι X) ≅ ∏ᶜ fun x => X
参数：ι : Type w；X : C；CategoryTheory.CechNerveTerminalFrom.wideCospan ι X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the isomorphism to the product induced by the limit cone `wideCospan ι X`
-/
def wideCospan.limitIsoPi [Finite ι] (X : C) :
    limit (wideCospan ι X) ≅ ∏ᶜ fun _ : ι => X :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (wideCospan.limitCone ι X).2)

@[reassoc (attr := simp)]
/-
**CategoryTheory.CechNerveTerminalFrom.wideCospan.limitIsoPi_inv_comp_pi** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.CechNerveTerminalFrom.wideCospan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasTerminal C] (ι : Type w)   [inst_2 : CategoryTheory.Limits.Has
FiniteProducts C] [inst_3 : Finite ι] (X : C) (j : ι),   CategoryTheory.Category
Struct.comp (CategoryTheory.CechNerveTerminalFrom.wideCospan.limitIsoPi ι X).inv
       (CategoryTheory.Limits.WidePullback.π (fun x => CategoryTheory.Limits.ter
minal.from X) j) =     CategoryTheory.Limits.Pi.π (fun x => X) j
参数：ι : Type w；X : C；j : ι；CategoryTheory.CechNerveTerminalFrom.wideCospan.limitI
soPi ι X；CategoryTheory.Limits.WidePullback.π (fun x => CategoryTheory.Limits.te
rminal.from X) j；fun x => X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
lemma wideCospan.limitIsoPi_inv_comp_pi [Finite ι] (X : C) (j : ι) :
    (wideCospan.limitIsoPi ι X).inv ≫ WidePullback.π _ j = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.CechNerveTerminalFrom.wideCospan.limitIsoPi_hom_comp_pi** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.CechNerveTerminalFrom.wideCospan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasTerminal C] (ι : Type w)   [inst_2 : CategoryTheory.Limits.Has
FiniteProducts C] [inst_3 : Finite ι] (X : C) (j : ι),   CategoryTheory.Category
Struct.comp (CategoryTheory.CechNerveTerminalFrom.wideCospan.limitIsoPi ι X).hom
       (CategoryTheory.Limits.Pi.π (fun x => X) j) =     CategoryTheory.Limits.W
idePullback.π (fun x => CategoryTheory.Limits.terminal.from X) j
参数：ι : Type w；X : C；j : ι；CategoryTheory.CechNerveTerminalFrom.wideCospan.limitI
soPi ι X；CategoryTheory.Limits.Pi.π (fun x => X) j；fun x => CategoryTheory.Limit
s.terminal.from X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CechNerveTerminalFrom.wideCospan.limitIsoPi_inv_comp_pi`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.Limits.HasTerminal C] (ι : Type w)   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma wideCospan.limitIsoPi_hom_comp_pi [Finite ι] (X : C) (j : ι) :
    (wideCospan.limitIsoPi ι X).hom ≫ Pi.π _ j = WidePullback.π _ j := by
  rw [← wideCospan.limitIsoPi_inv_comp_pi, Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an object `X : C`, the Čech nerve of the hom to the terminal object `X ⟶ ⊤_ C` is
naturally isomorphic to a simplicial object sending `⦋n⦌` to `Xⁿ⁺¹` (when `C` is `G-Set`, this is
`EG`, the universal cover of the classifying space of `G`). -/
/-
**CategoryTheory.CechNerveTerminalFrom.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.CechNerveTerminalFrom`。
形式化陈述：iso (X : C) : (Arrow.mk (terminal.from X)).cechNerve ≅ cechNerveTerminalFr
om X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an object `X : C`, the Čech nerve of the hom to the terminal object `X ⟶ ⊤
_ C` is
naturally isomorphic to a simplicial object sending `⦋n⦌` to `Xⁿ⁺¹` (when `C` is
 `G-Set`, this is
`EG`, the universal cover of the classifying space of `G`).
-/
def iso (X : C) : (Arrow.mk (terminal.from X)).cechNerve ≅ cechNerveTerminalFrom X :=
  NatIso.ofComponents (fun _ => wideCospan.limitIsoPi _ _) (fun {m n} f => by
    dsimp only [cechNerveTerminalFrom, Arrow.cechNerve]
    ext ⟨j⟩
    simp)

end CechNerveTerminalFrom

end CategoryTheory

