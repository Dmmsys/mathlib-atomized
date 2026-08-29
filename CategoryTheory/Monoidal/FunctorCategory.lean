/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace Monoidal

namespace FunctorCategory

variable (F G F' G' : C ⥤ D)

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
-/
@[simps]
/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
definition tensorObj
  signature: : C ⥤ D where
  body: F.obj X otimes G.obj X
  map f := F.map f otimesₘ G.map f

中文:
定义 tensorObj
  签名: : C ⥤ D where
  定义体: F.obj X otimes G.obj X
  map f := F.map f otimesₘ G.map f

Depends on / 依赖: E.mem, F.obj, G.obj, equivShrink, otimes
-/
def tensorObj : C ⥤ D where
  obj X := F.obj X otimes G.obj X
  map f := F.map f otimesₘ G.map f

variable {F G F' G'}
variable (α : F ⟶ G) (β : F' ⟶ G')

set_option backward.defeqAttrib.useBackward true in
/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
@[simps]
/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: : tensorObj F F' ⟶ tensorObj G G' where
  body: α.app X otimesₘ β.app X
  naturality X Y f := by
    dsimp; rw [tensorHom_comp_tensorHom, α.naturality, β.naturality, ← tensorHom_comp_tensorHom]

中文:
定义 tensorHom
  签名: : tensorObj F F' ⟶ tensorObj G G' where
  定义体: α.app X otimesₘ β.app X
  naturality X Y f := by
    dsimp; rw [tensorHom_comp_tensorHom, α.naturality, β.naturality, ← tensorHom_comp_tensorHom]
-/
def tensorHom : tensorObj F F' ⟶ tensorObj G G' where
  app X := α.app X otimesₘ β.app X
  naturality X Y f := by
    dsimp; rw [tensorHom_comp_tensorHom, α.naturality, β.naturality, ← tensorHom_comp_tensorHom]

/-- (An auxiliary definition for `functorCategoryMonoidal`.) -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (F) (β : F' ⟶ G')
  body: F.obj X ◁ β.app X
  naturality X Y f := by
    simp only [← id_tensorHom]
    apply (tensorHom (𝟙 F) β).naturality

中文:
定义 whiskerLeft
  签名: (F) (β : F' ⟶ G')
  定义体: F.obj X ◁ β.app X
  naturality X Y f := by
    simp only [← id_tensorHom]
    apply (tensorHom (𝟙 F) β).naturality

Depends on / 依赖: F.obj
-/
def whiskerLeft (F) (β : F' ⟶ G') : tensorObj F F' ⟶ tensorObj F G' where
  app X := F.obj X ◁ β.app X
  naturality X Y f := by
    simp only [← id_tensorHom]
    apply (tensorHom (𝟙 F) β).naturality

/-- (An auxiliary definition for `functorCategoryMonoidal`.) -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: (F')
  body: α.app X ▷ F'.obj X
  naturality X Y f := by
    simp only [← tensorHom_id]
    apply (tensorHom α (𝟙 F')).naturality

中文:
定义 whiskerRight
  签名: (F')
  定义体: α.app X ▷ F'.obj X
  naturality X Y f := by
    simp only [← tensorHom_id]
    apply (tensorHom α (𝟙 F')).naturality
-/
def whiskerRight (F') : tensorObj F F' ⟶ tensorObj G F' where
  app X := α.app X ▷ F'.obj X
  naturality X Y f := by
    simp only [← tensorHom_id]
    apply (tensorHom α (𝟙 F')).naturality

end FunctorCategory

open CategoryTheory.Monoidal.FunctorCategory

set_option backward.defeqAttrib.useBackward true in
/--
Instance `functorCategoryMonoidalStruct` / 实例 `functorCategoryMonoidalStruct`

English:
instance functorCategoryMonoidalStruct
  signature: : MonoidalCategoryStruct (C ⥤ D) where
  body: tensorObj F G
  tensorHom α β := tensorHom α β
  whiskerLeft F _ _ α := FunctorCategory.whiskerLeft F α
  whiskerRight α F := FunctorCategory.whiskerRight α F
  tensorUnit := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor F := NatIso.ofComponents fun X => fun_ (F.obj X)
  rightUnitor F := NatIso.ofComponents fun X => ρ_ (F.obj X)
  associator F G H := NatIso.ofComponents fun X => α_ (F.obj X) (G.obj X) (H.obj X)

@[simp]

中文:
实例 functorCategoryMonoidalStruct
  签名: : 幺半群范畴结构 (C ⥤ D) where
  定义体: tensorObj F G
  tensorHom α β := tensorHom α β
  whiskerLeft F _ _ α := FunctorCategory.whiskerLeft F α
  whiskerRight α F := FunctorCategory.whiskerRight α F
  tensorUnit := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor F := NatIso.ofComponents fun X => fun_ (F.obj X)
  rightUnitor F := NatIso.ofComponents fun X => ρ_ (F.obj X)
  associator F G H := NatIso.ofComponents fun X => α_ (F.obj X) (G.obj X) (H.obj X)

@[simp]

Depends on / 依赖: E.mem, E.presieve, Presieve, Presieve.ofArrows, convert, eqToHom, exists_eq_ofArrows, le_antisymm, ofArrows, tensorObj
-/
instance functorCategoryMonoidalStruct : MonoidalCategoryStruct (C ⥤ D) where
  tensorObj F G := tensorObj F G
  tensorHom α β := tensorHom α β
  whiskerLeft F _ _ α := FunctorCategory.whiskerLeft F α
  whiskerRight α F := FunctorCategory.whiskerRight α F
  tensorUnit := (CategoryTheory.Functor.const C).obj (𝟙_ D)
  leftUnitor F := NatIso.ofComponents fun X => fun_ (F.obj X)
  rightUnitor F := NatIso.ofComponents fun X => ρ_ (F.obj X)
  associator F G H := NatIso.ofComponents fun X => α_ (F.obj X) (G.obj X) (H.obj X)

@[simp]
/--
theorem `tensorUnit_obj` / 定理 `tensorUnit_obj`

English:
theorem tensorUnit_obj
  given: {X}
  statement: (𝟙_ (C ⥤ D)).obj X = 𝟙_ D
  proof: rfl

@[simp]

中文:
定理 tensorUnit_obj
  条件: {X}
  结论: (𝟙_ (C ⥤ D)).obj X = 𝟙_ D
  证明: rfl

@[simp]
-/
theorem tensorUnit_obj {X} : (𝟙_ (C ⥤ D)).obj X = 𝟙_ D :=
  rfl

@[simp]
/--
theorem `tensorUnit_map` / 定理 `tensorUnit_map`

English:
theorem tensorUnit_map
  given: {X Y} {f : X ⟶ Y}
  statement: (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D)
  proof: rfl

@[simp]

中文:
定理 tensorUnit_map
  条件: {X Y} {f : X ⟶ Y}
  结论: (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D)
  证明: rfl

@[simp]

Depends on / 依赖: E.restrictIndexOfSmall.f, HasPullback, Small.Index, Small.restrictFun, infer_instance, restrictFun, restrictIndexOfSmall
-/
theorem tensorUnit_map {X Y} {f : X ⟶ Y} : (𝟙_ (C ⥤ D)).map f = 𝟙 (𝟙_ D) :=
  rfl

@[simp]
/--
theorem `tensorObj_obj` / 定理 `tensorObj_obj`

English:
theorem tensorObj_obj
  given: {F G : C ⥤ D} {X}
  statement: (F otimes G).obj X = F.obj X otimes G.obj X
  proof: rfl

@[simp]

中文:
定理 tensorObj_obj
  条件: {F G : C ⥤ D} {X}
  结论: (F otimes G).obj X = F.obj X otimes G.obj X
  证明: rfl

@[simp]
-/
theorem tensorObj_obj {F G : C ⥤ D} {X} : (F otimes G).obj X = F.obj X otimes G.obj X :=
  rfl

@[simp]
/--
theorem `tensorObj_map` / 定理 `tensorObj_map`

English:
theorem tensorObj_map
  given: {F G : C ⥤ D} {X Y} {f : X ⟶ Y}
  statement: (F otimes G).map f = F.map f otimesₘ G.map f
  proof: rfl

@[simp]

中文:
定理 tensorObj_map
  条件: {F G : C ⥤ D} {X Y} {f : X ⟶ Y}
  结论: (F otimes G).map f = F.map f otimesₘ G.map f
  证明: rfl

@[simp]
-/
theorem tensorObj_map {F G : C ⥤ D} {X Y} {f : X ⟶ Y} : (F otimes G).map f = F.map f otimesₘ G.map f :=
  rfl

@[simp]
/--
theorem `tensorHom_app` / 定理 `tensorHom_app`

English:
theorem tensorHom_app
  given: {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X}
  proof: rfl

@[simp]

中文:
定理 tensorHom_app
  条件: {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X}
  证明: rfl

@[simp]
-/
theorem tensorHom_app {F G F' G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X} :
    (α otimesₘ β).app X = α.app X otimesₘ β.app X :=
  rfl

@[simp]
/--
theorem `whiskerLeft_app` / 定理 `whiskerLeft_app`

English:
theorem whiskerLeft_app
  given: {F F' G' : C ⥤ D} {β : F' ⟶ G'} {X}
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_app
  条件: {F F' G' : C ⥤ D} {β : F' ⟶ G'} {X}
  证明: rfl

@[simp]

Depends on / 依赖: Small.zeroHypercoverSmall, ZeroHypercover, ZeroHypercover.Small, ZeroHypercover.Small.restrictFun, ZeroHypercover.restrictIndexOfSmall, restrictFun, restrictIndexOfSmall, zeroHypercoverSmall
-/
theorem whiskerLeft_app {F F' G' : C ⥤ D} {β : F' ⟶ G'} {X} :
    (F ◁ β).app X = F.obj X ◁ β.app X :=
  rfl

@[simp]
/--
theorem `whiskerRight_app` / 定理 `whiskerRight_app`

English:
theorem whiskerRight_app
  given: {F G F' : C ⥤ D} {α : F ⟶ G} {X}
  proof: rfl

@[simp]

中文:
定理 whiskerRight_app
  条件: {F G F' : C ⥤ D} {α : F ⟶ G} {X}
  证明: rfl

@[simp]

Depends on / 依赖: E.map, ZeroHypercover, ZeroHypercover.Small.restrictFun, le_rfl, restrictFun, restrictIndexOfSmall, restrictIndexOfSmall.I, restrictIndexOfSmall.mem
-/
theorem whiskerRight_app {F G F' : C ⥤ D} {α : F ⟶ G} {X} :
    (α ▷ F').app X = α.app X ▷ F'.obj X :=
  rfl

@[simp]
/--
theorem `leftUnitor_hom_app` / 定理 `leftUnitor_hom_app`

English:
theorem leftUnitor_hom_app
  given: {F : C ⥤ D} {X}
  proof: rfl

@[simp]

中文:
定理 leftUnitor_hom_app
  条件: {F : C ⥤ D} {X}
  证明: rfl

@[simp]
-/
theorem leftUnitor_hom_app {F : C ⥤ D} {X} :
    ((fun_ F).hom : 𝟙_ _ otimes F ⟶ F).app X = (fun_ (F.obj X)).hom :=
  rfl

@[simp]
/--
theorem `leftUnitor_inv_app` / 定理 `leftUnitor_inv_app`

English:
theorem leftUnitor_inv_app
  given: {F : C ⥤ D} {X}
  proof: rfl

@[simp]

中文:
定理 leftUnitor_inv_app
  条件: {F : C ⥤ D} {X}
  证明: rfl

@[simp]
-/
theorem leftUnitor_inv_app {F : C ⥤ D} {X} :
    ((fun_ F).inv : F ⟶ 𝟙_ _ otimes F).app X = (fun_ (F.obj X)).inv :=
  rfl

@[simp]
/--
theorem `rightUnitor_hom_app` / 定理 `rightUnitor_hom_app`

English:
theorem rightUnitor_hom_app
  given: {F : C ⥤ D} {X}
  proof: rfl

@[simp]

中文:
定理 rightUnitor_hom_app
  条件: {F : C ⥤ D} {X}
  证明: rfl

@[simp]
-/
theorem rightUnitor_hom_app {F : C ⥤ D} {X} :
    ((ρ_ F).hom : F otimes 𝟙_ _ ⟶ F).app X = (ρ_ (F.obj X)).hom :=
  rfl

@[simp]
/--
theorem `rightUnitor_inv_app` / 定理 `rightUnitor_inv_app`

English:
theorem rightUnitor_inv_app
  given: {F : C ⥤ D} {X}
  proof: rfl

@[simp]

中文:
定理 rightUnitor_inv_app
  条件: {F : C ⥤ D} {X}
  证明: rfl

@[simp]
-/
theorem rightUnitor_inv_app {F : C ⥤ D} {X} :
    ((ρ_ F).inv : F ⟶ F otimes 𝟙_ _).app X = (ρ_ (F.obj X)).inv :=
  rfl

@[simp]
/--
theorem `associator_hom_app` / 定理 `associator_hom_app`

English:
theorem associator_hom_app
  given: {F G H : C ⥤ D} {X}
  proof: rfl

@[simp]

中文:
定理 associator_hom_app
  条件: {F G H : C ⥤ D} {X}
  证明: rfl

@[simp]
-/
theorem associator_hom_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).hom : (F otimes G) otimes H ⟶ F otimes G otimes H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).hom :=
  rfl

@[simp]
/--
theorem `associator_inv_app` / 定理 `associator_inv_app`

English:
theorem associator_inv_app
  given: {F G H : C ⥤ D} {X}
  proof: rfl

中文:
定理 associator_inv_app
  条件: {F G H : C ⥤ D} {X}
  证明: rfl
-/
theorem associator_inv_app {F G H : C ⥤ D} {X} :
    ((α_ F G H).inv : F otimes G otimes H ⟶ (F otimes G) otimes H).app X = (α_ (F.obj X) (G.obj X) (H.obj X)).inv :=
  rfl

/--
Instance `functorCategoryMonoidal` / 实例 `functorCategoryMonoidal`

English:
instance functorCategoryMonoidal
  signature: : MonoidalCategory (C ⥤ D) where
  body: by intros; ext; simp [tensorHom_def]
  pentagon F G H K := by ext X; dsimp; rw [pentagon]

中文:
实例 functorCategoryMonoidal
  签名: : 幺半群范畴 (C ⥤ D) where
  定义体: by intros; ext; simp [tensorHom_def]
  pentagon F G H K := by ext X; dsimp; rw [pentagon]

Depends on / 依赖: intros, pentagon, tensorHom_def
-/
instance functorCategoryMonoidal : MonoidalCategory (C ⥤ D) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  pentagon F G H K := by ext X; dsimp; rw [pentagon]

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [BraidedCategory.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `functorCategoryBraided` / 实例 `functorCategoryBraided`

English:
instance functorCategoryBraided
  signature: : BraidedCategory (C ⥤ D) where
  body: NatIso.ofComponents fun _ => β_ _ _
  hexagon_forward F G H := by ext X; apply hexagon_forward
  hexagon_reverse F G H := by ext X; apply hexagon_reverse

中文:
实例 functorCategoryBraided
  签名: : 辫范畴 (C ⥤ D) where
  定义体: NatIso.ofComponents fun _ => β_ _ _
  hexagon_forward F G H := by ext X; apply hexagon_forward
  hexagon_reverse F G H := by ext X; apply hexagon_reverse

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
instance functorCategoryBraided : BraidedCategory (C ⥤ D) where
  braiding F G := NatIso.ofComponents fun _ => β_ _ _
  hexagon_forward F G H := by ext X; apply hexagon_forward
  hexagon_reverse F G H := by ext X; apply hexagon_reverse

set_option backward.isDefEq.respectTransparency.types false in
example : BraidedCategory (C ⥤ D) :=
  CategoryTheory.Monoidal.functorCategoryBraided

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [SymmetricCategory.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `functorCategorySymmetric` / 实例 `functorCategorySymmetric`

English:
instance functorCategorySymmetric
  signature: : SymmetricCategory (C ⥤ D) where
  body: by ext X; apply symmetry

中文:
实例 functorCategorySymmetric
  签名: : 对称范畴 (C ⥤ D) where
  定义体: by ext X; apply symmetry

Depends on / 依赖: symmetry
-/
instance functorCategorySymmetric : SymmetricCategory (C ⥤ D) where
  symmetry F G := by ext X; apply symmetry

end SymmetricCategory

end Monoidal

set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `Functor.LaxMonoidal.whiskeringRight` / 实例 `Functor.LaxMonoidal.whiskeringRight`

English:
instance Functor.LaxMonoidal.whiskeringRight
  body: { app X := Functor.LaxMonoidal.ε L }
  μ F G := { app X := Functor.LaxMonoidal.μ L (F.obj X) (G.obj X) }

中文:
实例 函子.松弛幺半群.whiskeringRight
  定义体: { app X := Functor.LaxMonoidal.ε L }
  μ F G := { app X := Functor.LaxMonoidal.μ L (F.obj X) (G.obj X) }

Depends on / 依赖: Functor, Functor.LaxMonoidal, LaxMonoidal
-/
instance Functor.LaxMonoidal.whiskeringRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.LaxMonoidal] :
    ((Functor.whiskeringRight C D E).obj L).LaxMonoidal where
  ε := { app X := Functor.LaxMonoidal.ε L }
  μ F G := { app X := Functor.LaxMonoidal.μ L (F.obj X) (G.obj X) }

set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `Functor.OplaxMonoidal.whiskeringRight` / 实例 `Functor.OplaxMonoidal.whiskeringRight`

English:
instance Functor.OplaxMonoidal.whiskeringRight
  body: { app X := Functor.OplaxMonoidal.η L }
  δ F G := { app X := Functor.OplaxMonoidal.δ L (F.obj X) (G.obj X) }
  oplax_left_unitality := by aesop
  oplax_right_unitality := by aesop

中文:
实例 函子.反松弛幺半群.whiskeringRight
  定义体: { app X := Functor.OplaxMonoidal.η L }
  δ F G := { app X := Functor.OplaxMonoidal.δ L (F.obj X) (G.obj X) }
  oplax_left_unitality := by aesop
  oplax_right_unitality := by aesop

Depends on / 依赖: Functor, Functor.OplaxMonoidal, OplaxMonoidal
-/
instance Functor.OplaxMonoidal.whiskeringRight
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.OplaxMonoidal] :
    ((Functor.whiskeringRight C D E).obj L).OplaxMonoidal where
  η := { app X := Functor.OplaxMonoidal.η L }
  δ F G := { app X := Functor.OplaxMonoidal.δ L (F.obj X) (G.obj X) }
  oplax_left_unitality := by aesop
  oplax_right_unitality := by aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.Monoidal] :
    ((Functor.whiskeringRight C D E).obj L).Monoidal where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
/--
Instance `Functor.Monoidal.whiskeringLeft` / 实例 `Functor.Monoidal.whiskeringLeft`

English:
instance Functor.Monoidal.whiskeringLeft
  body: CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

中文:
实例 函子.幺半群.whiskeringLeft
  定义体: CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

Depends on / 依赖: CoreMonoidal, CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance Functor.Monoidal.whiskeringLeft
    (E : Type*) [Category* E] [MonoidalCategory E] (F : C ⥤ D) :
    ((whiskeringLeft _ _ E).obj F).Monoidal :=
  CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).functor.Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ E).obj e.inverse).Monoidal

instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).inverse.Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ E).obj e.functor).Monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (E : Type*) [Category* E] [MonoidalCategory E] (e : C ≌ D) :
    (e.congrLeft (E := E)).IsMonoidal where
  leftAdjoint_μ X Y := by
    ext
    simp [← Functor.map_comp]

end CategoryTheory
