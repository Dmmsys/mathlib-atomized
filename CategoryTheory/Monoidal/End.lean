/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v u

namespace CategoryTheory

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

variable (C : Type u) [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
/-- The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).

Note: due to the fact that composition of functors in mathlib is reversed compared to the
one usually found in the literature, this monoidal structure is in fact the monoidal
opposite of the one usually considered in the literature.
-/
@[instance_reducible]
/--
Definition of `endofunctorMonoidalCategory` / `endofunctorMonoidalCategory` 的定义

English:
definition endofunctorMonoidalCategory
  signature: : MonoidalCategory (C ⥤ C) where
  body: F ⋙ G
  whiskerLeft X _ _ F := Functor.whiskerLeft X F
  whiskerRight F X := Functor.whiskerRight F X
  tensorHom α β := α ◫ β
  tensorUnit := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F

中文:
定义 endofunctorMonoidalCategory
  签名: : 幺半群范畴 (C ⥤ C) where
  定义体: F ⋙ G
  whiskerLeft X _ _ F := Functor.whiskerLeft X F
  whiskerRight F X := Functor.whiskerRight F X
  tensorHom α β := α ◫ β
  tensorUnit := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F
-/
def endofunctorMonoidalCategory : MonoidalCategory (C ⥤ C) where
  tensorObj F G := F ⋙ G
  whiskerLeft X _ _ F := Functor.whiskerLeft X F
  whiskerRight F X := Functor.whiskerRight F X
  tensorHom α β := α ◫ β
  tensorUnit := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F

open CategoryTheory.MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory

/--
theorem `endofunctorMonoidalCategory_tensorUnit_obj` / 定理 `endofunctorMonoidalCategory_tensorUnit_obj`

English:
theorem endofunctorMonoidalCategory_tensorUnit_obj
  given: (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_tensorUnit_obj
  条件: (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_tensorUnit_obj (X : C) :
    (𝟙_ (C ⥤ C)).obj X = X := rfl

/--
theorem `endofunctorMonoidalCategory_tensorUnit_map` / 定理 `endofunctorMonoidalCategory_tensorUnit_map`

English:
theorem endofunctorMonoidalCategory_tensorUnit_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_tensorUnit_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_tensorUnit_map {X Y : C} (f : X ⟶ Y) :
    (𝟙_ (C ⥤ C)).map f = f := rfl

/--
theorem `endofunctorMonoidalCategory_tensorObj_obj` / 定理 `endofunctorMonoidalCategory_tensorObj_obj`

English:
theorem endofunctorMonoidalCategory_tensorObj_obj
  given: (F G : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_tensorObj_obj
  条件: (F G : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_tensorObj_obj (F G : C ⥤ C) (X : C) :
    (F otimes G).obj X = G.obj (F.obj X) := rfl

/--
theorem `endofunctorMonoidalCategory_tensorObj_map` / 定理 `endofunctorMonoidalCategory_tensorObj_map`

English:
theorem endofunctorMonoidalCategory_tensorObj_map
  given: (F G : C ⥤ C) {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_tensorObj_map
  条件: (F G : C ⥤ C) {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_tensorObj_map (F G : C ⥤ C) {X Y : C} (f : X ⟶ Y) :
    (F otimes G).map f = G.map (F.map f) := rfl

/--
theorem `endofunctorMonoidalCategory_tensorMap_app` / 定理 `endofunctorMonoidalCategory_tensorMap_app`

English:
theorem endofunctorMonoidalCategory_tensorMap_app
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_tensorMap_app
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_tensorMap_app
    {F G H K : C ⥤ C} {α : F ⟶ G} {β : H ⟶ K} (X : C) :
    (α otimesₘ β).app X = β.app (F.obj X) ≫ K.map (α.app X) := rfl

/--
theorem `endofunctorMonoidalCategory_whiskerLeft_app` / 定理 `endofunctorMonoidalCategory_whiskerLeft_app`

English:
theorem endofunctorMonoidalCategory_whiskerLeft_app
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_whiskerLeft_app
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_whiskerLeft_app
    {F H K : C ⥤ C} {β : H ⟶ K} (X : C) :
    (F ◁ β).app X = β.app (F.obj X) := rfl

/--
theorem `endofunctorMonoidalCategory_whiskerRight_app` / 定理 `endofunctorMonoidalCategory_whiskerRight_app`

English:
theorem endofunctorMonoidalCategory_whiskerRight_app
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_whiskerRight_app
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_whiskerRight_app
    {F G H : C ⥤ C} {α : F ⟶ G} (X : C) :
    (α ▷ H).app X = H.map (α.app X) := rfl

/--
theorem `endofunctorMonoidalCategory_associator_hom_app` / 定理 `endofunctorMonoidalCategory_associator_hom_app`

English:
theorem endofunctorMonoidalCategory_associator_hom_app
  given: (F G H : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_associator_hom_app
  条件: (F G H : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_associator_hom_app (F G H : C ⥤ C) (X : C) :
    (α_ F G H).hom.app X = 𝟙 _ := rfl

/--
theorem `endofunctorMonoidalCategory_associator_inv_app` / 定理 `endofunctorMonoidalCategory_associator_inv_app`

English:
theorem endofunctorMonoidalCategory_associator_inv_app
  given: (F G H : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_associator_inv_app
  条件: (F G H : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_associator_inv_app (F G H : C ⥤ C) (X : C) :
    (α_ F G H).inv.app X = 𝟙 _ := rfl

/--
theorem `endofunctorMonoidalCategory_leftUnitor_hom_app` / 定理 `endofunctorMonoidalCategory_leftUnitor_hom_app`

English:
theorem endofunctorMonoidalCategory_leftUnitor_hom_app
  given: (F : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_leftUnitor_hom_app
  条件: (F : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_leftUnitor_hom_app (F : C ⥤ C) (X : C) :
    (fun_ F).hom.app X = 𝟙 _ := rfl

/--
theorem `endofunctorMonoidalCategory_leftUnitor_inv_app` / 定理 `endofunctorMonoidalCategory_leftUnitor_inv_app`

English:
theorem endofunctorMonoidalCategory_leftUnitor_inv_app
  given: (F : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_leftUnitor_inv_app
  条件: (F : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_leftUnitor_inv_app (F : C ⥤ C) (X : C) :
    (fun_ F).inv.app X = 𝟙 _ := rfl

/--
theorem `endofunctorMonoidalCategory_rightUnitor_hom_app` / 定理 `endofunctorMonoidalCategory_rightUnitor_hom_app`

English:
theorem endofunctorMonoidalCategory_rightUnitor_hom_app
  given: (F : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_rightUnitor_hom_app
  条件: (F : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_rightUnitor_hom_app (F : C ⥤ C) (X : C) :
    (ρ_ F).hom.app X = 𝟙 _ := rfl

/--
theorem `endofunctorMonoidalCategory_rightUnitor_inv_app` / 定理 `endofunctorMonoidalCategory_rightUnitor_inv_app`

English:
theorem endofunctorMonoidalCategory_rightUnitor_inv_app
  given: (F : C ⥤ C) (X : C)
  proof: rfl

中文:
定理 endofunctorMonoidalCategory_rightUnitor_inv_app
  条件: (F : C ⥤ C) (X : C)
  证明: rfl
-/
@[simp] theorem endofunctorMonoidalCategory_rightUnitor_inv_app (F : C ⥤ C) (X : C) :
    (ρ_ F).inv.app X = 𝟙 _ := rfl

namespace MonoidalCategory

variable [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tensoringRight C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := (rightUnitorNatIso C).symm
      μIso := fun X Y => (Functor.isoWhiskerRight (curriedAssociatorNatIso C)
      ((evaluation C (C ⥤ C)).obj X ⋙ (evaluation C C).obj Y)) }

中文:
实例 :
  签名: (tensoringRight C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := (rightUnitorNatIso C).symm
      μIso := fun X Y => (Functor.isoWhiskerRight (curriedAssociatorNatIso C)
      ((evaluation C (C ⥤ C)).obj X ⋙ (evaluation C C).obj Y)) }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Functor.isoWhiskerRight, curriedAssociatorNatIso, evaluation, isoWhiskerRight, rightUnitorNatIso, toMonoidal
-/
instance : (tensoringRight C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (rightUnitorNatIso C).symm
      μIso := fun X Y => (Functor.isoWhiskerRight (curriedAssociatorNatIso C)
      ((evaluation C (C ⥤ C)).obj X ⋙ (evaluation C C).obj Y)) }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensoringRight_ε` / 引理 `tensoringRight_ε`

English:
lemma tensoringRight_ε
  proof: rfl

中文:
引理 tensoringRight_ε
  证明: rfl
-/
@[simp] lemma tensoringRight_ε :
    ε (tensoringRight C) = (rightUnitorNatIso C).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensoringRight_η` / 引理 `tensoringRight_η`

English:
lemma tensoringRight_η
  proof: rfl

中文:
引理 tensoringRight_η
  证明: rfl
-/
@[simp] lemma tensoringRight_η :
    η (tensoringRight C) = (rightUnitorNatIso C).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensoringRight_μ` / 引理 `tensoringRight_μ`

English:
lemma tensoringRight_μ
  given: (X Y : C) (Z : C)
  proof: rfl

中文:
引理 tensoringRight_μ
  条件: (X Y : C) (Z : C)
  证明: rfl
-/
@[simp] lemma tensoringRight_μ (X Y : C) (Z : C) :
    (μ (tensoringRight C) X Y).app Z = (α_ Z X Y).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensoringRight_δ` / 引理 `tensoringRight_δ`

English:
lemma tensoringRight_δ
  given: (X Y : C) (Z : C)
  proof: rfl

中文:
引理 tensoringRight_δ
  条件: (X Y : C) (Z : C)
  证明: rfl
-/
@[simp] lemma tensoringRight_δ (X Y : C) (Z : C) :
    (δ (tensoringRight C) X Y).app Z = (α_ Z X Y).inv := rfl

end MonoidalCategory

variable {C}
variable {M : Type*} [Category* M] [MonoidalCategory M] (F : M ⥤ (C ⥤ C))

@[reassoc (attr := simp)]
/--
theorem `μ_δ_app` / 定理 `μ_δ_app`

English:
theorem μ_δ_app
  given: (i j : M) (X : C) [F.Monoidal]
  proof: (μIso F i j).hom_inv_id_app X

@[reassoc (attr := simp)]

中文:
定理 μ_δ_app
  条件: (i j : M) (X : C) [F.幺半群]
  证明: (μIso F i j).hom_inv_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id_app
-/
theorem μ_δ_app (i j : M) (X : C) [F.Monoidal] :
    (μ F i j).app X ≫ (δ F i j).app X = 𝟙 _ :=
  (μIso F i j).hom_inv_id_app X

@[reassoc (attr := simp)]
/--
theorem `δ_μ_app` / 定理 `δ_μ_app`

English:
theorem δ_μ_app
  given: (i j : M) (X : C) [F.Monoidal]
  proof: (μIso F i j).inv_hom_id_app X

@[reassoc (attr := simp)]

中文:
定理 δ_μ_app
  条件: (i j : M) (X : C) [F.幺半群]
  证明: (μIso F i j).inv_hom_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: inv_hom_id_app
-/
theorem δ_μ_app (i j : M) (X : C) [F.Monoidal] :
    (δ F i j).app X ≫ (μ F i j).app X = 𝟙 _ :=
  (μIso F i j).inv_hom_id_app X

@[reassoc (attr := simp)]
/--
theorem `ε_η_app` / 定理 `ε_η_app`

English:
theorem ε_η_app
  given: (X : C) [F.Monoidal]
  statement: (ε F).app X ≫ (η F).app X = 𝟙 _
  proof: (εIso F).hom_inv_id_app X

@[reassoc (attr := simp)]

中文:
定理 ε_η_app
  条件: (X : C) [F.幺半群]
  结论: (ε F).app X ≫ (η F).app X = 𝟙 _
  证明: (εIso F).hom_inv_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id_app
-/
theorem ε_η_app (X : C) [F.Monoidal] : (ε F).app X ≫ (η F).app X = 𝟙 _ :=
  (εIso F).hom_inv_id_app X

@[reassoc (attr := simp)]
/--
theorem `η_ε_app` / 定理 `η_ε_app`

English:
theorem η_ε_app
  given: (X : C) [F.Monoidal]
  statement: (η F).app X ≫ (ε F).app X = 𝟙 _
  proof: (εIso F).inv_hom_id_app X

@[reassoc (attr := simp)]

中文:
定理 η_ε_app
  条件: (X : C) [F.幺半群]
  结论: (η F).app X ≫ (ε F).app X = 𝟙 _
  证明: (εIso F).inv_hom_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: inv_hom_id_app
-/
theorem η_ε_app (X : C) [F.Monoidal] : (η F).app X ≫ (ε F).app X = 𝟙 _ :=
  (εIso F).inv_hom_id_app X

@[reassoc (attr := simp)]
/--
theorem `ε_naturality` / 定理 `ε_naturality`

English:
theorem ε_naturality
  given: {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal]
  proof: ((ε F).naturality f).symm

@[reassoc (attr := simp)]

中文:
定理 ε_naturality
  条件: {X Y : C} (f : X ⟶ Y) [F.松弛幺半群]
  证明: ((ε F).naturality f).symm

@[reassoc (attr := simp)]

Depends on / 依赖: naturality
-/
theorem ε_naturality {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal] :
    (ε F).app X ≫ (F.obj (𝟙_ M)).map f = f ≫ (ε F).app Y :=
  ((ε F).naturality f).symm

@[reassoc (attr := simp)]
/--
theorem `η_naturality` / 定理 `η_naturality`

English:
theorem η_naturality
  given: {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal]
  proof: by
  simp

@[reassoc (attr := simp)]

中文:
定理 η_naturality
  条件: {X Y : C} (f : X ⟶ Y) [F.反松弛幺半群]
  证明: by
  simp

@[reassoc (attr := simp)]
-/
theorem η_naturality {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal] :
    (η F).app X ≫ (𝟙_ (C ⥤ C)).map f = (η F).app X ≫ f := by
  simp

@[reassoc (attr := simp)]
/--
theorem `μ_naturality` / 定理 `μ_naturality`

English:
theorem μ_naturality
  given: {m n : M} {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal]
  proof: (μ F m n).naturality f

中文:
定理 μ_naturality
  条件: {m n : M} {X Y : C} (f : X ⟶ Y) [F.松弛幺半群]
  证明: (μ F m n).naturality f

Depends on / 依赖: naturality
-/
theorem μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) [F.LaxMonoidal] :
    (F.obj n).map ((F.obj m).map f) ≫ (μ F m n).app Y = (μ F m n).app X ≫ (F.obj _).map f :=
  (μ F m n).naturality f

-- This is a simp lemma in the reverse direction via `NatTrans.naturality`.
@[reassoc]
/--
theorem `δ_naturality` / 定理 `δ_naturality`

English:
theorem δ_naturality
  given: {m n : M} {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal]
  proof: by simp

中文:
定理 δ_naturality
  条件: {m n : M} {X Y : C} (f : X ⟶ Y) [F.反松弛幺半群]
  证明: by simp
-/
theorem δ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.obj n).map ((F.obj m).map f) =
      (F.obj _).map f ≫ (δ F m n).app Y := by simp

-- This is not a simp lemma since it could be proved by the lemmas later.
@[reassoc]
/--
theorem `μ_naturality₂` / 定理 `μ_naturality₂`

English:
theorem μ_naturality₂
  given: {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) [F.LaxMonoidal]
  proof: by
  have := congr_app (μ_natural F f g) X
  dsimp at this
  simpa using this

@[reassoc (attr := simp)]

中文:
定理 μ_naturality₂
  条件: {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) [F.松弛幺半群]
  证明: by
  have := congr_app (μ_natural F f g) X
  dsimp at this
  simpa using this

@[reassoc (attr := simp)]

Depends on / 依赖: congr_app
-/
theorem μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) [F.LaxMonoidal] :
    (F.map g).app ((F.obj m).obj X) ≫ (F.obj n').map ((F.map f).app X) ≫ (μ F m' n').app X =
      (μ F m n).app X ≫ (F.map (f otimesₘ g)).app X := by
  have := congr_app (μ_natural F f g) X
  dsimp at this
  simpa using this

@[reassoc (attr := simp)]
/--
theorem `μ_naturalityₗ` / 定理 `μ_naturalityₗ`

English:
theorem μ_naturalityₗ
  given: {m n m' : M} (f : m ⟶ m') (X : C) [F.LaxMonoidal]
  proof: by
  rw [← tensorHom_id]; rw [← μ_naturality₂ F f (𝟙 n) X]
  simp

@[reassoc (attr := simp)]

中文:
定理 μ_naturalityₗ
  条件: {m n m' : M} (f : m ⟶ m') (X : C) [F.松弛幺半群]
  证明: by
  rw [← tensorHom_id]; rw [← μ_naturality₂ F f (𝟙 n) X]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: tensorHom_id
-/
theorem μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) [F.LaxMonoidal] :
    (F.obj n).map ((F.map f).app X) ≫ (μ F m' n).app X =
      (μ F m n).app X ≫ (F.map (f ▷ n)).app X := by
  rw [← tensorHom_id]; rw [← μ_naturality₂ F f (𝟙 n) X]
  simp

@[reassoc (attr := simp)]
/--
theorem `μ_naturalityᵣ` / 定理 `μ_naturalityᵣ`

English:
theorem μ_naturalityᵣ
  given: {m n n' : M} (g : n ⟶ n') (X : C) [F.LaxMonoidal]
  proof: by
  rw [← id_tensorHom]; rw [← μ_naturality₂ F (𝟙 m) g X]
  simp

@[reassoc (attr := simp)]

中文:
定理 μ_naturalityᵣ
  条件: {m n n' : M} (g : n ⟶ n') (X : C) [F.松弛幺半群]
  证明: by
  rw [← id_tensorHom]; rw [← μ_naturality₂ F (𝟙 m) g X]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: id_tensorHom
-/
theorem μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) [F.LaxMonoidal] :
    (F.map g).app ((F.obj m).obj X) ≫ (μ F m n').app X =
      (μ F m n).app X ≫ (F.map (m ◁ g)).app X := by
  rw [← id_tensorHom]; rw [← μ_naturality₂ F (𝟙 m) g X]
  simp

@[reassoc (attr := simp)]
/--
theorem `δ_naturalityₗ` / 定理 `δ_naturalityₗ`

English:
theorem δ_naturalityₗ
  given: {m n m' : M} (f : m ⟶ m') (X : C) [F.OplaxMonoidal]
  proof: congr_app (δ_natural_left F f n) X

@[reassoc (attr := simp)]

中文:
定理 δ_naturalityₗ
  条件: {m n m' : M} (f : m ⟶ m') (X : C) [F.反松弛幺半群]
  证明: congr_app (δ_natural_left F f n) X

@[reassoc (attr := simp)]

Depends on / 依赖: congr_app
-/
theorem δ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.obj n).map ((F.map f).app X) =
      (F.map (f ▷ n)).app X ≫ (δ F m' n).app X :=
  congr_app (δ_natural_left F f n) X

@[reassoc (attr := simp)]
/--
theorem `δ_naturalityᵣ` / 定理 `δ_naturalityᵣ`

English:
theorem δ_naturalityᵣ
  given: {m n n' : M} (g : n ⟶ n') (X : C) [F.OplaxMonoidal]
  proof: congr_app (δ_natural_right F m g) X

@[reassoc]

中文:
定理 δ_naturalityᵣ
  条件: {m n n' : M} (g : n ⟶ n') (X : C) [F.反松弛幺半群]
  证明: congr_app (δ_natural_right F m g) X

@[reassoc]

Depends on / 依赖: congr_app
-/
theorem δ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) [F.OplaxMonoidal] :
    (δ F m n).app X ≫ (F.map g).app ((F.obj m).obj X) =
      (F.map (m ◁ g)).app X ≫ (δ F m n').app X :=
  congr_app (δ_natural_right F m g) X

@[reassoc]
/--
theorem `left_unitality_app` / 定理 `left_unitality_app`

English:
theorem left_unitality_app
  given: (n : M) (X : C) [F.LaxMonoidal]
  proof: congr_app (left_unitality F n).symm X

@[simp, reassoc]

中文:
定理 left_unitality_app
  条件: (n : M) (X : C) [F.松弛幺半群]
  证明: congr_app (left_unitality F n).symm X

@[simp, reassoc]

Depends on / 依赖: congr_app, left_unitality
-/
theorem left_unitality_app (n : M) (X : C) [F.LaxMonoidal] :
    (F.obj n).map ((ε F).app X) ≫ (μ F (𝟙_ M) n).app X ≫ (F.map (fun_ n).hom).app X = 𝟙 _ :=
  congr_app (left_unitality F n).symm X

@[simp, reassoc]
/--
theorem `obj_ε_app` / 定理 `obj_ε_app`

English:
theorem obj_ε_app
  given: (n : M) (X : C) [F.Monoidal]
  proof: by
  rw [map_leftUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app, endofunctorMonoidalCategory_tensorObj_obj,
    Category.comp_id]

@[simp, reassoc]

中文:
定理 obj_ε_app
  条件: (n : M) (X : C) [F.幺半群]
  证明: by
  rw [map_leftUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app, endofunctorMonoidalCategory_tensorObj_obj,
    Category.comp_id]

@[simp, reassoc]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, comp_id, endofunctorMonoidalCategory_tensorObj_obj, id_comp, map_leftUnitor_inv
-/
theorem obj_ε_app (n : M) (X : C) [F.Monoidal] :
    (F.obj n).map ((ε F).app X) = (F.map (fun_ n).inv).app X ≫ (δ F (𝟙_ M) n).app X := by
  rw [map_leftUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app, endofunctorMonoidalCategory_tensorObj_obj,
    Category.comp_id]

@[simp, reassoc]
/--
theorem `obj_η_app` / 定理 `obj_η_app`

English:
theorem obj_η_app
  given: (n : M) (X : C) [F.Monoidal]
  proof: by
  rw [← cancel_mono ((F.obj n).map ((ε F).app X))]; rw [← Functor.map_comp]
  simp

@[reassoc]

中文:
定理 obj_η_app
  条件: (n : M) (X : C) [F.幺半群]
  证明: by
  rw [← cancel_mono ((F.obj n).map ((ε F).app X))]; rw [← Functor.map_comp]
  simp

@[reassoc]

Depends on / 依赖: F.obj, Functor, Functor.map_comp, cancel_mono, map_comp
-/
theorem obj_η_app (n : M) (X : C) [F.Monoidal] :
    (F.obj n).map ((η F).app X) = (μ F (𝟙_ M) n).app X ≫ (F.map (fun_ n).hom).app X := by
  rw [← cancel_mono ((F.obj n).map ((ε F).app X))]; rw [← Functor.map_comp]
  simp

@[reassoc]
/--
theorem `right_unitality_app` / 定理 `right_unitality_app`

English:
theorem right_unitality_app
  given: (n : M) (X : C) [F.Monoidal]
  proof: congr_app (Functor.LaxMonoidal.right_unitality F n).symm X

@[simp]

中文:
定理 right_unitality_app
  条件: (n : M) (X : C) [F.幺半群]
  证明: congr_app (Functor.LaxMonoidal.right_unitality F n).symm X

@[simp]

Depends on / 依赖: Functor, Functor.LaxMonoidal.right_unitality, LaxMonoidal, congr_app, right_unitality
-/
theorem right_unitality_app (n : M) (X : C) [F.Monoidal] :
    (ε F).app ((F.obj n).obj X) ≫ (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X = 𝟙 _ :=
  congr_app (Functor.LaxMonoidal.right_unitality F n).symm X

@[simp]
/--
theorem `ε_app_obj` / 定理 `ε_app_obj`

English:
theorem ε_app_obj
  given: (n : M) (X : C) [F.Monoidal]
  proof: by
  rw [map_rightUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[simp]

中文:
定理 ε_app_obj
  条件: (n : M) (X : C) [F.幺半群]
  证明: by
  rw [map_rightUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[simp]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, comp_id, endofunctorMonoidalCategory_tensorObj_obj, id_comp, map_rightUnitor_inv
-/
theorem ε_app_obj (n : M) (X : C) [F.Monoidal] :
    (ε F).app ((F.obj n).obj X) = (F.map (ρ_ n).inv).app X ≫ (δ F n (𝟙_ M)).app X := by
  rw [map_rightUnitor_inv]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[simp]
/--
theorem `η_app_obj` / 定理 `η_app_obj`

English:
theorem η_app_obj
  given: (n : M) (X : C) [F.Monoidal]
  proof: by
  rw [map_rightUnitor]
  dsimp
  simp only [Category.comp_id, μ_δ_app_assoc]

中文:
定理 η_app_obj
  条件: (n : M) (X : C) [F.幺半群]
  证明: by
  rw [map_rightUnitor]
  dsimp
  simp only [Category.comp_id, μ_δ_app_assoc]

Depends on / 依赖: Category, Category.comp_id, comp_id, map_rightUnitor
-/
theorem η_app_obj (n : M) (X : C) [F.Monoidal] :
    (η F).app ((F.obj n).obj X) = (μ F n (𝟙_ M)).app X ≫ (F.map (ρ_ n).hom).app X := by
  rw [map_rightUnitor]
  dsimp
  simp only [Category.comp_id, μ_δ_app_assoc]

set_option backward.isDefEq.respectTransparency false in -- Needed below
@[reassoc]
/--
theorem `associativity_app` / 定理 `associativity_app`

English:
theorem associativity_app
  given: (m₁ m₂ m₃ : M) (X : C) [F.LaxMonoidal]
  proof: by
  have := congr_app (associativity F m₁ m₂ m₃) X
  dsimp at this
  simpa using this

@[simp, reassoc]

中文:
定理 associativity_app
  条件: (m₁ m₂ m₃ : M) (X : C) [F.松弛幺半群]
  证明: by
  have := congr_app (associativity F m₁ m₂ m₃) X
  dsimp at this
  simpa using this

@[simp, reassoc]

Depends on / 依赖: associativity, congr_app
-/
theorem associativity_app (m₁ m₂ m₃ : M) (X : C) [F.LaxMonoidal] :
    (F.obj m₃).map ((μ F m₁ m₂).app X) ≫
        (μ F (m₁ otimes m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).hom).app X =
      (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫ (μ F m₁ (m₂ otimes m₃)).app X := by
  have := congr_app (associativity F m₁ m₂ m₃) X
  dsimp at this
  simpa using this

@[simp, reassoc]
/--
theorem `obj_μ_app` / 定理 `obj_μ_app`

English:
theorem obj_μ_app
  given: (m₁ m₂ m₃ : M) (X : C) [F.Monoidal]
  proof: by
  rw [← associativity_app_assoc]
  simp

@[simp, reassoc]

中文:
定理 obj_μ_app
  条件: (m₁ m₂ m₃ : M) (X : C) [F.幺半群]
  证明: by
  rw [← associativity_app_assoc]
  simp

@[simp, reassoc]

Depends on / 依赖: associativity_app_assoc
-/
theorem obj_μ_app (m₁ m₂ m₃ : M) (X : C) [F.Monoidal] :
    (F.obj m₃).map ((μ F m₁ m₂).app X) =
      (μ F m₂ m₃).app ((F.obj m₁).obj X) ≫
        (μ F m₁ (m₂ otimes m₃)).app X ≫
          (F.map (α_ m₁ m₂ m₃).inv).app X ≫ (δ F (m₁ otimes m₂) m₃).app X := by
  rw [← associativity_app_assoc]
  simp

@[simp, reassoc]
/--
theorem `obj_μ_inv_app` / 定理 `obj_μ_inv_app`

English:
theorem obj_μ_inv_app
  given: (m₁ m₂ m₃ : M) (X : C) [F.Monoidal]
  proof: by
  rw [map_associator]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app_assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[reassoc (attr := simp)]

中文:
定理 obj_μ_inv_app
  条件: (m₁ m₂ m₃ : M) (X : C) [F.幺半群]
  证明: by
  rw [map_associator]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app_assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, comp_id, endofunctorMonoidalCategory_tensorObj_obj, id_comp, map_associator
-/
theorem obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) [F.Monoidal] :
    (F.obj m₃).map ((δ F m₁ m₂).app X) =
      (μ F (m₁ otimes m₂) m₃).app X ≫
        (F.map (α_ m₁ m₂ m₃).hom).app X ≫
          (δ F m₁ (m₂ otimes m₃)).app X ≫ (δ F m₂ m₃).app ((F.obj m₁).obj X) := by
  rw [map_associator]
  dsimp
  simp only [Category.id_comp, Category.assoc, μ_δ_app_assoc, μ_δ_app,
    endofunctorMonoidalCategory_tensorObj_obj, Category.comp_id]

@[reassoc (attr := simp)]
/--
theorem `obj_zero_map_μ_app` / 定理 `obj_zero_map_μ_app`

English:
theorem obj_zero_map_μ_app
  given: {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) [F.Monoidal]
  proof: by
  rw [← cancel_epi ((ε F).app _)]; rw [← cancel_mono ((δ F _ _).app _)]
  simp

@[simp]

中文:
定理 obj_zero_map_μ_app
  条件: {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) [F.幺半群]
  证明: by
  rw [← cancel_epi ((ε F).app _)]; rw [← cancel_mono ((δ F _ _).app _)]
  simp

@[simp]

Depends on / 依赖: cancel_epi, cancel_mono
-/
theorem obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) [F.Monoidal] :
    (F.obj (𝟙_ M)).map f ≫ (μ F m (𝟙_ M)).app _ =
    (η F).app _ ≫ f ≫ (F.map (ρ_ m).inv).app _ := by
  rw [← cancel_epi ((ε F).app _)]; rw [← cancel_mono ((δ F _ _).app _)]
  simp

@[simp]
/--
theorem `obj_μ_zero_app` / 定理 `obj_μ_zero_app`

English:
theorem obj_μ_zero_app
  given: (m₁ m₂ : M) (X : C) [F.Monoidal]
  proof: by
  rw [← obj_η_app_assoc]; rw [← Functor.map_comp]
  simp

中文:
定理 obj_μ_zero_app
  条件: (m₁ m₂ : M) (X : C) [F.幺半群]
  证明: by
  rw [← obj_η_app_assoc]; rw [← Functor.map_comp]
  simp

Depends on / 依赖: Functor, Functor.map_comp, map_comp
-/
theorem obj_μ_zero_app (m₁ m₂ : M) (X : C) [F.Monoidal] :
    (μ F (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫ (μ F m₁ (𝟙_ M otimes m₂)).app X ≫
    (F.map (α_ m₁ (𝟙_ M) m₂).inv).app X ≫ (δ F (m₁ otimes 𝟙_ M) m₂).app X =
    (μ F (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫
    (F.map (fun_ m₂).hom).app ((F.obj m₁).obj X) ≫ (F.obj m₂).map ((F.map (ρ_ m₁).inv).app X) := by
  rw [← obj_η_app_assoc]; rw [← Functor.map_comp]
  simp

/-- If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`. -/
@[simps!]
/--
Definition of `unitOfTensorIsoUnit` / `unitOfTensorIsoUnit` 的定义

English:
definition unitOfTensorIsoUnit
  signature: (m n : M) (h : m otimes n ≅ 𝟙_ M) [F.Monoidal]
  body: μIso F m n ≪≫ F.mapIso h ≪≫ (εIso F).symm

中文:
定义 unitOfTensorIsoUnit
  签名: (m n : M) (h : m otimes n ≅ 𝟙_ M) [F.幺半群]
  定义体: μIso F m n ≪≫ F.mapIso h ≪≫ (εIso F).symm

Depends on / 依赖: F.mapIso, mapIso
-/
noncomputable def unitOfTensorIsoUnit (m n : M) (h : m otimes n ≅ 𝟙_ M) [F.Monoidal] :
    F.obj m ⋙ F.obj n ≅ 𝟭 C :=
  μIso F m n ≪≫ F.mapIso h ≪≫ (εIso F).symm

/-- If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`. -/
@[simps]
/--
Definition of `equivOfTensorIsoUnit` / `equivOfTensorIsoUnit` 的定义

English:
definition equivOfTensorIsoUnit
  signature: (m n : M) (h₁ : m otimes n ≅ 𝟙_ M) (h₂ : n otimes m ≅ 𝟙_ M)
  body: F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp X := by
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, η_app_obj, Category.assoc,
      obj_μ_inv_app, Functor.map_comp, δ_μ_app_assoc,

中文:
定义 equivOfTensorIsoUnit
  签名: (m n : M) (h₁ : m otimes n ≅ 𝟙_ M) (h₂ : n otimes m ≅ 𝟙_ M)
  定义体: F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp X := by
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, η_app_obj, Category.assoc,
      obj_μ_inv_app, Functor.map_comp, δ_μ_app_assoc,

Depends on / 依赖: F.obj
-/
noncomputable def equivOfTensorIsoUnit (m n : M) (h₁ : m otimes n ≅ 𝟙_ M) (h₂ : n otimes m ≅ 𝟙_ M)
    (H : h₁.hom ▷ m ≫ (fun_ m).hom = (α_ m n m).hom ≫ m ◁ h₂.hom ≫ (ρ_ m).hom) [F.Monoidal] :
    C ≌ C where
  functor := F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp X := by
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, η_app_obj, Category.assoc,
      obj_μ_inv_app, Functor.map_comp, δ_μ_app_assoc, obj_ε_app,
      unitOfTensorIsoUnit_inv_app]
    simp only [← NatTrans.comp_app, ← F.map_comp, ← H, inv_hom_whiskerRight_assoc,
      Iso.inv_hom_id, Functor.map_id, NatTrans.id_app]

end CategoryTheory
