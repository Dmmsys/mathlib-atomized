/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Currying of functors in three variables

We study the equivalence of categories
`currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E`.

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₁₂ C₃ C₂₃ D₁ D₂ D₃ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₁₂] [Category* C₂₃]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* E]

/--
Definition of `currying₃` / `currying₃` 的定义

English:
definition currying₃
  signature: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E
  body: currying.trans (currying.trans (prod.associativity C₁ C₂ C₃).congrLeft)

中文:
定义 currying₃
  签名: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E
  定义体: currying.trans (currying.trans (prod.associativity C₁ C₂ C₃).congrLeft)

Depends on / 依赖: associativity, congrLeft, currying, currying.trans, prod.associativity
-/
def currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ C₁ × C₂ × C₃ ⥤ E :=
  currying.trans (currying.trans (prod.associativity C₁ C₂ C₃).congrLeft)

/--
Definition of `uncurry₃` / `uncurry₃` 的定义

English:
abbreviation uncurry₃
  signature: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E
  body: currying₃.functor

中文:
缩写 uncurry₃
  签名: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E
  定义体: currying₃.functor

Depends on / 依赖: functor
-/
abbrev uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E := currying₃.functor

/--
Definition of `curry₃` / `curry₃` 的定义

English:
abbreviation curry₃
  signature: : (C₁ × C₂ × C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E
  body: currying₃.inverse

中文:
缩写 curry₃
  签名: : (C₁ × C₂ × C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E
  定义体: currying₃.inverse

Depends on / 依赖: inverse
-/
abbrev curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ E := currying₃.inverse

/--
Definition of `fullyFaithfulUncurry₃` / `fullyFaithfulUncurry₃` 的定义

English:
definition fullyFaithfulUncurry₃
  signature: :
  body: currying₃.fullyFaithfulFunctor

中文:
定义 fullyFaithfulUncurry₃
  签名: :
  定义体: currying₃.fullyFaithfulFunctor

Depends on / 依赖: fullyFaithfulFunctor
-/
def fullyFaithfulUncurry₃ :
    (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ × C₂ × C₃ ⥤ E)).FullyFaithful :=
  currying₃.fullyFaithfulFunctor

/--
Definition of `fullyFaithfulCurry₃` / `fullyFaithfulCurry₃` 的定义

English:
definition fullyFaithfulCurry₃
  signature: :
  body: currying₃.fullyFaithfulInverse

中文:
定义 fullyFaithfulCurry₃
  签名: :
  定义体: currying₃.fullyFaithfulInverse

Depends on / 依赖: fullyFaithfulInverse
-/
def fullyFaithfulCurry₃ :
    (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).FullyFaithful :=
  currying₃.fullyFaithfulInverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E).Full
  body: fullyFaithfulUncurry₃.full

中文:
实例 :
  签名: (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E).满
  定义体: fullyFaithfulUncurry₃.full
-/
instance : (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E).Full :=
  fullyFaithfulUncurry₃.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E).Faithful
  body: fullyFaithfulUncurry₃.faithful

中文:
实例 :
  签名: (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E).忠实
  定义体: fullyFaithfulUncurry₃.faithful

Depends on / 依赖: faithful
-/
instance : (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ C₁ × C₂ × C₃ ⥤ E).Faithful :=
  fullyFaithfulUncurry₃.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).Full
  body: fullyFaithfulCurry₃.full

中文:
实例 :
  签名: (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).满
  定义体: fullyFaithfulCurry₃.full
-/
instance : (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).Full :=
  fullyFaithfulCurry₃.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).Faithful
  body: fullyFaithfulCurry₃.faithful

@[simp]

中文:
实例 :
  签名: (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).忠实
  定义体: fullyFaithfulCurry₃.faithful

@[simp]

Depends on / 依赖: faithful
-/
instance : (curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E)).Faithful :=
  fullyFaithfulCurry₃.faithful

@[simp]
/--
lemma `curry₃_obj_map_app_app` / 引理 `curry₃_obj_map_app_app`

English:
lemma curry₃_obj_map_app_app
  statement: (F : C₁ × C₂ × C₃ ⥤ E)
  proof: rfl

@[simp]

中文:
引理 curry₃_obj_map_app_app
  结论: (F : C₁ × C₂ × C₃ ⥤ E)
  证明: rfl

@[simp]
-/
lemma curry₃_obj_map_app_app (F : C₁ × C₂ × C₃ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) :
    (((curry₃.obj F).map f).app X₂).app X₃ = F.map ⟨f, 𝟙 X₂, 𝟙 X₃⟩ := rfl

@[simp]
/--
lemma `curry₃_obj_obj_map_app` / 引理 `curry₃_obj_obj_map_app`

English:
lemma curry₃_obj_obj_map_app
  statement: (F : C₁ × C₂ × C₃ ⥤ E)
  proof: rfl

@[simp]

中文:
引理 curry₃_obj_obj_map_app
  结论: (F : C₁ × C₂ × C₃ ⥤ E)
  证明: rfl

@[simp]
-/
lemma curry₃_obj_obj_map_app (F : C₁ × C₂ × C₃ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) :
    (((curry₃.obj F).obj X₁).map f).app X₃ = F.map ⟨𝟙 X₁, f, 𝟙 X₃⟩ := rfl

@[simp]
/--
lemma `curry₃_obj_obj_obj_map` / 引理 `curry₃_obj_obj_obj_map`

English:
lemma curry₃_obj_obj_obj_map
  statement: (F : C₁ × C₂ × C₃ ⥤ E)
  proof: rfl

@[simp]

中文:
引理 curry₃_obj_obj_obj_map
  结论: (F : C₁ × C₂ × C₃ ⥤ E)
  证明: rfl

@[simp]
-/
lemma curry₃_obj_obj_obj_map (F : C₁ × C₂ × C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) :
    (((curry₃.obj F).obj X₁).obj X₂).map f = F.map ⟨𝟙 X₁, 𝟙 X₂, f⟩ := rfl

@[simp]
/--
lemma `curry₃_map_app_app_app` / 引理 `curry₃_map_app_app_app`

English:
lemma curry₃_map_app_app_app
  statement: {F G : C₁ × C₂ × C₃ ⥤ E} (f : F ⟶ G)
  proof: rfl

中文:
引理 curry₃_map_app_app_app
  结论: {F G : C₁ × C₂ × C₃ ⥤ E} (f : F ⟶ G)
  证明: rfl
-/
lemma curry₃_map_app_app_app {F G : C₁ × C₂ × C₃ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((curry₃.map f).app X₁).app X₂).app X₃ = f.app ⟨X₁, X₂, X₃⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `currying₃_unitIso_hom_app_app_app_app` / 引理 `currying₃_unitIso_hom_app_app_app_app`

English:
lemma currying₃_unitIso_hom_app_app_app_app
  statement: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  proof: by
  simp [currying₃, Equivalence.unit]

中文:
引理 currying₃_unitIso_hom_app_app_app_app
  结论: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  证明: by
  simp [currying₃, Equivalence.unit]

Depends on / 依赖: Equivalence, Equivalence.unit
-/
lemma currying₃_unitIso_hom_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.unitIso.hom.app F).app X₁).app X₂).app X₃ = 𝟙 _ := by
  simp [currying₃, Equivalence.unit]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `currying₃_unitIso_inv_app_app_app_app` / 引理 `currying₃_unitIso_inv_app_app_app_app`

English:
lemma currying₃_unitIso_inv_app_app_app_app
  statement: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  proof: by
  simp [currying₃, Equivalence.unitInv]

中文:
引理 currying₃_unitIso_inv_app_app_app_app
  结论: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  证明: by
  simp [currying₃, Equivalence.unitInv]

Depends on / 依赖: Equivalence, Equivalence.unitInv, unitInv
-/
lemma currying₃_unitIso_inv_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.unitIso.inv.app F).app X₁).app X₂).app X₃ = 𝟙 _ := by
  simp [currying₃, Equivalence.unitInv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F₁ : C₁ ⥤ D₁`, `F₂ : C₂ ⥤ D₂`, `F₃ : C₃ ⥤ D₃`
and `G : D₁ × D₂ × D₃ ⥤ E`, this is the isomorphism between
`curry₃.obj (F₁.prod (F₂.prod F₃) ⋙ G) : C₁ ⥤ C₂ ⥤ C₃ ⥤ E`
and `F₁ ⋙ curry₃.obj G ⋙ ((whiskeringLeft₂ E).obj F₂).obj F₃`. -/
@[simps!]
/--
Definition of `curry₃ObjProdComp` / `curry₃ObjProdComp` 的定义

English:
definition curry₃ObjProdComp
  signature: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (G : D₁ × D₂ × D₃ ⥤ E)
  body: NatIso.ofComponents
    (fun X₁ => NatIso.ofComponents
      (fun X₂ => NatIso.ofComponents (fun X₃ => Iso.refl _)))

中文:
定义 curry₃ObjProdComp
  签名: (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (G : D₁ × D₂ × D₃ ⥤ E)
  定义体: NatIso.ofComponents
    (fun X₁ => NatIso.ofComponents
      (fun X₂ => NatIso.ofComponents (fun X₃ => Iso.refl _)))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def curry₃ObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (G : D₁ × D₂ × D₃ ⥤ E) :
    curry₃.obj (F₁.prod (F₂.prod F₃) ⋙ G) ≅
      F₁ ⋙ curry₃.obj G ⋙ ((whiskeringLeft₂ E).obj F₂).obj F₃ :=
  NatIso.ofComponents
    (fun X₁ => NatIso.ofComponents
      (fun X₂ => NatIso.ofComponents (fun X₃ => Iso.refl _)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `bifunctorComp₁₂` can be described in terms of the curryfication of functors. -/
@[simps!]
/--
Definition of `bifunctorComp₁₂Iso` / `bifunctorComp₁₂Iso` 的定义

English:
definition bifunctorComp₁₂Iso
  signature: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ E)
  body: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

中文:
定义 bifunctorComp₁₂Iso
  签名: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ E)
  定义体: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def bifunctorComp₁₂Iso (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ E) :
    bifunctorComp₁₂ F₁₂ G ≅ curry.obj (uncurry.obj F₁₂ ⋙ G) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `bifunctorComp₂₃` can be described in terms of the curryfication of functors. -/
@[simps!]
/--
Definition of `bifunctorComp₂₃Iso` / `bifunctorComp₂₃Iso` 的定义

English:
definition bifunctorComp₂₃Iso
  signature: (F : C₁ ⥤ C₂₃ ⥤ E) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  body: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ =>
    NatIso.ofComponents (fun _ => Iso.refl _)))

中文:
定义 bifunctorComp₂₃Iso
  签名: (F : C₁ ⥤ C₂₃ ⥤ E) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  定义体: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ =>
    NatIso.ofComponents (fun _ => Iso.refl _)))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def bifunctorComp₂₃Iso (F : C₁ ⥤ C₂₃ ⥤ E) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) :
    bifunctorComp₂₃ F G₂₃ ≅
    curry.obj (curry.obj (prod.associator _ _ _ ⋙
      uncurry.obj (uncurry.obj G₂₃ ⋙ F.flip).flip)) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ =>
    NatIso.ofComponents (fun _ => Iso.refl _)))

/--
Flip the first and third arguments in a trifunctor.
-/
@[simps!]
/--
Definition of `flip₁₃` / `flip₁₃` 的定义

English:
definition flip₁₃
  signature: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  body: {
    obj H := {
      obj K := ((F.obj K).obj H).obj G
      map f := ((F.map f).app _).app _ }
    map g := { app X := ((F.obj X).map g).app _ } }
  map h := { app X := { app Y := ((F.obj Y).obj X).map h } }

中文:
定义 flip₁₃
  签名: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  定义体: {
    obj H := {
      obj K := ((F.obj K).obj H).obj G
      map f := ((F.map f).app _).app _ }
    map g := { app X := ((F.obj X).map g).app _ } }
  map h := { app X := { app Y := ((F.obj Y).obj X).map h } }
-/
def flip₁₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : C₃ ⥤ C₂ ⥤ C₁ ⥤ E where
  obj G := {
    obj H := {
      obj K := ((F.obj K).obj H).obj G
      map f := ((F.map f).app _).app _ }
    map g := { app X := ((F.obj X).map g).app _ } }
  map h := { app X := { app Y := ((F.obj Y).obj X).map h } }

set_option backward.defeqAttrib.useBackward true in
/--
Flip the first and third arguments in a trifunctor, as a functor.
-/
@[simps!]
/--
Definition of `flip₁₃Functor` / `flip₁₃Functor` 的定义

English:
definition flip₁₃Functor
  signature: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₃ ⥤ C₂ ⥤ C₁ ⥤ E) where
  body: F.flip₁₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } } }

中文:
定义 flip₁₃Functor
  签名: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₃ ⥤ C₂ ⥤ C₁ ⥤ E) where
  定义体: F.flip₁₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } } }

Depends on / 依赖: F.flip
-/
def flip₁₃Functor : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₃ ⥤ C₂ ⥤ C₁ ⥤ E) where
  obj F := F.flip₁₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } } }

/--
Flip the second and third arguments in a trifunctor.
-/
@[simps!]
/--
Definition of `flip₂₃` / `flip₂₃` 的定义

English:
definition flip₂₃
  signature: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  body: (F.obj G).flip
  map f := (flipFunctor _ _ _).map (F.map f)

中文:
定义 flip₂₃
  签名: (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
  定义体: (F.obj G).flip
  map f := (flipFunctor _ _ _).map (F.map f)

Depends on / 依赖: F.obj
-/
def flip₂₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : C₁ ⥤ C₃ ⥤ C₂ ⥤ E where
  obj G := (F.obj G).flip
  map f := (flipFunctor _ _ _).map (F.map f)

set_option backward.defeqAttrib.useBackward true in
/--
Flip the second and third arguments in a trifunctor, as a functor.
-/
@[simps!]
/--
Definition of `flip₂₃Functor` / `flip₂₃Functor` 的定义

English:
definition flip₂₃Functor
  signature: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ ⥤ C₃ ⥤ C₂ ⥤ E) where
  body: F.flip₂₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } }
    naturality _ _ g := by
      ext
      simp only [flip₂₃_obj_obj_obj, NatTrans.comp_app, flip₂₃_map_app_app]
      simp [← NatTrans.comp_app] }

中文:
定义 flip₂₃Functor
  签名: : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ ⥤ C₃ ⥤ C₂ ⥤ E) where
  定义体: F.flip₂₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } }
    naturality _ _ g := by
      ext
      simp only [flip₂₃_obj_obj_obj, NatTrans.comp_app, flip₂₃_map_app_app]
      simp [← NatTrans.comp_app] }

Depends on / 依赖: F.flip
-/
def flip₂₃Functor : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ ⥤ C₃ ⥤ C₂ ⥤ E) where
  obj F := F.flip₂₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } }
    naturality _ _ g := by
      ext
      simp only [flip₂₃_obj_obj_obj, NatTrans.comp_app, flip₂₃_map_app_app]
      simp [← NatTrans.comp_app] }

end Functor

end CategoryTheory
