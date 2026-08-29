/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Curry and uncurry, as functors.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

This is used in `CategoryTheory.Category.Cat.CartesianClosed` to equip the category of small
categories `Cat.{u, u}` with a Cartesian closed structure.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

open scoped CategoryTheory.Prod

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E] {H : Type u₅} [Category.{v₅} H]

/-- The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
@[simps, implicit_reducible]
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E where
  body: { obj := fun X => (F.obj X.1).obj X.2
      map := fun {X} {Y} f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp := fun f g => by
        simp only [prod_comp_fst, prod_comp_snd, Functor.map_comp, NatTrans.comp_app,
          Category.assoc]
        slice_lhs 2 3 => rw [← NatTrans.natura

中文:
定义 uncurry
  签名: : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E where
  定义体: { obj := fun X => (F.obj X.1).obj X.2
      map := fun {X} {Y} f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp := fun f g => by
        simp only [prod_comp_fst, prod_comp_snd, Functor.map_comp, NatTrans.comp_app,
          Category.assoc]
        slice_lhs 2 3 => rw [← NatTrans.natura

Depends on / 依赖: Category, Category.assoc, F.map, F.obj, Functor, Functor.map_comp, NatTrans, NatTrans.comp_app, NatTrans.naturality, T.app, comp_app, map_comp, naturality, prod_comp_fst, prod_comp_snd, slice_lhs
-/
def uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E where
  obj F :=
    { obj := fun X => (F.obj X.1).obj X.2
      map := fun {X} {Y} f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp := fun f g => by
        simp only [prod_comp_fst, prod_comp_snd, Functor.map_comp, NatTrans.comp_app,
          Category.assoc]
        slice_lhs 2 3 => rw [← NatTrans.naturality]
        rw [Category.assoc] }
  map T :=
    { app := fun X => (T.app X.1).app X.2
      naturality := fun X Y f => by
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [NatTrans.naturality]
        slice_lhs 1 2 => rw [← NatTrans.comp_app, NatTrans.naturality, NatTrans.comp_app]
        rw [Category.assoc] }

/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
@[implicit_reducible]
/--
Definition of `curryObj` / `curryObj` 的定义

English:
definition curryObj
  signature: (F : C × D ⥤ E)
  body: { obj := fun Y => F.obj (X, Y)
      map := fun g => F.map (𝟙 X ×ₘ g)
      map_id := fun Y => by rw [← prod_id]; exact F.map_id ⟨X,Y⟩
      map_comp := fun f g => by simp [← F.map_comp] }
  map f :=
    { app := fun Y => F.map (f ×ₘ 𝟙 Y)
      naturality := fun {Y} {Y'} g => by simp [← F.map_comp] 

中文:
定义 curryObj
  签名: (F : C × D ⥤ E)
  定义体: { obj := fun Y => F.obj (X, Y)
      map := fun g => F.map (𝟙 X ×ₘ g)
      map_id := fun Y => by rw [← prod_id]; exact F.map_id ⟨X,Y⟩
      map_comp := fun f g => by simp [← F.map_comp] }
  map f :=
    { app := fun Y => F.map (f ×ₘ 𝟙 Y)
      naturality := fun {Y} {Y'} g => by simp [← F.map_comp] 

Depends on / 依赖: F.map, F.map_comp, F.map_id, F.obj, map_comp, map_id, naturality, prod_id
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E where
  obj X :=
    { obj := fun Y => F.obj (X, Y)
      map := fun g => F.map (𝟙 X ×ₘ g)
      map_id := fun Y => by rw [← prod_id]; exact F.map_id ⟨X,Y⟩
      map_comp := fun f g => by simp [← F.map_comp] }
  map f :=
    { app := fun Y => F.map (f ×ₘ 𝟙 Y)
      naturality := fun {Y} {Y'} g => by simp [← F.map_comp] }
  map_id := fun X => by ext Y; exact F.map_id _
  map_comp := fun f g => by ext Y; simp [← F.map_comp]

/-- The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
@[implicit_reducible, simps! obj_obj_obj obj_obj_map obj_map_app map_app_app]
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  body: curryObj F
  map T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality := fun Y Y' g => by
            dsimp [curryObj]
            rw [NatTrans.naturality] }
      naturality := fun X X' f => by
        ext; dsimp [curryObj]
        rw [NatTrans.naturality] }

中文:
定义 curry
  签名: : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  定义体: curryObj F
  map T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality := fun Y Y' g => by
            dsimp [curryObj]
            rw [NatTrans.naturality] }
      naturality := fun X X' f => by
        ext; dsimp [curryObj]
        rw [NatTrans.naturality] }

Depends on / 依赖: curryObj
-/
def curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  obj F := curryObj F
  map T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality := fun Y Y' g => by
            dsimp [curryObj]
            rw [NatTrans.naturality] }
      naturality := fun X X' f => by
        ext; dsimp [curryObj]
        rw [NatTrans.naturality] }

-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of functor categories given by currying/uncurrying.
-/
@[implicit_reducible, simps!]
/--
Definition of `currying` / `currying` 的定义

English:
definition currying
  signature: : C ⥤ D ⥤ E ≌ C × D ⥤ E where
  body: uncurry
  inverse := curry
  unitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))
  counitIso := NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun _ => Iso.refl _) (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      dsimp at f₁

中文:
定义 currying
  签名: : C ⥤ D ⥤ E ≌ C × D ⥤ E where
  定义体: uncurry
  inverse := curry
  unitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))
  counitIso := NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun _ => Iso.refl _) (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      dsimp at f₁

Depends on / 依赖: uncurry
-/
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E where
  functor := uncurry
  inverse := curry
  unitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))
  counitIso := NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun _ => Iso.refl _) (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      dsimp at f₁ f₂ ⊢
      simp only [← F.map_comp, prod_comp, Category.comp_id, Category.id_comp]))

/-- The equivalence of functor categories given by flipping. -/
@[implicit_reducible, simps!]
/--
Definition of `flipping` / `flipping` 的定义

English:
definition flipping
  signature: : C ⥤ D ⥤ E ≌ D ⥤ C ⥤ E where
  body: flipFunctor _ _ _
  inverse := flipFunctor _ _ _
  unitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))

中文:
定义 flipping
  签名: : C ⥤ D ⥤ E ≌ D ⥤ C ⥤ E where
  定义体: flipFunctor _ _ _
  inverse := flipFunctor _ _ _
  unitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))

Depends on / 依赖: flipFunctor
-/
def flipping : C ⥤ D ⥤ E ≌ D ⥤ C ⥤ E where
  functor := flipFunctor _ _ _
  inverse := flipFunctor _ _ _
  unitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => NatIso.ofComponents
    (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)))

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fullyFaithfulUncurry` / `fullyFaithfulUncurry` 的定义

English:
definition fullyFaithfulUncurry
  signature: : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).FullyFaithful
  body: currying.fullyFaithfulFunctor

中文:
定义 fullyFaithfulUncurry
  签名: : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).满忠实
  定义体: currying.fullyFaithfulFunctor

Depends on / 依赖: currying, currying.fullyFaithfulFunctor, fullyFaithfulFunctor
-/
def fullyFaithfulUncurry : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).FullyFaithful :=
  currying.fullyFaithfulFunctor

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fullyFaithfulCurry` / `fullyFaithfulCurry` 的定义

English:
definition fullyFaithfulCurry
  signature: : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).FullyFaithful
  body: currying.fullyFaithfulInverse

中文:
定义 fullyFaithfulCurry
  签名: : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).满忠实
  定义体: currying.fullyFaithfulInverse

Depends on / 依赖: currying, currying.fullyFaithfulInverse, fullyFaithfulInverse
-/
def fullyFaithfulCurry : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).FullyFaithful :=
  currying.fullyFaithfulInverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).Full
  body: fullyFaithfulCurry.full

中文:
实例 :
  签名: (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).满
  定义体: fullyFaithfulCurry.full

Depends on / 依赖: fullyFaithfulCurry, fullyFaithfulCurry.full
-/
instance : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).Full :=
  fullyFaithfulCurry.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).Faithful
  body: fullyFaithfulCurry.faithful

中文:
实例 :
  签名: (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).忠实
  定义体: fullyFaithfulCurry.faithful

Depends on / 依赖: faithful, fullyFaithfulCurry, fullyFaithfulCurry.faithful
-/
instance : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).Faithful :=
  fullyFaithfulCurry.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).Full
  body: fullyFaithfulUncurry.full

中文:
实例 :
  签名: (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).满
  定义体: fullyFaithfulUncurry.full

Depends on / 依赖: fullyFaithfulUncurry, fullyFaithfulUncurry.full
-/
instance : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).Full :=
  fullyFaithfulUncurry.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).Faithful
  body: fullyFaithfulUncurry.faithful

中文:
实例 :
  签名: (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).忠实
  定义体: fullyFaithfulUncurry.faithful

Depends on / 依赖: faithful, fullyFaithfulUncurry, fullyFaithfulUncurry.faithful
-/
instance : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).Faithful :=
  fullyFaithfulUncurry.faithful

/-- Given functors `F₁ : C ⥤ D`, `F₂ : C' ⥤ D'` and `G : D × D' ⥤ E`, this is the isomorphism
between `curry.obj ((F₁.prod F₂).comp G)` and
`F₁ ⋙ curry.obj G ⋙ (whiskeringLeft C' D' E).obj F₂` in the category `C ⥤ C' ⥤ E`. -/
@[simps!]
/--
Definition of `curryObjProdComp` / `curryObjProdComp` 的定义

English:
definition curryObjProdComp
  signature: {C' D' : Type*} [Category* C'] [Category* D']
  body: NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => Iso.refl _))

中文:
定义 curryObjProdComp
  签名: {C' D' : 类型} [范畴* C'] [范畴* D']
  定义体: NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def curryObjProdComp {C' D' : Type*} [Category* C'] [Category* D']
    (F₁ : C ⥤ D) (F₂ : C' ⥤ D') (G : D × D' ⥤ E) :
    curry.obj ((F₁.prod F₂).comp G) ≅
      F₁ ⋙ curry.obj G ⋙ (whiskeringLeft C' D' E).obj F₂ :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => Iso.refl _))

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[implicit_reducible, simps!]
/--
Definition of `flipIsoCurrySwapUncurry` / `flipIsoCurrySwapUncurry` 的定义

English:
definition flipIsoCurrySwapUncurry
  signature: (F : C ⥤ D ⥤ E)
  body: NatIso.ofComponents fun d => NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 flipIsoCurrySwapUncurry
  签名: (F : C ⥤ D ⥤ E)
  定义体: NatIso.ofComponents fun d => NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (Prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents fun d => NatIso.ofComponents fun _ => Iso.refl _

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[implicit_reducible, simps!]
/--
Definition of `uncurryObjFlip` / `uncurryObjFlip` 的定义

English:
definition uncurryObjFlip
  signature: (F : C ⥤ D ⥤ E)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 uncurryObjFlip
  签名: (F : C ⥤ D ⥤ E)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ Prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents fun _ => Iso.refl _

variable (B C D E)

/-- A version of `CategoryTheory.whiskeringRight` for bifunctors, obtained by uncurrying,
applying `whiskeringRight` and currying back
-/
@[implicit_reducible, simps!]
/--
Definition of `whiskeringRight₂` / `whiskeringRight₂` 的定义

English:
definition whiskeringRight₂
  signature: : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E
  body: uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry

中文:
定义 whiskeringRight₂
  签名: : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E
  定义体: uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry

Depends on / 依赖: prodFunctorToFunctorProd, uncurry, whiskeringLeft, whiskeringRight
-/
def whiskeringRight₂ : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E :=
  uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry

variable {B C D E}

/--
lemma `uncurry_obj_curry_obj` / 引理 `uncurry_obj_curry_obj`

English:
lemma uncurry_obj_curry_obj
  given: (F : B × C ⥤ D)
  statement: uncurry.obj (curry.obj F) = F
  proof: Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [← F.map_comp, Category.id_comp, Category.comp_id, prod_comp])

中文:
引理 uncurry_obj_curry_obj
  条件: (F : B × C ⥤ D)
  结论: uncurry.obj (curry.obj F) = F
  证明: Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [← F.map_comp, Category.id_comp, Category.comp_id, prod_comp])

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, F.map_comp, Functor, Functor.ext, comp_id, id_comp, map_comp, prod_comp
-/
lemma uncurry_obj_curry_obj (F : B × C ⥤ D) : uncurry.obj (curry.obj F) = F :=
  Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [← F.map_comp, Category.id_comp, Category.comp_id, prod_comp])

/--
lemma `curry_obj_injective` / 引理 `curry_obj_injective`

English:
lemma curry_obj_injective
  given: {F₁ F₂ : C × D ⥤ E} (h : curry.obj F₁ = curry.obj F₂)
  proof: by
  rw [← uncurry_obj_curry_obj F₁]; rw [← uncurry_obj_curry_obj F₂]; rw [h]

中文:
引理 curry_obj_injective
  条件: {F₁ F₂ : C × D ⥤ E} (h : curry.obj F₁ = curry.obj F₂)
  证明: by
  rw [← uncurry_obj_curry_obj F₁]; rw [← uncurry_obj_curry_obj F₂]; rw [h]

Depends on / 依赖: uncurry_obj_curry_obj
-/
lemma curry_obj_injective {F₁ F₂ : C × D ⥤ E} (h : curry.obj F₁ = curry.obj F₂) :
    F₁ = F₂ := by
  rw [← uncurry_obj_curry_obj F₁]; rw [← uncurry_obj_curry_obj F₂]; rw [h]

/--
lemma `curry_obj_uncurry_obj` / 引理 `curry_obj_uncurry_obj`

English:
lemma curry_obj_uncurry_obj
  given: (F : B ⥤ C ⥤ D)
  statement: curry.obj (uncurry.obj F) = F
  proof: Functor.ext (fun _ => Functor.ext (by simp) (by simp)) (by cat_disch)

中文:
引理 curry_obj_uncurry_obj
  条件: (F : B ⥤ C ⥤ D)
  结论: curry.obj (uncurry.obj F) = F
  证明: Functor.ext (fun _ => Functor.ext (by simp) (by simp)) (by cat_disch)

Depends on / 依赖: Functor, Functor.ext, cat_disch
-/
lemma curry_obj_uncurry_obj (F : B ⥤ C ⥤ D) : curry.obj (uncurry.obj F) = F :=
  Functor.ext (fun _ => Functor.ext (by simp) (by simp)) (by cat_disch)

/--
lemma `uncurry_obj_injective` / 引理 `uncurry_obj_injective`

English:
lemma uncurry_obj_injective
  given: {F₁ F₂ : B ⥤ C ⥤ D} (h : uncurry.obj F₁ = uncurry.obj F₂)
  proof: by
  rw [← curry_obj_uncurry_obj F₁]; rw [← curry_obj_uncurry_obj F₂]; rw [h]

中文:
引理 uncurry_obj_injective
  条件: {F₁ F₂ : B ⥤ C ⥤ D} (h : uncurry.obj F₁ = uncurry.obj F₂)
  证明: by
  rw [← curry_obj_uncurry_obj F₁]; rw [← curry_obj_uncurry_obj F₂]; rw [h]

Depends on / 依赖: curry_obj_uncurry_obj
-/
lemma uncurry_obj_injective {F₁ F₂ : B ⥤ C ⥤ D} (h : uncurry.obj F₁ = uncurry.obj F₂) :
    F₁ = F₂ := by
  rw [← curry_obj_uncurry_obj F₁]; rw [← curry_obj_uncurry_obj F₂]; rw [h]

/--
lemma `flip_flip` / 引理 `flip_flip`

English:
lemma flip_flip
  given: (F : B ⥤ C ⥤ D)
  statement: F.flip.flip = F
  proof: rfl

中文:
引理 flip_flip
  条件: (F : B ⥤ C ⥤ D)
  结论: F.flip.flip = F
  证明: rfl
-/
lemma flip_flip (F : B ⥤ C ⥤ D) : F.flip.flip = F := rfl

/--
lemma `flip_injective` / 引理 `flip_injective`

English:
lemma flip_injective
  given: {F₁ F₂ : B ⥤ C ⥤ D} (h : F₁.flip = F₂.flip)
  proof: by
  rw [← flip_flip F₁]; rw [← flip_flip F₂]; rw [h]

中文:
引理 flip_injective
  条件: {F₁ F₂ : B ⥤ C ⥤ D} (h : F₁.flip = F₂.flip)
  证明: by
  rw [← flip_flip F₁]; rw [← flip_flip F₂]; rw [h]

Depends on / 依赖: flip_flip
-/
lemma flip_injective {F₁ F₂ : B ⥤ C ⥤ D} (h : F₁.flip = F₂.flip) :
    F₁ = F₂ := by
  rw [← flip_flip F₁]; rw [← flip_flip F₂]; rw [h]

/--
lemma `uncurry_obj_curry_obj_flip_flip` / 引理 `uncurry_obj_curry_obj_flip_flip`

English:
lemma uncurry_obj_curry_obj_flip_flip
  given: (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H)
  proof: Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

中文:
引理 uncurry_obj_curry_obj_flip_flip
  条件: (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H)
  证明: Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.ext, G.map_comp, comp_id, id_comp, map_comp, prod_comp
-/
lemma uncurry_obj_curry_obj_flip_flip (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) :
    uncurry.obj (F₂ ⋙ (F₁ ⋙ curry.obj G).flip).flip = (F₁.prod F₂) ⋙ G :=
  Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

/--
lemma `uncurry_obj_curry_obj_flip_flip'` / 引理 `uncurry_obj_curry_obj_flip_flip'`

English:
lemma uncurry_obj_curry_obj_flip_flip'
  given: (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H)
  proof: Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

中文:
引理 uncurry_obj_curry_obj_flip_flip'
  条件: (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H)
  证明: Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.ext, G.map_comp, comp_id, id_comp, map_comp, prod_comp
-/
lemma uncurry_obj_curry_obj_flip_flip' (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) :
    uncurry.obj (F₁ ⋙ (F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂) ⋙ G :=
  Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

/-- Natural isomorphism witnessing `comp_flip_uncurry_eq`. -/
@[implicit_reducible, simps!]
/--
Definition of `compFlipUncurryIso` / `compFlipUncurryIso` 的定义

English:
definition compFlipUncurryIso
  signature: (F : B ⥤ D) (G : D ⥤ C ⥤ E)
  body: .refl _

中文:
定义 compFlipUncurryIso
  签名: (F : B ⥤ D) (G : D ⥤ C ⥤ E)
  定义体: .refl _
-/
def compFlipUncurryIso (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip ≅ (𝟭 C).prod F ⋙ uncurry.obj G.flip := .refl _

/--
lemma `comp_flip_uncurry_eq` / 引理 `comp_flip_uncurry_eq`

English:
lemma comp_flip_uncurry_eq
  given: (F : B ⥤ D) (G : D ⥤ C ⥤ E)
  proof: rfl

中文:
引理 comp_flip_uncurry_eq
  条件: (F : B ⥤ D) (G : D ⥤ C ⥤ E)
  证明: rfl
-/
lemma comp_flip_uncurry_eq (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip = (𝟭 C).prod F ⋙ uncurry.obj G.flip := rfl

/-- Natural isomorphism witnessing `comp_flip_curry_eq`. -/
@[implicit_reducible, simps!]
/--
Definition of `curryObjCompIso` / `curryObjCompIso` 的定义

English:
definition curryObjCompIso
  signature: (F : C × B ⥤ D) (G : D ⥤ E)
  body: .refl _

中文:
定义 curryObjCompIso
  签名: (F : C × B ⥤ D) (G : D ⥤ E)
  定义体: .refl _
-/
def curryObjCompIso (F : C × B ⥤ D) (G : D ⥤ E) :
    (curry.obj (F ⋙ G)).flip ≅ (curry.obj F).flip ⋙ (whiskeringRight _ _ _).obj G := .refl _

/--
lemma `curry_obj_comp_flip` / 引理 `curry_obj_comp_flip`

English:
lemma curry_obj_comp_flip
  given: (F : C × B ⥤ D) (G : D ⥤ E)
  proof: rfl

中文:
引理 curry_obj_comp_flip
  条件: (F : C × B ⥤ D) (G : D ⥤ E)
  证明: rfl
-/
lemma curry_obj_comp_flip (F : C × B ⥤ D) (G : D ⥤ E) :
    (curry.obj (F ⋙ G)).flip =
      (curry.obj F).flip ⋙ (whiskeringRight _ _ _).obj G := rfl

/-- The equivalence of types of bifunctors giving by flipping the arguments. -/
@[implicit_reducible, simps!]
/--
Definition of `flippingEquiv` / `flippingEquiv` 的定义

English:
definition flippingEquiv
  signature: : C ⥤ D ⥤ E ≃ D ⥤ C ⥤ E where
  body: F.flip
  invFun F := F.flip
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 flippingEquiv
  签名: : C ⥤ D ⥤ E ≃ D ⥤ C ⥤ E where
  定义体: F.flip
  invFun F := F.flip
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: F.flip
-/
def flippingEquiv : C ⥤ D ⥤ E ≃ D ⥤ C ⥤ E where
  toFun F := F.flip
  invFun F := F.flip
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence of types of bifunctors given by currying. -/
@[implicit_reducible, simps!]
/--
Definition of `curryingEquiv` / `curryingEquiv` 的定义

English:
definition curryingEquiv
  signature: : C ⥤ D ⥤ E ≃ C × D ⥤ E where
  body: uncurry.obj F
  invFun G := curry.obj G
  left_inv := curry_obj_uncurry_obj
  right_inv := uncurry_obj_curry_obj

中文:
定义 curryingEquiv
  签名: : C ⥤ D ⥤ E ≃ C × D ⥤ E where
  定义体: uncurry.obj F
  invFun G := curry.obj G
  left_inv := curry_obj_uncurry_obj
  right_inv := uncurry_obj_curry_obj

Depends on / 依赖: uncurry, uncurry.obj
-/
def curryingEquiv : C ⥤ D ⥤ E ≃ C × D ⥤ E where
  toFun F := uncurry.obj F
  invFun G := curry.obj G
  left_inv := curry_obj_uncurry_obj
  right_inv := uncurry_obj_curry_obj

/-- The flipped equivalence of types of bifunctors given by currying. -/
@[implicit_reducible, simps!]
/--
Definition of `curryingFlipEquiv` / `curryingFlipEquiv` 的定义

English:
definition curryingFlipEquiv
  signature: : D ⥤ C ⥤ E ≃ C × D ⥤ E
  body: flippingEquiv.trans curryingEquiv

中文:
定义 curryingFlipEquiv
  签名: : D ⥤ C ⥤ E ≃ C × D ⥤ E
  定义体: flippingEquiv.trans curryingEquiv

Depends on / 依赖: curryingEquiv, flippingEquiv, flippingEquiv.trans
-/
def curryingFlipEquiv : D ⥤ C ⥤ E ≃ C × D ⥤ E :=
  flippingEquiv.trans curryingEquiv

end Functor

end CategoryTheory
