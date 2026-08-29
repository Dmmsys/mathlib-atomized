/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
/-!
# Chosen finite products in `Cat`

This file proves that the Cartesian product of a pair of categories agrees with the
product in `Cat`, and provides the associated `CartesianMonoidalCategory` instance.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Cat

open Limits

attribute [local instance] uliftCategory in
/--
Definition of `chosenTerminal` / `chosenTerminal` 的定义

English:
abbreviation chosenTerminal
  signature: : Cat.{v, u}
  body: Cat.of (ULift (ULiftHom (Discrete Unit)))

中文:
缩写 chosenTerminal
  签名: : Cat.{v, u}
  定义体: Cat.of (ULift (ULiftHom (Discrete Unit)))

Depends on / 依赖: Cat.of, Discrete, ULiftHom
-/
abbrev chosenTerminal : Cat.{v, u} := Cat.of (ULift (ULiftHom (Discrete Unit)))

attribute [local instance] uliftCategory in
/--
Definition of `chosenTerminalIsTerminal` / `chosenTerminalIsTerminal` 的定义

English:
definition chosenTerminalIsTerminal
  signature: : IsTerminal chosenTerminal.{v, u}
  body: IsTerminal.ofUniqueHom (fun C => ((Functor.const C).obj ⟨⟨⟨⟩⟩⟩).toCatHom) fun _ _ => rfl

中文:
定义 chosenTerminalIsTerminal
  签名: : IsTerminal chosenTerminal.{v, u}
  定义体: IsTerminal.ofUniqueHom (fun C => ((Functor.const C).obj ⟨⟨⟨⟩⟩⟩).toCatHom) fun _ _ => rfl

Depends on / 依赖: Functor, Functor.const, IsTerminal, IsTerminal.ofUniqueHom, ofUniqueHom, toCatHom
-/
def chosenTerminalIsTerminal : IsTerminal chosenTerminal.{v, u} :=
  IsTerminal.ofUniqueHom (fun C => ((Functor.const C).obj ⟨⟨⟨⟩⟩⟩).toCatHom) fun _ _ => rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromChosenTerminalEquiv` / `fromChosenTerminalEquiv` 的定义

English:
definition fromChosenTerminalEquiv
  signature: {C : Type u} [Category.{v} C]
  body: F.obj ⟨⟨()⟩⟩
  invFun := (Functor.const _).obj
  left_inv _ := by
    apply Functor.ext
    · rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact (Functor.map_id _ _).symm
    · intro; rfl
  right_inv _ := rfl

中文:
定义 fromChosenTerminalEquiv
  签名: {C : 类型u} [Category.{v} C]
  定义体: F.obj ⟨⟨()⟩⟩
  invFun := (Functor.const _).obj
  left_inv _ := by
    apply Functor.ext
    · rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact (Functor.map_id _ _).symm
    · intro; rfl
  right_inv _ := rfl

Depends on / 依赖: F.obj
-/
def fromChosenTerminalEquiv {C : Type u} [Category.{v} C] : Cat.chosenTerminal ⥤ C ≃ C where
  toFun F := F.obj ⟨⟨()⟩⟩
  invFun := (Functor.const _).obj
  left_inv _ := by
    apply Functor.ext
    · rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟨⟩⟩⟩⟩
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact (Functor.map_id _ _).symm
    · intro; rfl
  right_inv _ := rfl

/--
Definition of `prodCone` / `prodCone` 的定义

English:
definition prodCone
  signature: (C D : Cat.{v, u})
  body: .mk (P := .of (C × D)) (Prod.fst _ _).toCatHom (Prod.snd _ _).toCatHom

中文:
定义 prodCone
  签名: (C D : Cat.{v, u})
  定义体: .mk (P := .of (C × D)) (Prod.fst _ _).toCatHom (Prod.snd _ _).toCatHom

Depends on / 依赖: Prod.fst, Prod.snd, toCatHom
-/
def prodCone (C D : Cat.{v, u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _).toCatHom (Prod.snd _ _).toCatHom

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLimitProdCone` / `isLimitProdCone` 的定义

English:
definition isLimitProdCone
  signature: (X Y : Cat)
  body: BinaryFan.isLimitMk
  (fun S => (S.fst.toFunctor.prod' S.snd.toFunctor).toCatHom) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h1 h2 => Cat.Hom.ext <| Functor.hext
      (fun _ => Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ => by dsimp; rw [← h1, ← h2]; rfl))

中文:
定义 isLimitProdCone
  签名: (X Y : Cat)
  定义体: BinaryFan.isLimitMk
  (fun S => (S.fst.toFunctor.prod' S.snd.toFunctor).toCatHom) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h1 h2 => Cat.Hom.ext <| Functor.hext
      (fun _ => Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ => by dsimp; rw [← h1, ← h2]; rfl))

Depends on / 依赖: BinaryFan, BinaryFan.isLimitMk, isLimitMk
-/
def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => (S.fst.toFunctor.prod' S.snd.toFunctor).toCatHom) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h1 h2 => Cat.Hom.ext <| Functor.hext
      (fun _ => Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ => by dsimp; rw [← h1, ← h2]; rfl))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CartesianMonoidalCategory Cat
  body: .ofChosenFiniteProducts ⟨_, chosenTerminalIsTerminal⟩ fun X Y =>
    { cone := X.prodCone Y, isLimit := isLimitProdCone X Y }

中文:
实例 :
  签名: CartesianMonoidalCategory Cat
  定义体: .ofChosenFiniteProducts ⟨_, chosenTerminalIsTerminal⟩ fun X Y =>
    { cone := X.prodCone Y, isLimit := isLimitProdCone X Y }

Depends on / 依赖: X.prodCone, chosenTerminalIsTerminal, isLimit, isLimitProdCone, ofChosenFiniteProducts, prodCone
-/
instance : CartesianMonoidalCategory Cat :=
  .ofChosenFiniteProducts ⟨_, chosenTerminalIsTerminal⟩ fun X Y =>
    { cone := X.prodCone Y, isLimit := isLimitProdCone X Y }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory Cat
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: BraidedCategory Cat
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
instance : BraidedCategory Cat := .ofCartesianMonoidalCategory

/-- A monoidal instance for `Cat` is provided from the `CartesianMonoidalCategory` instance. -/
example : MonoidalCategory Cat := by infer_instance

/-- A symmetric monoidal instance for `Cat` is provided through
`CartesianMonoidalCategory.toSymmetricCategory`. -/
example : SymmetricCategory Cat := by infer_instance

end Cat

namespace Monoidal

open MonoidalCategory

/--
lemma `tensorObj` / 引理 `tensorObj`

English:
lemma tensorObj
  given: (C : Cat) (D : Cat)
  statement: C otimes D = Cat.of (C × D)
  proof: rfl

中文:
引理 tensorObj
  条件: (C : Cat) (D : Cat)
  结论: C otimes D = Cat.of (C × D)
  证明: rfl
-/
lemma tensorObj (C : Cat) (D : Cat) : C otimes D = Cat.of (C × D) := rfl

/--
lemma `whiskerLeft` / 引理 `whiskerLeft`

English:
lemma whiskerLeft
  given: (X : Cat) {A : Cat} {B : Cat} (F : A ⟶ B)
  proof: rfl

中文:
引理 whiskerLeft
  条件: (X : Cat) {A : Cat} {B : Cat} (F : A ⟶ B)
  证明: rfl
-/
lemma whiskerLeft (X : Cat) {A : Cat} {B : Cat} (F : A ⟶ B) :
    X ◁ F = ((𝟭 X).prod F.toFunctor).toCatHom := rfl

/--
lemma `whiskerLeft_fst` / 引理 `whiskerLeft_fst`

English:
lemma whiskerLeft_fst
  given: (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B)
  proof: rfl

中文:
引理 whiskerLeft_fst
  条件: (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B)
  证明: rfl
-/
lemma whiskerLeft_fst (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f).toFunctor ⋙ Prod.fst _ _ = Prod.fst _ _ := rfl

/--
lemma `whiskerLeft_snd` / 引理 `whiskerLeft_snd`

English:
lemma whiskerLeft_snd
  given: (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B)
  proof: rfl

中文:
引理 whiskerLeft_snd
  条件: (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B)
  证明: rfl
-/
lemma whiskerLeft_snd (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f).toFunctor ⋙ Prod.snd _ _ = Prod.snd _ _ ⋙ f.toFunctor := rfl

/--
lemma `whiskerRight` / 引理 `whiskerRight`

English:
lemma whiskerRight
  given: {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat)
  proof: rfl

中文:
引理 whiskerRight
  条件: {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat)
  证明: rfl
-/
lemma whiskerRight {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    f ▷ X = (f.toFunctor.prod (𝟭 X)).toCatHom := rfl

/--
lemma `whiskerRight_fst` / 引理 `whiskerRight_fst`

English:
lemma whiskerRight_fst
  given: {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat)
  proof: rfl

中文:
引理 whiskerRight_fst
  条件: {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat)
  证明: rfl
-/
lemma whiskerRight_fst {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X).toFunctor ⋙ Prod.fst _ _ = Prod.fst _ _ ⋙ f.toFunctor := rfl

/--
lemma `whiskerRight_snd` / 引理 `whiskerRight_snd`

English:
lemma whiskerRight_snd
  given: {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat)
  proof: rfl

中文:
引理 whiskerRight_snd
  条件: {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat)
  证明: rfl
-/
lemma whiskerRight_snd {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X).toFunctor ⋙ Prod.snd _ _ = Prod.snd _ _ := rfl

/--
lemma `tensorHom` / 引理 `tensorHom`

English:
lemma tensorHom
  given: {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y)
  proof: rfl

中文:
引理 tensorHom
  条件: {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y)
  证明: rfl
-/
lemma tensorHom {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y) :
    f otimesₘ g = (f.toFunctor.prod g.toFunctor).toCatHom := rfl

/--
lemma `tensorUnit` / 引理 `tensorUnit`

English:
lemma tensorUnit
  statement: 𝟙_ Cat = Cat.chosenTerminal
  proof: rfl

中文:
引理 tensorUnit
  结论: 𝟙_ Cat = Cat.chosenTerminal
  证明: rfl
-/
lemma tensorUnit : 𝟙_ Cat = Cat.chosenTerminal := rfl

/--
lemma `associator_hom` / 引理 `associator_hom`

English:
lemma associator_hom
  given: (X : Cat) (Y : Cat) (Z : Cat)
  proof: rfl

中文:
引理 associator_hom
  条件: (X : Cat) (Y : Cat) (Z : Cat)
  证明: rfl
-/
lemma associator_hom (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).hom = (Functor.prod' (Prod.fst (X × Y) Z ⋙ Prod.fst X Y)
      ((Functor.prod' ((Prod.fst (X × Y) Z ⋙ Prod.snd X Y))
      (Prod.snd (X × Y) Z : (X × Y) × Z ⥤ Z)))).toCatHom := rfl

/--
lemma `associator_inv` / 引理 `associator_inv`

English:
lemma associator_inv
  given: (X : Cat) (Y : Cat) (Z : Cat)
  proof: rfl

中文:
引理 associator_inv
  条件: (X : Cat) (Y : Cat) (Z : Cat)
  证明: rfl
-/
lemma associator_inv (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).inv = (Functor.prod' (Functor.prod' (Prod.fst X (Y × Z) : X × (Y × Z) ⥤ X)
      (Prod.snd X (Y × Z) ⋙ Prod.fst Y Z)) (Prod.snd X (Y × Z) ⋙ Prod.snd Y Z)).toCatHom := rfl

/--
lemma `leftUnitor_hom` / 引理 `leftUnitor_hom`

English:
lemma leftUnitor_hom
  given: (C : Cat.{v, u})
  statement: (fun_ C).hom = (Prod.snd _ _).toCatHom
  proof: rfl

中文:
引理 leftUnitor_hom
  条件: (C : Cat.{v, u})
  结论: (fun_ C).hom = (Prod.snd _ _).toCatHom
  证明: rfl
-/
lemma leftUnitor_hom (C : Cat.{v, u}) : (fun_ C).hom = (Prod.snd _ _).toCatHom := rfl

/--
lemma `leftUnitor_inv` / 引理 `leftUnitor_inv`

English:
lemma leftUnitor_inv
  given: (C : Cat.{v, u})
  statement: (fun_ C).inv = (Prod.sectR ⟨⟨⟨⟩⟩⟩ _).toCatHom
  proof: rfl

中文:
引理 leftUnitor_inv
  条件: (C : Cat.{v, u})
  结论: (fun_ C).inv = (Prod.sectR ⟨⟨⟨⟩⟩⟩ _).toCatHom
  证明: rfl
-/
lemma leftUnitor_inv (C : Cat.{v, u}) : (fun_ C).inv = (Prod.sectR ⟨⟨⟨⟩⟩⟩ _).toCatHom := rfl

/--
lemma `rightUnitor_hom` / 引理 `rightUnitor_hom`

English:
lemma rightUnitor_hom
  given: (C : Cat.{v, u})
  statement: (ρ_ C).hom = (Prod.fst _ _).toCatHom
  proof: rfl

中文:
引理 rightUnitor_hom
  条件: (C : Cat.{v, u})
  结论: (ρ_ C).hom = (Prod.fst _ _).toCatHom
  证明: rfl

Depends on / 依赖: infer_instance, isIso_iff_of_reflects_iso, sheafToPresheaf, sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv
-/
lemma rightUnitor_hom (C : Cat.{v, u}) : (ρ_ C).hom = (Prod.fst _ _).toCatHom := rfl

/--
lemma `rightUnitor_inv` / 引理 `rightUnitor_inv`

English:
lemma rightUnitor_inv
  given: (C : Cat.{v, u})
  statement: (ρ_ C).inv = (Prod.sectL _ ⟨⟨⟨⟩⟩⟩).toCatHom
  proof: rfl

中文:
引理 rightUnitor_inv
  条件: (C : Cat.{v, u})
  结论: (ρ_ C).inv = (Prod.sectL _ ⟨⟨⟨⟩⟩⟩).toCatHom
  证明: rfl
-/
lemma rightUnitor_inv (C : Cat.{v, u}) : (ρ_ C).inv = (Prod.sectL _ ⟨⟨⟨⟩⟩⟩).toCatHom := rfl

end CategoryTheory.Monoidal
