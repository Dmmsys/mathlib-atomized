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
/-- The chosen terminal object in `Cat`. -/
/-
**CategoryTheory.Cat.chosenTerminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Cat`。
形式化陈述：chosenTerminal : Cat.{v, u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen terminal object in `Cat`.
-/
abbrev chosenTerminal : Cat.{v, u} := Cat.of (ULift (ULiftHom (Discrete Unit)))

attribute [local instance] uliftCategory in
/-- The chosen terminal object in `Cat` is terminal. -/
/-
**CategoryTheory.Cat.chosenTerminalIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Cat`。
形式化陈述：chosenTerminalIsTerminal : IsTerminal chosenTerminal.{v, u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen terminal object in `Cat` is terminal.
-/
def chosenTerminalIsTerminal : IsTerminal chosenTerminal.{v, u} :=
  IsTerminal.ofUniqueHom (fun C ↦ ((Functor.const C).obj ⟨⟨⟨⟩⟩⟩).toCatHom) fun _ _ ↦ rfl

set_option backward.isDefEq.respectTransparency false in
/-- The type of functors out of the chosen terminal category is equivalent to the type of objects
in the target category. TODO: upgrade to an equivalence of categories. -/
/-
**CategoryTheory.Cat.fromChosenTerminalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Cat`。
形式化陈述：fromChosenTerminalEquiv {C : Type u} [Category.{v} C] : Cat.chosenTerminal
 ⥤ C ≃ C where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of functors out of the chosen terminal category is equivalent to the ty
pe of objects
in the target category. TODO: upgrade to an equivalence of categories.
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

/-- The chosen product of categories `C × D` yields a product cone in `Cat`. -/
/-
**CategoryTheory.Cat.prodCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：prodCone (C D : Cat.{v, u}) : BinaryFan C D
参数：C D : Cat.{v, u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chosen product of categories `C × D` yields a product cone in `Cat`.
-/
def prodCone (C D : Cat.{v, u}) : BinaryFan C D :=
  .mk (P := .of (C × D)) (Prod.fst _ _).toCatHom (Prod.snd _ _).toCatHom

set_option backward.isDefEq.respectTransparency.types false in
/-- The product cone in `Cat` is indeed a product. -/
/-
**CategoryTheory.Cat.isLimitProdCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
at`。
形式化陈述：isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y)
参数：X Y : Cat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product cone in `Cat` is indeed a product.
-/
def isLimitProdCone (X Y : Cat) : IsLimit (prodCone X Y) := BinaryFan.isLimitMk
  (fun S => (S.fst.toFunctor.prod' S.snd.toFunctor).toCatHom) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h1 h2 => Cat.Hom.ext <| Functor.hext
      (fun _ ↦ Prod.ext (by simp [← h1]) (by simp [← h2]))
      (fun _ _ _ ↦ by dsimp; rw [← h1, ← h2]; rfl))
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory Cat :=
  .ofChosenFiniteProducts ⟨_, chosenTerminalIsTerminal⟩ fun X Y ↦
    { cone := X.prodCone Y, isLimit := isLimitProdCone X Y }
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory Cat := .ofCartesianMonoidalCategory

/-- A monoidal instance for `Cat` is provided from the `CartesianMonoidalCategory` instance. -/
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal instance for `Cat` is provided from the `CartesianMonoidalCategory` i
nstance.
-/
example : MonoidalCategory Cat := by infer_instance

/-- A symmetric monoidal instance for `Cat` is provided through
`CartesianMonoidalCategory.toSymmetricCategory`. -/
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A symmetric monoidal instance for `Cat` is provided through
`CartesianMonoidalCategory.toSymmetricCategory`.
-/
example : SymmetricCategory Cat := by infer_instance

end Cat

namespace Monoidal

open MonoidalCategory

/-
**CategoryTheory.Monoidal.tensorObj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
noidal`。
形式化陈述：tensorObj (C : Cat) (D : Cat) : C otimes D = Cat.of (C × D)
参数：C : Cat；D : Cat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj (C : Cat) (D : Cat) : C ⊗ D = Cat.of (C × D) := rfl
/-
**CategoryTheory.Monoidal.whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Monoidal`。
形式化陈述：whiskerLeft (X : Cat) {A : Cat} {B : Cat} (F : A ⟶ B) : X ◁ F = ((𝟭 X).pro
d F.toFunctor).toCatHom
参数：X : Cat；F : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft (X : Cat) {A : Cat} {B : Cat} (F : A ⟶ B) :
    X ◁ F = ((𝟭 X).prod F.toFunctor).toCatHom := rfl
/-
**CategoryTheory.Monoidal.whiskerLeft_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Monoidal`。
形式化陈述：whiskerLeft_fst (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) : (X ◁ f).toFunc
tor ⋙ Prod.fst _ _ = Prod.fst _ _
参数：X : Cat；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_fst (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f).toFunctor ⋙ Prod.fst _ _ = Prod.fst _ _ := rfl
/-
**CategoryTheory.Monoidal.whiskerLeft_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Monoidal`。
形式化陈述：whiskerLeft_snd (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) : (X ◁ f).toFunc
tor ⋙ Prod.snd _ _ = Prod.snd _ _ ⋙ f.toFunctor
参数：X : Cat；f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_snd (X : Cat) {A : Cat} {B : Cat} (f : A ⟶ B) :
    (X ◁ f).toFunctor ⋙ Prod.snd _ _ = Prod.snd _ _ ⋙ f.toFunctor := rfl
/-
**CategoryTheory.Monoidal.whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Monoidal`。
形式化陈述：whiskerRight {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) : f ▷ X = (f.toFunc
tor.prod (𝟭 X)).toCatHom
参数：f : A ⟶ B；X : Cat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    f ▷ X = (f.toFunctor.prod (𝟭 X)).toCatHom := rfl
/-
**CategoryTheory.Monoidal.whiskerRight_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Monoidal`。
形式化陈述：whiskerRight_fst {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) : (f ▷ X).toFun
ctor ⋙ Prod.fst _ _ = Prod.fst _ _ ⋙ f.toFunctor
参数：f : A ⟶ B；X : Cat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_fst {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X).toFunctor ⋙ Prod.fst _ _ = Prod.fst _ _ ⋙ f.toFunctor := rfl
/-
**CategoryTheory.Monoidal.whiskerRight_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Monoidal`。
形式化陈述：whiskerRight_snd {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) : (f ▷ X).toFun
ctor ⋙ Prod.snd _ _ = Prod.snd _ _
参数：f : A ⟶ B；X : Cat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_snd {A : Cat} {B : Cat} (f : A ⟶ B) (X : Cat) :
    (f ▷ X).toFunctor ⋙ Prod.snd _ _ = Prod.snd _ _ := rfl
/-
**CategoryTheory.Monoidal.tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
noidal`。
形式化陈述：tensorHom {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y) 
: f otimesₘ g = (f.toFunctor.prod g.toFunctor).toCatHom
参数：f : A ⟶ B；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom {A : Cat} {B : Cat} (f : A ⟶ B) {X : Cat} {Y : Cat} (g : X ⟶ Y) :
    f ⊗ₘ g = (f.toFunctor.prod g.toFunctor).toCatHom := rfl
/-
**CategoryTheory.Monoidal.tensorUnit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.M
onoidal`。
形式化陈述：tensorUnit : 𝟙_ Cat = Cat.chosenTerminal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit : 𝟙_ Cat = Cat.chosenTerminal := rfl
/-
**CategoryTheory.Monoidal.associator_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Monoidal`。
形式化陈述：associator_hom (X : Cat) (Y : Cat) (Z : Cat) : (associator X Y Z).hom = (F
unctor.prod' (Prod.fst (X × Y) Z ⋙ Prod.fst X Y) ((Functor.prod' ((Prod.fst (X ×
 Y) Z ⋙ Prod.snd X Y)) (Prod.snd (X × Y) Z : (X × Y) × Z ⥤ Z)))).toCatHom
参数：X : Cat；Y : Cat；Z : Cat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_hom (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).hom = (Functor.prod' (Prod.fst (X × Y) Z ⋙ Prod.fst X Y)
      ((Functor.prod' ((Prod.fst (X × Y) Z ⋙ Prod.snd X Y))
      (Prod.snd (X × Y) Z : (X × Y) × Z ⥤ Z)))).toCatHom := rfl
/-
**CategoryTheory.Monoidal.associator_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Monoidal`。
形式化陈述：associator_inv (X : Cat) (Y : Cat) (Z : Cat) : (associator X Y Z).inv = (F
unctor.prod' (Functor.prod' (Prod.fst X (Y × Z) : X × (Y × Z) ⥤ X) (Prod.snd X (
Y × Z) ⋙ Prod.fst Y Z)) (Prod.snd X (Y × Z) ⋙ Prod.snd Y Z)).toCatHom
参数：X : Cat；Y : Cat；Z : Cat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_inv (X : Cat) (Y : Cat) (Z : Cat) :
    (associator X Y Z).inv = (Functor.prod' (Functor.prod' (Prod.fst X (Y × Z) : X × (Y × Z) ⥤ X)
      (Prod.snd X (Y × Z) ⋙ Prod.fst Y Z)) (Prod.snd X (Y × Z) ⋙ Prod.snd Y Z)).toCatHom := rfl
/-
**CategoryTheory.Monoidal.leftUnitor_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Monoidal`。
形式化陈述：leftUnitor_hom (C : Cat.{v, u}) : (fun_ C).hom = (Prod.snd _ _).toCatHom
参数：C : Cat.{v, u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom (C : Cat.{v, u}) : (λ_ C).hom = (Prod.snd _ _).toCatHom := rfl
/-
**CategoryTheory.Monoidal.leftUnitor_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Monoidal`。
形式化陈述：leftUnitor_inv (C : Cat.{v, u}) : (fun_ C).inv = (Prod.sectR ⟨⟨⟨⟩⟩⟩ _).toC
atHom
参数：C : Cat.{v, u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_inv (C : Cat.{v, u}) : (λ_ C).inv = (Prod.sectR ⟨⟨⟨⟩⟩⟩ _).toCatHom := rfl
/-
**CategoryTheory.Monoidal.rightUnitor_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Monoidal`。
形式化陈述：rightUnitor_hom (C : Cat.{v, u}) : (ρ_ C).hom = (Prod.fst _ _).toCatHom
参数：C : Cat.{v, u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom (C : Cat.{v, u}) : (ρ_ C).hom = (Prod.fst _ _).toCatHom := rfl
/-
**CategoryTheory.Monoidal.rightUnitor_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Monoidal`。
形式化陈述：rightUnitor_inv (C : Cat.{v, u}) : (ρ_ C).inv = (Prod.sectL _ ⟨⟨⟨⟩⟩⟩).toCa
tHom
参数：C : Cat.{v, u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_inv (C : Cat.{v, u}) : (ρ_ C).inv = (Prod.sectL _ ⟨⟨⟨⟩⟩⟩).toCatHom := rfl

end CategoryTheory.Monoidal

