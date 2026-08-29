/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Trifunctor
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensorObj : C → C → C`
* `tensorHom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`

and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `leftUnitor_nat_iso`, `rightUnitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files after proving the coherence theorem,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `CategoryTheory.Monoidal.CoherenceLemmas`.

## Implementation notes

In the definition of monoidal categories, we also provide the whiskering operators:
* `whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⊗ Y₁ ⟶ X ⊗ Y₂`, denoted by `X ◁ f`,
* `whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : X₁ ⊗ Y ⟶ X₂ ⊗ Y`, denoted by `f ▷ Y`.

These are products of an object and a morphism (the terminology "whiskering"
is borrowed from 2-category theory). The tensor product of morphisms `tensorHom` can be defined
in terms of the whiskerings. There are two possible such definitions, which are related by
the exchange property of the whiskerings. These two definitions are accessed by `tensorHom_def`
and `tensorHom_def'`. By default, `tensorHom` is defined so that `tensorHom_def` holds
definitionally.

If you want to provide `tensorHom` and define `whiskerLeft` and `whiskerRight` in terms of it,
you can use the alternative constructor `CategoryTheory.MonoidalCategory.ofTensorHom`.

The whiskerings are useful when considering simp-normal forms of morphisms in monoidal categories.

### Simp-normal form for morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any morphisms into the simp-normal
form defined below. Rewriting into simp-normal form is especially useful in preprocessing
performed by the `coherence` tactic.

The simp-normal form of morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of morphisms like `f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅` such that each `fᵢ` is
  either a structural morphism (morphisms made up only of identities, associators, unitors)
  or a non-structural morphism, and
2. each non-structural morphism in the composition is of the form `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅`,
  where each `Xᵢ` is an object that is not the identity or a tensor and `f` is a non-structural
  morphism that is not the identity or a composite.

Note that `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅` is actually `X₁ ◁ (X₂ ◁ (X₃ ◁ ((f ▷ X₄) ▷ X₅)))`.

Currently, the simp lemmas don't rewrite `𝟙 X ⊗ₘ f` and `f ⊗ₘ 𝟙 Y` into `X ◁ f` and `f ▷ Y`,
respectively, since it requires a huge refactoring. We hope to add these simp lemmas soon.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/

@[expose] public section

universe v u

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

/--
Definition of `MonoidalCategoryStruct` / `MonoidalCategoryStruct` 的定义

English:
class MonoidalCategoryStruct
  parameters: (C : Type u) [𝒞 : Category.{v} C]
  axioms and operations (8):
    - tensorObj : C -> C -> C
    - whiskerLeft((X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂)) : tensorObj X Y₁ ⟶ tensorObj X Y₂
    - whiskerRight({X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
    - tensorHom({X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂)  [default: whiskerRight f X₂ ≫ whiskerLeft Y₁ g]
    - tensorUnit((C)) : C
    - associator : forall X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
    - leftUnitor : forall X : C, tensorObj tensorUnit X ≅ X
    - rightUnitor : forall X : C, tensorObj X tensorUnit ≅ X

中文:
类 幺半群范畴结构
  参数: (C : 类型u) [𝒞 : 范畴.{v} C]
  公理与运算 (8 个):
    - tensorObj : C -> C -> C
    - whiskerLeft((X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂)) : tensorObj X Y₁ ⟶ tensorObj X Y₂
    - whiskerRight({X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
    - tensorHom({X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂)  [默认: whiskerRight f X₂ ≫ whiskerLeft Y₁ g]
    - tensorUnit((C)) : C
    - associator : 对任意 X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
    - leftUnitor : 对任意 X : C, tensorObj tensorUnit X ≅ X
    - rightUnitor : 对任意 X : C, tensorObj X tensorUnit ≅ X

Depends on / 依赖: whiskerLeft, whiskerRight
-/
class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C -> C -> C
  /-- left whiskering for morphisms -/
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  /-- right whiskering for morphisms -/
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  /-- The tensor unity in the monoidal structure `𝟙_ C` -/
  tensorUnit (C) : C
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : forall X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : forall X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : forall X : C, tensorObj X tensorUnit ≅ X

namespace MonoidalCategory

export MonoidalCategoryStruct
  (tensorObj whiskerLeft whiskerRight tensorHom tensorUnit associator leftUnitor rightUnitor)

end MonoidalCategory

namespace MonoidalCategory

/-- Notation for `tensorObj`, the tensor product of objects in a monoidal category -/
scoped infixr:70 " otimes " => MonoidalCategoryStruct.tensorObj

/-- Notation for the `whiskerLeft` operator of monoidal categories -/
scoped infixr:81 " ◁ " => MonoidalCategoryStruct.whiskerLeft

/-- Notation for the `whiskerRight` operator of monoidal categories -/
scoped infixl:81 " ▷ " => MonoidalCategoryStruct.whiskerRight

/-- Notation for `tensorHom`, the tensor product of morphisms in a monoidal category -/
scoped infixr:70 " otimesₘ " => MonoidalCategoryStruct.tensorHom
-- TODO: Try setting this notation to `⊗` if the elaborator is improved and performs
-- better than currently on overloaded notations.

/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
scoped notation "𝟙_ " C:arg => MonoidalCategoryStruct.tensorUnit C

/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
scoped notation "α_" => MonoidalCategoryStruct.associator

/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
scoped notation "fun_" => MonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

/--
Definition of `Pentagon` / `Pentagon` 的定义

English:
definition Pentagon
  signature: {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
  body: (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ otimes Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ otimes Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ otimes Y₄)).hom

中文:
定义 Pentagon
  签名: {C : 类型u} [范畴.{v} C] [幺半群范畴结构 C]
  定义体: (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ otimes Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ otimes Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ otimes Y₄)).hom

Depends on / 依赖: otimes
-/
def Pentagon {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ otimes Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ otimes Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ otimes Y₄)).hom

end MonoidalCategory

open MonoidalCategory

/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms
`f ⊗ₘ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations. -/
@[stacks 0FFK, wikidata Q1945014]
-- Porting note: The Mathport did not translate the temporary notation
/--
Definition of `MonoidalCategory` / `MonoidalCategory` 的定义

English:
class MonoidalCategory
  parameters: (C : Type u) [𝒞 : Category.{v} C]
  extends: MonoidalCategoryStruct C
  axioms and operations (10):
    - tensorHom_def({X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)) : f otimesₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g)  [default: by cat_disch]
    - id_tensorHom_id : forall X₁ X₂ : C, 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 (X₁ otimes X₂)  [default: by cat_disch]
    - tensorHom_comp_tensorHom : forall {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂), (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂)  [default: by cat_disch]
    - whiskerLeft_id : forall (X Y : C), X ◁ 𝟙 Y = 𝟙 (X otimes Y)  [default: by cat_disch]
    - id_whiskerRight : forall (X Y : C), 𝟙 X ▷ Y = 𝟙 (X otimes Y)  [default: by cat_disch]
    - associator_naturality : forall {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃), ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ (f₂ otimesₘ f₃))  [default: by cat_disch]
    - leftUnitor_naturality : forall {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (fun_ Y).hom = (fun_ X).hom ≫ f  [default: by cat_disch]
    - rightUnitor_naturality : forall {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f  [default: by cat_disch]
    - pentagon : forall W X Y Z : C, (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otimes Z)).hom  [default: by cat_disch]
    - triangle : forall X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (fun_ Y).hom = (ρ_ X).hom ▷ Y  [default: by cat_disch]

中文:
类 幺半群范畴
  参数: (C : 类型u) [𝒞 : 范畴.{v} C]
  继承: 幺半群范畴结构 C
  公理与运算 (10 个):
    - tensorHom_def({X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)) : f otimesₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g)  [默认: by cat_disch]
    - id_tensorHom_id : 对任意 X₁ X₂ : C, 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 (X₁ otimes X₂)  [默认: by cat_disch]
    - tensorHom_comp_tensorHom : 对任意 {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂), (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂)  [默认: by cat_disch]
    - whiskerLeft_id : 对任意 (X Y : C), X ◁ 𝟙 Y = 𝟙 (X otimes Y)  [默认: by cat_disch]
    - id_whiskerRight : 对任意 (X Y : C), 𝟙 X ▷ Y = 𝟙 (X otimes Y)  [默认: by cat_disch]
    - associator_naturality : 对任意 {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃), ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ (f₂ otimesₘ f₃))  [默认: by cat_disch]
    - leftUnitor_naturality : 对任意 {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (fun_ Y).hom = (fun_ X).hom ≫ f  [默认: by cat_disch]
    - rightUnitor_naturality : 对任意 {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f  [默认: by cat_disch]
    - pentagon : 对任意 W X Y Z : C, (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otimes Z)).hom  [默认: by cat_disch]
    - triangle : 对任意 X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (fun_ Y).hom = (ρ_ X).hom ▷ Y  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f otimesₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      cat_disch
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/
  id_tensorHom_id : forall X₁ X₂ : C, 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 (X₁ otimes X₂) := by cat_disch
  /--
  Composition of tensor products is tensor product of compositions:
  `(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)`
  -/
  tensorHom_comp_tensorHom :
    forall {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂) := by
    cat_disch
  whiskerLeft_id : forall (X Y : C), X ◁ 𝟙 Y = 𝟙 (X otimes Y) := by
    cat_disch
  id_whiskerRight : forall (X Y : C), 𝟙 X ▷ Y = 𝟙 (X otimes Y) := by
    cat_disch
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ₘ f₂) ⊗ₘ f₃ ≃ f₁ ⊗ₘ (f₂ ⊗ₘ f₃)` -/
  associator_naturality :
    forall {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ (f₂ otimesₘ f₃)) := by
    cat_disch
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    forall {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (fun_ Y).hom = (fun_ X).hom ≫ f := by
    cat_disch
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    forall {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
    cat_disch
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    forall W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otimes Z)).hom := by
    cat_disch
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    forall X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (fun_ Y).hom = (ρ_ X).hom ▷ Y := by
    cat_disch

attribute [reassoc] MonoidalCategory.tensorHom_def
attribute [reassoc, simp] MonoidalCategory.whiskerLeft_id
attribute [reassoc, simp] MonoidalCategory.id_whiskerRight
attribute [reassoc (attr := simp)] MonoidalCategory.tensorHom_comp_tensorHom
attribute [reassoc] MonoidalCategory.associator_naturality
attribute [reassoc] MonoidalCategory.leftUnitor_naturality
attribute [reassoc] MonoidalCategory.rightUnitor_naturality
attribute [reassoc (attr := simp)] MonoidalCategory.pentagon
attribute [reassoc (attr := simp)] MonoidalCategory.triangle

namespace MonoidalCategory

/--
Definition of `ofTensorHom` / `ofTensorHom` 的定义

English:
abbreviation ofTensorHom
  signature: {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
  body: by intros; simp [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← id_tensorHom_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, id_tensorHom_id]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]
  triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle]

中文:
缩写 ofTensorHom
  签名: {C : 类型u} [范畴.{v} C] [幺半群范畴结构 C]
  定义体: by intros; simp [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← id_tensorHom_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, id_tensorHom_id]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]
  triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle]

Depends on / 依赖: associator_naturality, cat_disch, id_tensorHom, tensorHom, tensorHom_comp_tensorHom, tensorHom_id, whiskerLeft, whiskerRight
-/
abbrev ofTensorHom {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (id_tensorHom_id : forall X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
      cat_disch)
    (id_tensorHom : forall (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), tensorHom (𝟙 X) f = whiskerLeft X f := by
      cat_disch)
    (tensorHom_id : forall {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), tensorHom f (𝟙 Y) = whiskerRight f Y := by
      cat_disch)
    (tensorHom_comp_tensorHom :
      forall {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂) := by
          cat_disch)
    (associator_naturality :
      forall {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
            cat_disch)
    (leftUnitor_naturality :
      forall {X Y : C} (f : X ⟶ Y),
        tensorHom (𝟙 (𝟙_ C)) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
          cat_disch)
    (rightUnitor_naturality :
      forall {X Y : C} (f : X ⟶ Y),
        tensorHom f (𝟙 (𝟙_ C)) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
          cat_disch)
    (pentagon :
      forall W X Y Z : C,
        tensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
            cat_disch)
    (triangle :
      forall X Y : C,
        (associator X (𝟙_ C) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
          tensorHom (rightUnitor X).hom (𝟙 Y) := by
            cat_disch) :
      MonoidalCategory C where
  tensorHom_def := by intros; simp [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
  whiskerLeft_id := by intros; simp [← id_tensorHom, ← id_tensorHom_id]
  id_whiskerRight := by intros; simp [← tensorHom_id, id_tensorHom_id]
  pentagon := by intros; simp [← id_tensorHom, ← tensorHom_id, pentagon]
  triangle := by intros; simp [← id_tensorHom, ← tensorHom_id, triangle]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

@[simp]
/--
theorem `id_tensorHom` / 定理 `id_tensorHom`

English:
theorem id_tensorHom
  given: (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂)
  proof: by
  simp [tensorHom_def]

@[simp]

中文:
定理 id_tensorHom
  条件: (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂)
  证明: by
  simp [tensorHom_def]

@[simp]

Depends on / 依赖: tensorHom_def
-/
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X otimesₘ f = X ◁ f := by
  simp [tensorHom_def]

@[simp]
/--
theorem `tensorHom_id` / 定理 `tensorHom_id`

English:
theorem tensorHom_id
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  proof: by
  simp [tensorHom_def]

@[reassoc, simp]

中文:
定理 tensorHom_id
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  证明: by
  simp [tensorHom_def]

@[reassoc, simp]

Depends on / 依赖: tensorHom_def
-/
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f otimesₘ 𝟙 Y = f ▷ Y := by
  simp [tensorHom_def]

@[reassoc, simp]
/--
theorem `whiskerLeft_comp` / 定理 `whiskerLeft_comp`

English:
theorem whiskerLeft_comp
  given: (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  simp [← id_tensorHom]

@[reassoc, simp]

中文:
定理 whiskerLeft_comp
  条件: (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  simp [← id_tensorHom]

@[reassoc, simp]

Depends on / 依赖: id_tensorHom
-/
theorem whiskerLeft_comp (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g := by
  simp [← id_tensorHom]

@[reassoc, simp]
/--
theorem `id_whiskerLeft` / 定理 `id_whiskerLeft`

English:
theorem id_whiskerLeft
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← assoc]; rw [← leftUnitor_naturality]; simp

@[reassoc, simp]

中文:
定理 id_whiskerLeft
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← assoc]; rw [← leftUnitor_naturality]; simp

@[reassoc, simp]

Depends on / 依赖: leftUnitor_naturality
-/
theorem id_whiskerLeft {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv := by
  rw [← assoc]; rw [← leftUnitor_naturality]; simp

@[reassoc, simp]
/--
theorem `tensor_whiskerLeft` / 定理 `tensor_whiskerLeft`

English:
theorem tensor_whiskerLeft
  given: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  proof: by
  simp only [← id_tensorHom]
  rw [← assoc]; rw [← associator_naturality]
  simp

@[reassoc, simp]

中文:
定理 tensor_whiskerLeft
  条件: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  证明: by
  simp only [← id_tensorHom]
  rw [← assoc]; rw [← associator_naturality]
  simp

@[reassoc, simp]

Depends on / 依赖: associator_naturality, id_tensorHom
-/
theorem tensor_whiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f ≫ (α_ X Y Z').inv := by
  simp only [← id_tensorHom]
  rw [← assoc]; rw [← associator_naturality]
  simp

@[reassoc, simp]
/--
theorem `comp_whiskerRight` / 定理 `comp_whiskerRight`

English:
theorem comp_whiskerRight
  given: {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C)
  proof: by
  simp [← tensorHom_id]

@[reassoc, simp]

中文:
定理 comp_whiskerRight
  条件: {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C)
  证明: by
  simp [← tensorHom_id]

@[reassoc, simp]

Depends on / 依赖: tensorHom_id
-/
theorem comp_whiskerRight {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) :
    (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z := by
  simp [← tensorHom_id]

@[reassoc, simp]
/--
theorem `whiskerRight_id` / 定理 `whiskerRight_id`

English:
theorem whiskerRight_id
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← assoc]; rw [← rightUnitor_naturality]; simp

@[reassoc, simp]

中文:
定理 whiskerRight_id
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← assoc]; rw [← rightUnitor_naturality]; simp

@[reassoc, simp]

Depends on / 依赖: rightUnitor_naturality
-/
theorem whiskerRight_id {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← assoc]; rw [← rightUnitor_naturality]; simp

@[reassoc, simp]
/--
theorem `whiskerRight_tensor` / 定理 `whiskerRight_tensor`

English:
theorem whiskerRight_tensor
  given: {X X' : C} (f : X ⟶ X') (Y Z : C)
  proof: by
  simp only [← tensorHom_id]
  rw [associator_naturality]
  simp

@[reassoc, simp]

中文:
定理 whiskerRight_tensor
  条件: {X X' : C} (f : X ⟶ X') (Y Z : C)
  证明: by
  simp only [← tensorHom_id]
  rw [associator_naturality]
  simp

@[reassoc, simp]

Depends on / 依赖: associator_naturality, tensorHom_id
-/
theorem whiskerRight_tensor {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom := by
  simp only [← tensorHom_id]
  rw [associator_naturality]
  simp

@[reassoc, simp]
/--
theorem `whisker_assoc` / 定理 `whisker_assoc`

English:
theorem whisker_assoc
  given: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  proof: by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc]; rw [← associator_naturality]
  simp

@[reassoc]

中文:
定理 whisker_assoc
  条件: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  证明: by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc]; rw [← associator_naturality]
  simp

@[reassoc]

Depends on / 依赖: HasPairwisePullbacks, Presieve, Presieve.HasPairwisePullbacks.has_pullbacks, Presieve.ofArrows.mk, associator_naturality, has_pullbacks, id_tensorHom, ofArrows, tensorHom_id
-/
theorem whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X Y' Z).inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc]; rw [← associator_naturality]
  simp

@[reassoc]
/--
theorem `whisker_exchange` / 定理 `whisker_exchange`

English:
theorem whisker_exchange
  given: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  proof: by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]

中文:
定理 whisker_exchange
  条件: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  证明: by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]

Depends on / 依赖: id_tensorHom, tensorHom_id
-/
theorem whisker_exchange {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]
/--
theorem `tensorHom_def'` / 定理 `tensorHom_def'`

English:
theorem tensorHom_def'
  given: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: whisker_exchange f g ▸ tensorHom_def f g

@[reassoc]

中文:
定理 tensorHom_def'
  条件: {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: whisker_exchange f g ▸ tensorHom_def f g

@[reassoc]

Depends on / 依赖: tensorHom_def, whisker_exchange
-/
theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂ :=
  whisker_exchange f g ▸ tensorHom_def f g

@[reassoc]
/--
theorem `whiskerLeft_comp_tensorHom` / 定理 `whiskerLeft_comp_tensorHom`

English:
theorem whiskerLeft_comp_tensorHom
  given: {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by
  simp [tensorHom_def']

@[reassoc]

中文:
定理 whiskerLeft_comp_tensorHom
  条件: {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by
  simp [tensorHom_def']

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
theorem whiskerLeft_comp_tensorHom {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (V ◁ g) ≫ (f otimesₘ h) = f otimesₘ (g ≫ h) := by
  simp [tensorHom_def']

@[reassoc]
/--
theorem `whiskerRight_comp_tensorHom` / 定理 `whiskerRight_comp_tensorHom`

English:
theorem whiskerRight_comp_tensorHom
  given: {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W)
  proof: by
  simp [tensorHom_def]

@[reassoc]

中文:
定理 whiskerRight_comp_tensorHom
  条件: {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W)
  证明: by
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
theorem whiskerRight_comp_tensorHom {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ▷ V) ≫ (g otimesₘ h) = (f ≫ g) otimesₘ h := by
  simp [tensorHom_def]

@[reassoc]
/--
theorem `tensorHom_comp_whiskerLeft` / 定理 `tensorHom_comp_whiskerLeft`

English:
theorem tensorHom_comp_whiskerLeft
  given: {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by
  simp [tensorHom_def]

@[reassoc]

中文:
定理 tensorHom_comp_whiskerLeft
  条件: {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
theorem tensorHom_comp_whiskerLeft {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f otimesₘ g) ≫ (W ◁ h) = f otimesₘ (g ≫ h) := by
  simp [tensorHom_def]

@[reassoc]
/--
theorem `tensorHom_comp_whiskerRight` / 定理 `tensorHom_comp_whiskerRight`

English:
theorem tensorHom_comp_whiskerRight
  given: {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W)
  proof: by
  simp [tensorHom_def, whisker_exchange]

中文:
定理 tensorHom_comp_whiskerRight
  条件: {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W)
  证明: by
  simp [tensorHom_def, whisker_exchange]

Depends on / 依赖: tensorHom_def, whisker_exchange
-/
theorem tensorHom_comp_whiskerRight {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f otimesₘ h) ≫ (g ▷ W) = (f ≫ g) otimesₘ h := by
  simp [tensorHom_def, whisker_exchange]

/--
lemma `leftUnitor_inv_comp_tensorHom` / 引理 `leftUnitor_inv_comp_tensorHom`

English:
lemma leftUnitor_inv_comp_tensorHom
  given: {X Y Z : C} (f : 𝟙_ C ⟶ Y) (g : X ⟶ Z)
  proof: by simp [tensorHom_def']

中文:
引理 leftUnitor_inv_comp_tensorHom
  条件: {X Y Z : C} (f : 𝟙_ C ⟶ Y) (g : X ⟶ Z)
  证明: by simp [tensorHom_def']
-/
@[reassoc] lemma leftUnitor_inv_comp_tensorHom {X Y Z : C} (f : 𝟙_ C ⟶ Y) (g : X ⟶ Z) :
    (fun_ X).inv ≫ (f otimesₘ g) = g ≫ (fun_ Z).inv ≫ f ▷ Z := by simp [tensorHom_def']

/--
lemma `rightUnitor_inv_comp_tensorHom` / 引理 `rightUnitor_inv_comp_tensorHom`

English:
lemma rightUnitor_inv_comp_tensorHom
  given: {X Y Z : C} (f : X ⟶ Y) (g : 𝟙_ C ⟶ Z)
  proof: by simp [tensorHom_def]

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_inv_comp_tensorHom
  条件: {X Y Z : C} (f : X ⟶ Y) (g : 𝟙_ C ⟶ Z)
  证明: by simp [tensorHom_def]

@[reassoc (attr := simp)]
-/
@[reassoc] lemma rightUnitor_inv_comp_tensorHom {X Y Z : C} (f : X ⟶ Y) (g : 𝟙_ C ⟶ Z) :
    (ρ_ X).inv ≫ (f otimesₘ g) = f ≫ (ρ_ Y).inv ≫ Y ◁ g := by simp [tensorHom_def]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_hom_inv` / 定理 `whiskerLeft_hom_inv`

English:
theorem whiskerLeft_hom_inv
  given: (X : C) {Y Z : C} (f : Y ≅ Z)
  proof: by
  rw [← whiskerLeft_comp]; rw [hom_inv_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_hom_inv
  条件: (X : C) {Y Z : C} (f : Y ≅ Z)
  证明: by
  rw [← whiskerLeft_comp]; rw [hom_inv_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem whiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.hom ≫ X ◁ f.inv = 𝟙 (X otimes Y) := by
  rw [← whiskerLeft_comp]; rw [hom_inv_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_whiskerRight` / 定理 `hom_inv_whiskerRight`

English:
theorem hom_inv_whiskerRight
  given: {X Y : C} (f : X ≅ Y) (Z : C)
  proof: by
  rw [← comp_whiskerRight]; rw [hom_inv_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_whiskerRight
  条件: {X Y : C} (f : X ≅ Y) (Z : C)
  证明: by
  rw [← comp_whiskerRight]; rw [hom_inv_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight, hom_inv_id, id_whiskerRight
-/
theorem hom_inv_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.hom ▷ Z ≫ f.inv ▷ Z = 𝟙 (X otimes Z) := by
  rw [← comp_whiskerRight]; rw [hom_inv_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_inv_hom` / 定理 `whiskerLeft_inv_hom`

English:
theorem whiskerLeft_inv_hom
  given: (X : C) {Y Z : C} (f : Y ≅ Z)
  proof: by
  rw [← whiskerLeft_comp]; rw [inv_hom_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_inv_hom
  条件: (X : C) {Y Z : C} (f : Y ≅ Z)
  证明: by
  rw [← whiskerLeft_comp]; rw [inv_hom_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: inv_hom_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem whiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X otimes Z) := by
  rw [← whiskerLeft_comp]; rw [inv_hom_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_whiskerRight` / 定理 `inv_hom_whiskerRight`

English:
theorem inv_hom_whiskerRight
  given: {X Y : C} (f : X ≅ Y) (Z : C)
  proof: by
  rw [← comp_whiskerRight]; rw [inv_hom_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 inv_hom_whiskerRight
  条件: {X Y : C} (f : X ≅ Y) (Z : C)
  证明: by
  rw [← comp_whiskerRight]; rw [inv_hom_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight, id_whiskerRight, inv_hom_id
-/
theorem inv_hom_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y otimes Z) := by
  rw [← comp_whiskerRight]; rw [inv_hom_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_hom_inv'` / 定理 `whiskerLeft_hom_inv'`

English:
theorem whiskerLeft_hom_inv'
  given: (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f]
  proof: by
  rw [← whiskerLeft_comp]; rw [IsIso.hom_inv_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_hom_inv'
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z) [是同构 f]
  证明: by
  rw [← whiskerLeft_comp]; rw [IsIso.hom_inv_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, hom_inv_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem whiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ f ≫ X ◁ inv f = 𝟙 (X otimes Y) := by
  rw [← whiskerLeft_comp]; rw [IsIso.hom_inv_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_whiskerRight'` / 定理 `hom_inv_whiskerRight'`

English:
theorem hom_inv_whiskerRight'
  given: {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C)
  proof: by
  rw [← comp_whiskerRight]; rw [IsIso.hom_inv_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_whiskerRight'
  条件: {X Y : C} (f : X ⟶ Y) [是同构 f] (Z : C)
  证明: by
  rw [← comp_whiskerRight]; rw [IsIso.hom_inv_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, comp_whiskerRight, hom_inv_id, id_whiskerRight
-/
theorem hom_inv_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    f ▷ Z ≫ inv f ▷ Z = 𝟙 (X otimes Z) := by
  rw [← comp_whiskerRight]; rw [IsIso.hom_inv_id]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_inv_hom'` / 定理 `whiskerLeft_inv_hom'`

English:
theorem whiskerLeft_inv_hom'
  given: (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f]
  proof: by
  rw [← whiskerLeft_comp]; rw [IsIso.inv_hom_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_inv_hom'
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z) [是同构 f]
  证明: by
  rw [← whiskerLeft_comp]; rw [IsIso.inv_hom_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.inv_hom_id, inv_hom_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem whiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ inv f ≫ X ◁ f = 𝟙 (X otimes Z) := by
  rw [← whiskerLeft_comp]; rw [IsIso.inv_hom_id]; rw [whiskerLeft_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_whiskerRight'` / 定理 `inv_hom_whiskerRight'`

English:
theorem inv_hom_whiskerRight'
  given: {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C)
  proof: by
  rw [← comp_whiskerRight]; rw [IsIso.inv_hom_id]; rw [id_whiskerRight]

中文:
定理 inv_hom_whiskerRight'
  条件: {X Y : C} (f : X ⟶ Y) [是同构 f] (Z : C)
  证明: by
  rw [← comp_whiskerRight]; rw [IsIso.inv_hom_id]; rw [id_whiskerRight]

Depends on / 依赖: IsIso.inv_hom_id, comp_whiskerRight, id_whiskerRight, inv_hom_id
-/
theorem inv_hom_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    inv f ▷ Z ≫ f ▷ Z = 𝟙 (Y otimes Z) := by
  rw [← comp_whiskerRight]; rw [IsIso.inv_hom_id]; rw [id_whiskerRight]

/-- The left whiskering of an isomorphism is an isomorphism. -/
@[simps]
/--
Definition of `whiskerLeftIso` / `whiskerLeftIso` 的定义

English:
definition whiskerLeftIso
  signature: (X : C) {Y Z : C} (f : Y ≅ Z)
  body: X ◁ f.hom
  inv := X ◁ f.inv

中文:
定义 whiskerLeftIso
  签名: (X : C) {Y Z : C} (f : Y ≅ Z)
  定义体: X ◁ f.hom
  inv := X ◁ f.inv

Depends on / 依赖: f.hom
-/
def whiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X otimes Y ≅ X otimes Z where
  hom := X ◁ f.hom
  inv := X ◁ f.inv

/--
Instance `whiskerLeft_isIso` / 实例 `whiskerLeft_isIso`

English:
instance whiskerLeft_isIso
  signature: (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f]
  body: (whiskerLeftIso X (asIso f)).isIso_hom

@[simp, push]

中文:
实例 whiskerLeft_isIso
  签名: (X : C) {Y Z : C} (f : Y ⟶ Z) [是同构 f]
  定义体: (whiskerLeftIso X (asIso f)).isIso_hom

@[simp, push]

Depends on / 依赖: isIso_hom, whiskerLeftIso
-/
instance whiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ f) :=
  (whiskerLeftIso X (asIso f)).isIso_hom

@[simp, push]
/--
theorem `inv_whiskerLeft` / 定理 `inv_whiskerLeft`

English:
theorem inv_whiskerLeft
  given: (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f]
  proof: by
  cat_disch

@[simp]

中文:
定理 inv_whiskerLeft
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z) [是同构 f]
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ f) = X ◁ inv f := by
  cat_disch

@[simp]
/--
lemma `whiskerLeftIso_refl` / 引理 `whiskerLeftIso_refl`

English:
lemma whiskerLeftIso_refl
  given: (W X : C)
  proof: Iso.ext (whiskerLeft_id W X)

@[simp]

中文:
引理 whiskerLeftIso_refl
  条件: (W X : C)
  证明: Iso.ext (whiskerLeft_id W X)

@[simp]

Depends on / 依赖: Iso.ext, whiskerLeft_id
-/
lemma whiskerLeftIso_refl (W X : C) :
    whiskerLeftIso W (Iso.refl X) = Iso.refl (W otimes X) :=
  Iso.ext (whiskerLeft_id W X)

@[simp]
/--
lemma `whiskerLeftIso_trans` / 引理 `whiskerLeftIso_trans`

English:
lemma whiskerLeftIso_trans
  given: (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z)
  proof: Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[simp]

中文:
引理 whiskerLeftIso_trans
  条件: (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z)
  证明: Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[simp]

Depends on / 依赖: Iso.ext, f.hom, g.hom, whiskerLeft_comp
-/
lemma whiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
    whiskerLeftIso W (f ≪≫ g) = whiskerLeftIso W f ≪≫ whiskerLeftIso W g :=
  Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[simp]
/--
lemma `whiskerLeftIso_symm` / 引理 `whiskerLeftIso_symm`

English:
lemma whiskerLeftIso_symm
  given: (W : C) {X Y : C} (f : X ≅ Y)
  proof: rfl

中文:
引理 whiskerLeftIso_symm
  条件: (W : C) {X Y : C} (f : X ≅ Y)
  证明: rfl
-/
lemma whiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) :
    (whiskerLeftIso W f).symm = whiskerLeftIso W f.symm := rfl

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[simps!]
/--
Definition of `whiskerRightIso` / `whiskerRightIso` 的定义

English:
definition whiskerRightIso
  signature: {X Y : C} (f : X ≅ Y) (Z : C)
  body: f.hom ▷ Z
  inv := f.inv ▷ Z

中文:
定义 whiskerRightIso
  签名: {X Y : C} (f : X ≅ Y) (Z : C)
  定义体: f.hom ▷ Z
  inv := f.inv ▷ Z

Depends on / 依赖: f.hom
-/
def whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X otimes Z ≅ Y otimes Z where
  hom := f.hom ▷ Z
  inv := f.inv ▷ Z

/--
Instance `whiskerRight_isIso` / 实例 `whiskerRight_isIso`

English:
instance whiskerRight_isIso
  signature: {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f]
  body: (whiskerRightIso (asIso f) Z).isIso_hom

@[simp, push]

中文:
实例 whiskerRight_isIso
  签名: {X Y : C} (f : X ⟶ Y) (Z : C) [是同构 f]
  定义体: (whiskerRightIso (asIso f) Z).isIso_hom

@[simp, push]

Depends on / 依赖: isIso_hom, whiskerRightIso
-/
instance whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z) :=
  (whiskerRightIso (asIso f) Z).isIso_hom

@[simp, push]
/--
theorem `inv_whiskerRight` / 定理 `inv_whiskerRight`

English:
theorem inv_whiskerRight
  given: {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f]
  proof: by
  cat_disch

@[simp]

中文:
定理 inv_whiskerRight
  条件: {X Y : C} (f : X ⟶ Y) (Z : C) [是同构 f]
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ Z) = inv f ▷ Z := by
  cat_disch

@[simp]
/--
lemma `whiskerRightIso_refl` / 引理 `whiskerRightIso_refl`

English:
lemma whiskerRightIso_refl
  given: (X W : C)
  proof: Iso.ext (id_whiskerRight X W)

@[simp]

中文:
引理 whiskerRightIso_refl
  条件: (X W : C)
  证明: Iso.ext (id_whiskerRight X W)

@[simp]

Depends on / 依赖: Iso.ext, id_whiskerRight
-/
lemma whiskerRightIso_refl (X W : C) :
    whiskerRightIso (Iso.refl X) W = Iso.refl (X otimes W) :=
  Iso.ext (id_whiskerRight X W)

@[simp]
/--
lemma `whiskerRightIso_trans` / 引理 `whiskerRightIso_trans`

English:
lemma whiskerRightIso_trans
  given: {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C)
  proof: Iso.ext (comp_whiskerRight f.hom g.hom W)

@[simp]

中文:
引理 whiskerRightIso_trans
  条件: {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C)
  证明: Iso.ext (comp_whiskerRight f.hom g.hom W)

@[simp]

Depends on / 依赖: Iso.ext, comp_whiskerRight, f.hom, g.hom
-/
lemma whiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) :
    whiskerRightIso (f ≪≫ g) W = whiskerRightIso f W ≪≫ whiskerRightIso g W :=
  Iso.ext (comp_whiskerRight f.hom g.hom W)

@[simp]
/--
lemma `whiskerRightIso_symm` / 引理 `whiskerRightIso_symm`

English:
lemma whiskerRightIso_symm
  given: {X Y : C} (f : X ≅ Y) (W : C)
  proof: rfl

中文:
引理 whiskerRightIso_symm
  条件: {X Y : C} (f : X ≅ Y) (W : C)
  证明: rfl
-/
lemma whiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) :
    (whiskerRightIso f W).symm = whiskerRightIso f.symm W := rfl

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
/--
Definition of `tensorIso` / `tensorIso` 的定义

English:
definition tensorIso
  signature: {X Y X' Y' : C} (f : X ≅ Y)
  body: f.hom otimesₘ g.hom
  inv := f.inv otimesₘ g.inv
  hom_inv_id := by simp [Iso.hom_inv_id, Iso.hom_inv_id]
  inv_hom_id := by simp [Iso.inv_hom_id, Iso.inv_hom_id]

中文:
定义 tensorIso
  签名: {X Y X' Y' : C} (f : X ≅ Y)
  定义体: f.hom otimesₘ g.hom
  inv := f.inv otimesₘ g.inv
  hom_inv_id := by simp [Iso.hom_inv_id, Iso.hom_inv_id]
  inv_hom_id := by simp [Iso.inv_hom_id, Iso.inv_hom_id]

Depends on / 依赖: f.hom, g.hom
-/
def tensorIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X otimes X' ≅ Y otimes Y' where
  hom := f.hom otimesₘ g.hom
  inv := f.inv otimesₘ g.inv
  hom_inv_id := by simp [Iso.hom_inv_id, Iso.hom_inv_id]
  inv_hom_id := by simp [Iso.inv_hom_id, Iso.inv_hom_id]

/-- Notation for `tensorIso`, the tensor product of isomorphisms -/
scoped infixr:70 " otimesᵢ " => tensorIso
-- TODO: Try setting this notation to `⊗` if the elaborator is improved and performs
-- better than currently on overloaded notations.

@[inherit_doc whiskerLeftIso]
scoped infixr:81 " ◁ᵢ " => whiskerLeftIso

@[inherit_doc whiskerRightIso]
scoped infixl:81 " ▷ᵢ " => whiskerRightIso

/--
theorem `tensorIso_def` / 定理 `tensorIso_def`

English:
theorem tensorIso_def
  given: {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y')
  proof: Iso.ext (tensorHom_def f.hom g.hom)

中文:
定理 tensorIso_def
  条件: {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y')
  证明: Iso.ext (tensorHom_def f.hom g.hom)

Depends on / 依赖: Iso.ext, f.hom, g.hom, tensorHom_def
-/
theorem tensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f otimesᵢ g = whiskerRightIso f X' ≪≫ whiskerLeftIso Y g :=
  Iso.ext (tensorHom_def f.hom g.hom)

/--
theorem `tensorIso_def'` / 定理 `tensorIso_def'`

English:
theorem tensorIso_def'
  given: {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y')
  proof: Iso.ext (tensorHom_def' f.hom g.hom)

中文:
定理 tensorIso_def'
  条件: {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y')
  证明: Iso.ext (tensorHom_def' f.hom g.hom)

Depends on / 依赖: Iso.ext, f.hom, g.hom, tensorHom_def
-/
theorem tensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f otimesᵢ g = whiskerLeftIso X g ≪≫ whiskerRightIso f Y' :=
  Iso.ext (tensorHom_def' f.hom g.hom)

/--
Instance `tensor_isIso` / 实例 `tensor_isIso`

English:
instance tensor_isIso
  signature: {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g]
  body: (asIso f otimesᵢ asIso g).isIso_hom

@[simp, push]

中文:
实例 tensor_isIso
  签名: {W X Y Z : C} (f : W ⟶ X) [是同构 f] (g : Y ⟶ Z) [是同构 g]
  定义体: (asIso f otimesᵢ asIso g).isIso_hom

@[simp, push]

Depends on / 依赖: isIso_hom
-/
instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f otimesₘ g) :=
  (asIso f otimesᵢ asIso g).isIso_hom

@[simp, push]
/--
theorem `inv_tensor` / 定理 `inv_tensor`

English:
theorem inv_tensor
  given: {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g]
  proof: by
  simp [tensorHom_def, whisker_exchange]

中文:
定理 inv_tensor
  条件: {W X Y Z : C} (f : W ⟶ X) [是同构 f] (g : Y ⟶ Z) [是同构 g]
  证明: by
  simp [tensorHom_def, whisker_exchange]

Depends on / 依赖: tensorHom_def, whisker_exchange
-/
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f otimesₘ g) = inv f otimesₘ inv g := by
  simp [tensorHom_def, whisker_exchange]

variable {W X Y Z : C}

/--
theorem `whiskerLeft_dite` / 定理 `whiskerLeft_dite`

English:
theorem whiskerLeft_dite
  statement: {P : Prop} [Decidable P]
  proof: by
  split_ifs <;> rfl

中文:
定理 whiskerLeft_dite
  结论: {P : 命题} [可判定 P]
  证明: by
  split_ifs <;> rfl

Depends on / 依赖: split_ifs
-/
theorem whiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P -> (Y ⟶ Z)) (f' : ¬P -> (Y ⟶ Z)) :
      X ◁ (if h : P then f h else f' h) = if h : P then X ◁ f h else X ◁ f' h := by
  split_ifs <;> rfl

/--
theorem `dite_whiskerRight` / 定理 `dite_whiskerRight`

English:
theorem dite_whiskerRight
  statement: {P : Prop} [Decidable P]
  proof: by
  split_ifs <;> rfl

中文:
定理 dite_whiskerRight
  结论: {P : 命题} [可判定 P]
  证明: by
  split_ifs <;> rfl

Depends on / 依赖: split_ifs
-/
theorem dite_whiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P -> (X ⟶ Y)) (f' : ¬P -> (X ⟶ Y)) (Z : C) :
      (if h : P then f h else f' h) ▷ Z = if h : P then f h ▷ Z else f' h ▷ Z := by
  split_ifs <;> rfl

/--
theorem `tensor_dite` / 定理 `tensor_dite`

English:
theorem tensor_dite
  statement: {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (Y ⟶ Z))
  proof: by split_ifs <;> rfl

中文:
定理 tensor_dite
  结论: {P : 命题} [可判定 P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (Y ⟶ Z))
  证明: by split_ifs <;> rfl

Depends on / 依赖: split_ifs
-/
theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (Y ⟶ Z))
    (g' : ¬P -> (Y ⟶ Z)) : (f otimesₘ if h : P then g h else g' h) =
    if h : P then f otimesₘ g h else f otimesₘ g' h := by split_ifs <;> rfl

/--
theorem `dite_tensor` / 定理 `dite_tensor`

English:
theorem dite_tensor
  statement: {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (Y ⟶ Z))
  proof: by split_ifs <;> rfl

@[simp]

中文:
定理 dite_tensor
  结论: {P : 命题} [可判定 P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (Y ⟶ Z))
  证明: by split_ifs <;> rfl

@[simp]

Depends on / 依赖: split_ifs
-/
theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (Y ⟶ Z))
    (g' : ¬P -> (Y ⟶ Z)) : (if h : P then g h else g' h) otimesₘ f =
    if h : P then g h otimesₘ f else g' h otimesₘ f := by split_ifs <;> rfl

@[simp]
/--
theorem `whiskerLeft_eqToHom` / 定理 `whiskerLeft_eqToHom`

English:
theorem whiskerLeft_eqToHom
  given: (X : C) {Y Z : C} (f : Y = Z)
  proof: by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]

中文:
定理 whiskerLeft_eqToHom
  条件: (X : C) {Y Z : C} (f : Y = Z)
  证明: by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]

Depends on / 依赖: eqToHom_refl, whiskerLeft_id
-/
theorem whiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) :
    X ◁ eqToHom f = eqToHom (congr_arg₂ tensorObj rfl f) := by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]
/--
theorem `eqToHom_whiskerRight` / 定理 `eqToHom_whiskerRight`

English:
theorem eqToHom_whiskerRight
  given: {X Y : C} (f : X = Y) (Z : C)
  proof: by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc]

中文:
定理 eqToHom_whiskerRight
  条件: {X Y : C} (f : X = Y) (Z : C)
  证明: by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc]

Depends on / 依赖: eqToHom_refl, id_whiskerRight
-/
theorem eqToHom_whiskerRight {X Y : C} (f : X = Y) (Z : C) :
    eqToHom f ▷ Z = eqToHom (congr_arg₂ tensorObj f rfl) := by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc]
/--
theorem `associator_naturality_left` / 定理 `associator_naturality_left`

English:
theorem associator_naturality_left
  given: {X X' : C} (f : X ⟶ X') (Y Z : C)
  proof: by simp

@[reassoc]

中文:
定理 associator_naturality_left
  条件: {X X' : C} (f : X ⟶ X') (Y Z : C)
  证明: by simp

@[reassoc]
-/
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y otimes Z) := by simp

@[reassoc]
/--
theorem `associator_inv_naturality_left` / 定理 `associator_inv_naturality_left`

English:
theorem associator_inv_naturality_left
  given: {X X' : C} (f : X ⟶ X') (Y Z : C)
  proof: by simp

@[reassoc]

中文:
定理 associator_inv_naturality_left
  条件: {X X' : C} (f : X ⟶ X') (Y Z : C)
  证明: by simp

@[reassoc]
-/
theorem associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y otimes Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z := by simp

@[reassoc]
/--
theorem `whiskerRight_tensor_symm` / 定理 `whiskerRight_tensor_symm`

English:
theorem whiskerRight_tensor_symm
  given: {X X' : C} (f : X ⟶ X') (Y Z : C)
  proof: by simp

@[reassoc]

中文:
定理 whiskerRight_tensor_symm
  条件: {X X' : C} (f : X ⟶ X') (Y Z : C)
  证明: by simp

@[reassoc]
-/
theorem whiskerRight_tensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z = (α_ X Y Z).hom ≫ f ▷ (Y otimes Z) ≫ (α_ X' Y Z).inv := by simp

@[reassoc]
/--
theorem `associator_naturality_middle` / 定理 `associator_naturality_middle`

English:
theorem associator_naturality_middle
  given: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  proof: by simp

@[reassoc]

中文:
定理 associator_naturality_middle
  条件: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  证明: by simp

@[reassoc]
-/
theorem associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z := by simp

@[reassoc]
/--
theorem `associator_inv_naturality_middle` / 定理 `associator_inv_naturality_middle`

English:
theorem associator_inv_naturality_middle
  given: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  proof: by simp

@[reassoc]

中文:
定理 associator_inv_naturality_middle
  条件: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  证明: by simp

@[reassoc]
-/
theorem associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z := by simp

@[reassoc]
/--
theorem `whisker_assoc_symm` / 定理 `whisker_assoc_symm`

English:
theorem whisker_assoc_symm
  given: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  proof: by simp

@[reassoc]

中文:
定理 whisker_assoc_symm
  条件: (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C)
  证明: by simp

@[reassoc]
-/
theorem whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom := by simp

@[reassoc]
/--
theorem `associator_naturality_right` / 定理 `associator_naturality_right`

English:
theorem associator_naturality_right
  given: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  proof: by simp

@[reassoc]

中文:
定理 associator_naturality_right
  条件: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  证明: by simp

@[reassoc]
-/
theorem associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X otimes Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f := by simp

@[reassoc]
/--
theorem `associator_inv_naturality_right` / 定理 `associator_inv_naturality_right`

English:
theorem associator_inv_naturality_right
  given: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  proof: by simp

@[reassoc]

中文:
定理 associator_inv_naturality_right
  条件: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  证明: by simp

@[reassoc]
-/
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X otimes Y) ◁ f := by simp

@[reassoc]
/--
theorem `tensor_whiskerLeft_symm` / 定理 `tensor_whiskerLeft_symm`

English:
theorem tensor_whiskerLeft_symm
  given: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  proof: by simp

@[reassoc]

中文:
定理 tensor_whiskerLeft_symm
  条件: (X Y : C) {Z Z' : C} (f : Z ⟶ Z')
  证明: by simp

@[reassoc]
-/
theorem tensor_whiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f = (α_ X Y Z).inv ≫ (X otimes Y) ◁ f ≫ (α_ X Y Z').hom := by simp

@[reassoc]
/--
theorem `leftUnitor_inv_naturality` / 定理 `leftUnitor_inv_naturality`

English:
theorem leftUnitor_inv_naturality
  given: {X Y : C} (f : X ⟶ Y)
  proof: by simp

@[reassoc]

中文:
定理 leftUnitor_inv_naturality
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by simp

@[reassoc]
-/
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (fun_ Y).inv = (fun_ X).inv ≫ _ ◁ f := by simp

@[reassoc]
/--
theorem `id_whiskerLeft_symm` / 定理 `id_whiskerLeft_symm`

English:
theorem id_whiskerLeft_symm
  given: {X X' : C} (f : X ⟶ X')
  proof: by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]

中文:
定理 id_whiskerLeft_symm
  条件: {X X' : C} (f : X ⟶ X')
  证明: by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]

Depends on / 依赖: comp_id, id_whiskerLeft, inv_hom_id, inv_hom_id_assoc
-/
theorem id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (fun_ X).inv ≫ 𝟙_ C ◁ f ≫ (fun_ X').hom := by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]
/--
theorem `rightUnitor_inv_naturality` / 定理 `rightUnitor_inv_naturality`

English:
theorem rightUnitor_inv_naturality
  given: {X X' : C} (f : X ⟶ X')
  proof: by simp

@[reassoc]

中文:
定理 rightUnitor_inv_naturality
  条件: {X X' : C} (f : X ⟶ X')
  证明: by simp

@[reassoc]
-/
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ f ▷ _ := by simp

@[reassoc]
/--
theorem `whiskerRight_id_symm` / 定理 `whiskerRight_id_symm`

English:
theorem whiskerRight_id_symm
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp

中文:
定理 whiskerRight_id_symm
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp
-/
theorem whiskerRight_id_symm {X Y : C} (f : X ⟶ Y) :
    f = (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom := by
  simp

/--
theorem `whiskerLeft_iff` / 定理 `whiskerLeft_iff`

English:
theorem whiskerLeft_iff
  given: {X Y : C} (f g : X ⟶ Y)
  statement: 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g
  proof: by simp

中文:
定理 whiskerLeft_iff
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g
  证明: by simp
-/
theorem whiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g := by simp

/--
theorem `whiskerRight_iff` / 定理 `whiskerRight_iff`

English:
theorem whiskerRight_iff
  given: {X Y : C} (f g : X ⟶ Y)
  statement: f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g
  proof: by simp

中文:
定理 whiskerRight_iff
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g
  证明: by simp
-/
theorem whiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g := by simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/

section

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv` / 定理 `pentagon_inv`

English:
theorem pentagon_inv
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y otimes Z)).inv ≫ (α_ (W otimes X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_inv_hom_hom_inv` / 定理 `pentagon_inv_inv_hom_hom_inv`

English:
theorem pentagon_inv_inv_hom_hom_inv
  proof: by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv)]; rw [← cancel_mono (α_ (W otimes X) Y Z).inv]
  simp

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_inv_hom_hom_inv
  证明: by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv)]; rw [← cancel_mono (α_ (W otimes X) Y Z).inv]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, cancel_mono, otimes
-/
theorem pentagon_inv_inv_hom_hom_inv :
    (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W otimes X) Y Z).hom =
      W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y otimes Z)).inv := by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv)]; rw [← cancel_mono (α_ (W otimes X) Y Z).inv]
  simp

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_hom_hom_hom_inv` / 定理 `pentagon_inv_hom_hom_hom_inv`

English:
theorem pentagon_inv_hom_hom_hom_inv
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_hom_hom_hom_inv
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_inv_hom_hom_hom_inv :
    (α_ (W otimes X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).hom =
      (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_inv_inv_inv_inv` / 定理 `pentagon_hom_inv_inv_inv_inv`

English:
theorem pentagon_hom_inv_inv_inv_inv
  proof: by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_inv_inv_inv_inv
  证明: by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi
-/
theorem pentagon_hom_inv_inv_inv_inv :
    W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y otimes Z)).inv ≫ (α_ (W otimes X) Y Z).inv =
      (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z := by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_hom_inv_hom_hom` / 定理 `pentagon_hom_hom_inv_hom_hom`

English:
theorem pentagon_hom_hom_inv_hom_hom
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_hom_inv_hom_hom
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_hom_hom_inv_hom_hom :
    (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).inv =
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_inv_inv_inv_hom` / 定理 `pentagon_hom_inv_inv_inv_hom`

English:
theorem pentagon_hom_inv_inv_inv_hom
  proof: by
  rw [← cancel_epi (α_ W X (Y otimes Z)).inv]; rw [← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_inv_inv_inv_hom
  证明: by
  rw [← cancel_epi (α_ W X (Y otimes Z)).inv]; rw [← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, cancel_mono, otimes
-/
theorem pentagon_hom_inv_inv_inv_hom :
    (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X otimes Y) Z).inv =
      (α_ (W otimes X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z := by
  rw [← cancel_epi (α_ W X (Y otimes Z)).inv]; rw [← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_hom_inv_inv_hom` / 定理 `pentagon_hom_hom_inv_inv_hom`

English:
theorem pentagon_hom_hom_inv_inv_hom
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_hom_inv_inv_hom
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_hom_hom_inv_inv_hom :
    (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y otimes Z)).inv =
      (α_ W X Y).inv ▷ Z ≫ (α_ (W otimes X) Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_hom_hom_hom_hom` / 定理 `pentagon_inv_hom_hom_hom_hom`

English:
theorem pentagon_inv_hom_hom_hom_hom
  proof: by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_hom_hom_hom_hom
  证明: by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi
-/
theorem pentagon_inv_hom_hom_hom_hom :
    (α_ W X Y).inv ▷ Z ≫ (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otimes Z)).hom =
      (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom := by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_inv_hom_inv_inv` / 定理 `pentagon_inv_inv_hom_inv_inv`

English:
theorem pentagon_inv_inv_hom_inv_inv
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_inv_hom_inv_inv
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_inv_inv_hom_inv_inv :
    (α_ W X (Y otimes Z)).inv ≫ (α_ (W otimes X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z =
      W ◁ (α_ X Y Z).inv ≫ (α_ W (X otimes Y) Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `triangle_assoc_comp_right` / 定理 `triangle_assoc_comp_right`

English:
theorem triangle_assoc_comp_right
  given: (X Y : C)
  proof: by
  rw [← triangle]; rw [Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]

中文:
定理 triangle_assoc_comp_right
  条件: (X Y : C)
  证明: by
  rw [← triangle]; rw [Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id_assoc, inv_hom_id_assoc, triangle
-/
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (fun_ Y).hom := by
  rw [← triangle]; rw [Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/--
theorem `triangle_assoc_comp_right_inv` / 定理 `triangle_assoc_comp_right_inv`

English:
theorem triangle_assoc_comp_right_inv
  given: (X Y : C)
  proof: by
  simp [← cancel_mono (X ◁ (fun_ Y).hom)]

@[reassoc (attr := simp)]

中文:
定理 triangle_assoc_comp_right_inv
  条件: (X Y : C)
  证明: by
  simp [← cancel_mono (X ◁ (fun_ Y).hom)]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono, fun_
-/
theorem triangle_assoc_comp_right_inv (X Y : C) :
    (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y).hom = X ◁ (fun_ Y).inv := by
  simp [← cancel_mono (X ◁ (fun_ Y).hom)]

@[reassoc (attr := simp)]
/--
theorem `triangle_assoc_comp_left_inv` / 定理 `triangle_assoc_comp_left_inv`

English:
theorem triangle_assoc_comp_left_inv
  given: (X Y : C)
  proof: by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

中文:
定理 triangle_assoc_comp_left_inv
  条件: (X Y : C)
  证明: by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

Depends on / 依赖: cancel_mono
-/
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (X ◁ (fun_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight X Y : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`.
-/
@[reassoc, simp]
/--
theorem `leftUnitor_whiskerRight` / 定理 `leftUnitor_whiskerRight`

English:
theorem leftUnitor_whiskerRight
  given: (X Y : C)
  proof: by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [← cancel_epi (α_ _ _ _).hom]; rw [←
      cancel_epi ((α_ _ _ _).hom ▷ _)]; rw [pentagon_assoc]; rw [triangle]; rw [← associator_naturality_middle]; rw [←
      comp_whiskerRight_assoc]; rw [triangle]; rw [associator_naturality_left]

@[reassoc, simp]

中文:
定理 leftUnitor_whiskerRight
  条件: (X Y : C)
  证明: by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [← cancel_epi (α_ _ _ _).hom]; rw [←
      cancel_epi ((α_ _ _ _).hom ▷ _)]; rw [pentagon_assoc]; rw [triangle]; rw [← associator_naturality_middle]; rw [←
      comp_whiskerRight_assoc]; rw [triangle]; rw [associator_naturality_left]

@[reassoc, simp]

Depends on / 依赖: associator_naturality_left, associator_naturality_middle, cancel_epi, comp_whiskerRight_assoc, pentagon_assoc, triangle, whiskerLeft_comp, whiskerLeft_iff
-/
theorem leftUnitor_whiskerRight (X Y : C) :
    (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)).hom := by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [← cancel_epi (α_ _ _ _).hom]; rw [←
      cancel_epi ((α_ _ _ _).hom ▷ _)]; rw [pentagon_assoc]; rw [triangle]; rw [← associator_naturality_middle]; rw [←
      comp_whiskerRight_assoc]; rw [triangle]; rw [associator_naturality_left]

@[reassoc, simp]
/--
theorem `leftUnitor_inv_whiskerRight` / 定理 `leftUnitor_inv_whiskerRight`

English:
theorem leftUnitor_inv_whiskerRight
  given: (X Y : C)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc, simp]

中文:
定理 leftUnitor_inv_whiskerRight
  条件: (X Y : C)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc, simp]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem leftUnitor_inv_whiskerRight (X Y : C) :
    (fun_ X).inv ▷ Y = (fun_ (X otimes Y)).inv ≫ (α_ (𝟙_ C) X Y).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
/--
theorem `whiskerLeft_rightUnitor` / 定理 `whiskerLeft_rightUnitor`

English:
theorem whiskerLeft_rightUnitor
  given: (X Y : C)
  proof: by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [← cancel_epi (α_ _ _ _).inv]; rw [←
      cancel_epi (X ◁ (α_ _ _ _).inv)]; rw [pentagon_inv_assoc]; rw [triangle_assoc_comp_right]; rw [←
      associator_inv_naturality_middle]; rw [← whiskerLeft_comp_assoc]; rw [triangle_assoc_comp_right]; rw [associator_inv_naturality_right]

@[reassoc, simp]

中文:
定理 whiskerLeft_rightUnitor
  条件: (X Y : C)
  证明: by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [← cancel_epi (α_ _ _ _).inv]; rw [←
      cancel_epi (X ◁ (α_ _ _ _).inv)]; rw [pentagon_inv_assoc]; rw [triangle_assoc_comp_right]; rw [←
      associator_inv_naturality_middle]; rw [← whiskerLeft_comp_assoc]; rw [triangle_assoc_comp_right]; rw [associator_inv_naturality_right]

@[reassoc, simp]

Depends on / 依赖: associator_inv_naturality_middle, associator_inv_naturality_right, cancel_epi, comp_whiskerRight, pentagon_inv_assoc, triangle_assoc_comp_right, whiskerLeft_comp_assoc, whiskerRight_iff
-/
theorem whiskerLeft_rightUnitor (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).hom := by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [← cancel_epi (α_ _ _ _).inv]; rw [←
      cancel_epi (X ◁ (α_ _ _ _).inv)]; rw [pentagon_inv_assoc]; rw [triangle_assoc_comp_right]; rw [←
      associator_inv_naturality_middle]; rw [← whiskerLeft_comp_assoc]; rw [triangle_assoc_comp_right]; rw [associator_inv_naturality_right]

@[reassoc, simp]
/--
theorem `whiskerLeft_rightUnitor_inv` / 定理 `whiskerLeft_rightUnitor_inv`

English:
theorem whiskerLeft_rightUnitor_inv
  given: (X Y : C)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc]

中文:
定理 whiskerLeft_rightUnitor_inv
  条件: (X Y : C)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem whiskerLeft_rightUnitor_inv (X Y : C) :
    X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙_ C)).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc]
/--
theorem `leftUnitor_tensor_hom` / 定理 `leftUnitor_tensor_hom`

English:
theorem leftUnitor_tensor_hom
  given: (X Y : C)
  proof: by simp

@[reassoc]

中文:
定理 leftUnitor_tensor_hom
  条件: (X Y : C)
  证明: by simp

@[reassoc]
-/
theorem leftUnitor_tensor_hom (X Y : C) :
    (fun_ (X otimes Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (fun_ X).hom ▷ Y := by simp

@[reassoc]
/--
theorem `leftUnitor_tensor_inv` / 定理 `leftUnitor_tensor_inv`

English:
theorem leftUnitor_tensor_inv
  given: (X Y : C)
  proof: by simp

@[reassoc]

中文:
定理 leftUnitor_tensor_inv
  条件: (X Y : C)
  证明: by simp

@[reassoc]
-/
theorem leftUnitor_tensor_inv (X Y : C) :
    (fun_ (X otimes Y)).inv = (fun_ X).inv ▷ Y ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc]
/--
theorem `rightUnitor_tensor_hom` / 定理 `rightUnitor_tensor_hom`

English:
theorem rightUnitor_tensor_hom
  given: (X Y : C)
  proof: by simp

@[reassoc]

中文:
定理 rightUnitor_tensor_hom
  条件: (X Y : C)
  证明: by simp

@[reassoc]
-/
theorem rightUnitor_tensor_hom (X Y : C) :
    (ρ_ (X otimes Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by simp

@[reassoc]
/--
theorem `rightUnitor_tensor_inv` / 定理 `rightUnitor_tensor_inv`

English:
theorem rightUnitor_tensor_inv
  given: (X Y : C)
  proof: by simp

中文:
定理 rightUnitor_tensor_inv
  条件: (X Y : C)
  证明: by simp
-/
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X otimes Y)).inv = X ◁ (ρ_ Y).inv ≫ (α_ X Y (𝟙_ C)).inv := by simp

end

@[reassoc]
/--
theorem `associator_inv_naturality` / 定理 `associator_inv_naturality`

English:
theorem associator_inv_naturality
  given: {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
  proof: by
  simp [tensorHom_def]

@[reassoc, simp]

中文:
定理 associator_inv_naturality
  条件: {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
  证明: by
  simp [tensorHom_def]

@[reassoc, simp]

Depends on / 依赖: tensorHom_def
-/
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f otimesₘ g otimesₘ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f otimesₘ g) otimesₘ h) := by
  simp [tensorHom_def]

@[reassoc, simp]
/--
theorem `associator_conjugation` / 定理 `associator_conjugation`

English:
theorem associator_conjugation
  given: {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
  proof: by
  rw [associator_inv_naturality]; rw [hom_inv_id_assoc]

@[reassoc]

中文:
定理 associator_conjugation
  条件: {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
  证明: by
  rw [associator_inv_naturality]; rw [hom_inv_id_assoc]

@[reassoc]

Depends on / 依赖: associator_inv_naturality, hom_inv_id_assoc
-/
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f otimesₘ g) otimesₘ h = (α_ X Y Z).hom ≫ (f otimesₘ g otimesₘ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality]; rw [hom_inv_id_assoc]

@[reassoc]
/--
theorem `associator_inv_conjugation` / 定理 `associator_inv_conjugation`

English:
theorem associator_inv_conjugation
  given: {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
  proof: by
  rw [associator_naturality]; rw [inv_hom_id_assoc]

中文:
定理 associator_inv_conjugation
  条件: {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
  证明: by
  rw [associator_naturality]; rw [inv_hom_id_assoc]

Depends on / 依赖: associator_naturality, inv_hom_id_assoc
-/
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f otimesₘ g otimesₘ h = (α_ X Y Z).inv ≫ ((f otimesₘ g) otimesₘ h) ≫ (α_ X' Y' Z').hom := by
  rw [associator_naturality]; rw [inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
/--
theorem `id_tensor_associator_naturality` / 定理 `id_tensor_associator_naturality`

English:
theorem id_tensor_associator_naturality
  given: {X Y Z Z' : C} (h : Z ⟶ Z')
  proof: by
  rw [← id_tensorHom_id]; rw [associator_naturality]

@[reassoc]

中文:
定理 id_tensor_associator_naturality
  条件: {X Y Z Z' : C} (h : Z ⟶ Z')
  证明: by
  rw [← id_tensorHom_id]; rw [associator_naturality]

@[reassoc]

Depends on / 依赖: associator_naturality, id_tensorHom_id
-/
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X otimes Y) otimesₘ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X otimesₘ 𝟙 Y otimesₘ h) := by
  rw [← id_tensorHom_id]; rw [associator_naturality]

@[reassoc]
/--
theorem `id_tensor_associator_inv_naturality` / 定理 `id_tensor_associator_inv_naturality`

English:
theorem id_tensor_associator_inv_naturality
  given: {X Y Z X' : C} (f : X ⟶ X')
  proof: by
  rw [← id_tensorHom_id]; rw [associator_inv_naturality]

@[reassoc]

中文:
定理 id_tensor_associator_inv_naturality
  条件: {X Y Z X' : C} (f : X ⟶ X')
  证明: by
  rw [← id_tensorHom_id]; rw [associator_inv_naturality]

@[reassoc]

Depends on / 依赖: associator_inv_naturality, id_tensorHom_id
-/
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f otimesₘ 𝟙 (Y otimes Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f otimesₘ 𝟙 Y) otimesₘ 𝟙 Z) := by
  rw [← id_tensorHom_id]; rw [associator_inv_naturality]

@[reassoc]
/--
theorem `hom_inv_id_tensor` / 定理 `hom_inv_id_tensor`

English:
theorem hom_inv_id_tensor
  given: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 hom_inv_id_tensor
  条件: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom otimesₘ g) ≫ (f.inv otimesₘ h) = (𝟙 V otimesₘ g) ≫ (𝟙 V otimesₘ h) := by simp

@[reassoc]
/--
theorem `inv_hom_id_tensor` / 定理 `inv_hom_id_tensor`

English:
theorem inv_hom_id_tensor
  given: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 inv_hom_id_tensor
  条件: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv otimesₘ g) ≫ (f.hom otimesₘ h) = (𝟙 W otimesₘ g) ≫ (𝟙 W otimesₘ h) := by simp

@[reassoc]
/--
theorem `tensor_hom_inv_id` / 定理 `tensor_hom_inv_id`

English:
theorem tensor_hom_inv_id
  given: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 tensor_hom_inv_id
  条件: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g otimesₘ f.hom) ≫ (h otimesₘ f.inv) = (g otimesₘ 𝟙 V) ≫ (h otimesₘ 𝟙 V) := by simp

@[reassoc]
/--
theorem `tensor_inv_hom_id` / 定理 `tensor_inv_hom_id`

English:
theorem tensor_inv_hom_id
  given: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 tensor_inv_hom_id
  条件: {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g otimesₘ f.inv) ≫ (h otimesₘ f.hom) = (g otimesₘ 𝟙 W) ≫ (h otimesₘ 𝟙 W) := by simp

@[reassoc]
/--
theorem `hom_inv_id_tensor'` / 定理 `hom_inv_id_tensor'`

English:
theorem hom_inv_id_tensor'
  given: {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 hom_inv_id_tensor'
  条件: {V W X Y Z : C} (f : V ⟶ W) [是同构 f] (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f otimesₘ g) ≫ (inv f otimesₘ h) = (𝟙 V otimesₘ g) ≫ (𝟙 V otimesₘ h) := by simp

@[reassoc]
/--
theorem `inv_hom_id_tensor'` / 定理 `inv_hom_id_tensor'`

English:
theorem inv_hom_id_tensor'
  given: {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 inv_hom_id_tensor'
  条件: {V W X Y Z : C} (f : V ⟶ W) [是同构 f] (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f otimesₘ g) ≫ (f otimesₘ h) = (𝟙 W otimesₘ g) ≫ (𝟙 W otimesₘ h) := by simp

@[reassoc]
/--
theorem `tensor_hom_inv_id'` / 定理 `tensor_hom_inv_id'`

English:
theorem tensor_hom_inv_id'
  given: {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 tensor_hom_inv_id'
  条件: {V W X Y Z : C} (f : V ⟶ W) [是同构 f] (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g otimesₘ f) ≫ (h otimesₘ inv f) = (g otimesₘ 𝟙 V) ≫ (h otimesₘ 𝟙 V) := by simp

@[reassoc]
/--
theorem `tensor_inv_hom_id'` / 定理 `tensor_inv_hom_id'`

English:
theorem tensor_inv_hom_id'
  given: {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 tensor_inv_hom_id'
  条件: {V W X Y Z : C} (f : V ⟶ W) [是同构 f] (g : X ⟶ Y) (h : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g otimesₘ inv f) ≫ (h otimesₘ f) = (g otimesₘ 𝟙 W) ≫ (h otimesₘ 𝟙 W) := by simp

@[reassoc]
/--
theorem `comp_tensor_id` / 定理 `comp_tensor_id`

English:
theorem comp_tensor_id
  given: (f : W ⟶ X) (g : X ⟶ Y)
  statement: f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z)
  proof: by
  simp

@[reassoc]

中文:
定理 comp_tensor_id
  条件: (f : W ⟶ X) (g : X ⟶ Y)
  结论: f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z)
  证明: by
  simp

@[reassoc]
-/
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z) := by
  simp

@[reassoc]
/--
theorem `id_tensor_comp` / 定理 `id_tensor_comp`

English:
theorem id_tensor_comp
  given: (f : W ⟶ X) (g : X ⟶ Y)
  statement: 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ f) ≫ (𝟙 Z otimesₘ g)
  proof: by
  simp

@[reassoc]

中文:
定理 id_tensor_comp
  条件: (f : W ⟶ X) (g : X ⟶ Y)
  结论: 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ f) ≫ (𝟙 Z otimesₘ g)
  证明: by
  simp

@[reassoc]
-/
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ f) ≫ (𝟙 Z otimesₘ g) := by
  simp

@[reassoc]
/--
theorem `id_tensor_comp_tensor_id` / 定理 `id_tensor_comp_tensor_id`

English:
theorem id_tensor_comp_tensor_id
  given: (f : W ⟶ X) (g : Y ⟶ Z)
  statement: (𝟙 Y otimesₘ f) ≫ (g otimesₘ 𝟙 X) = g otimesₘ f
  proof: by
  simp [tensorHom_def']

@[reassoc]

中文:
定理 id_tensor_comp_tensor_id
  条件: (f : W ⟶ X) (g : Y ⟶ Z)
  结论: (𝟙 Y otimesₘ f) ≫ (g otimesₘ 𝟙 X) = g otimesₘ f
  证明: by
  simp [tensorHom_def']

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y otimesₘ f) ≫ (g otimesₘ 𝟙 X) = g otimesₘ f := by
  simp [tensorHom_def']

@[reassoc]
/--
theorem `tensor_id_comp_id_tensor` / 定理 `tensor_id_comp_id_tensor`

English:
theorem tensor_id_comp_id_tensor
  given: (f : W ⟶ X) (g : Y ⟶ Z)
  statement: (g otimesₘ 𝟙 W) ≫ (𝟙 Z otimesₘ f) = g otimesₘ f
  proof: by
  simp [tensorHom_def]

中文:
定理 tensor_id_comp_id_tensor
  条件: (f : W ⟶ X) (g : Y ⟶ Z)
  结论: (g otimesₘ 𝟙 W) ≫ (𝟙 Z otimesₘ f) = g otimesₘ f
  证明: by
  simp [tensorHom_def]

Depends on / 依赖: tensorHom_def
-/
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g otimesₘ 𝟙 W) ≫ (𝟙 Z otimesₘ f) = g otimesₘ f := by
  simp [tensorHom_def]

/--
theorem `tensor_left_iff` / 定理 `tensor_left_iff`

English:
theorem tensor_left_iff
  given: {X Y : C} (f g : X ⟶ Y)
  statement: 𝟙 (𝟙_ C) otimesₘ f = 𝟙 (𝟙_ C) otimesₘ g ↔ f = g
  proof: by simp

中文:
定理 tensor_left_iff
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: 𝟙 (𝟙_ C) otimesₘ f = 𝟙 (𝟙_ C) otimesₘ g ↔ f = g
  证明: by simp
-/
theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) otimesₘ f = 𝟙 (𝟙_ C) otimesₘ g ↔ f = g := by simp

/--
theorem `tensor_right_iff` / 定理 `tensor_right_iff`

English:
theorem tensor_right_iff
  given: {X Y : C} (f g : X ⟶ Y)
  statement: f otimesₘ 𝟙 (𝟙_ C) = g otimesₘ 𝟙 (𝟙_ C) ↔ f = g
  proof: by simp

中文:
定理 tensor_right_iff
  条件: {X Y : C} (f g : X ⟶ Y)
  结论: f otimesₘ 𝟙 (𝟙_ C) = g otimesₘ 𝟙 (𝟙_ C) ↔ f = g
  证明: by simp
-/
theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f otimesₘ 𝟙 (𝟙_ C) = g otimesₘ 𝟙 (𝟙_ C) ↔ f = g := by simp

section

variable (C)

attribute [local simp] whisker_exchange

/-- The tensor product expressed as a functor. -/
@[simps, implicit_reducible]
/--
Definition of `tensor` / `tensor` 的定义

English:
definition tensor
  signature: : C × C ⥤ C where
  body: X.1 otimes X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 otimesₘ f.2

中文:
定义 tensor
  签名: : C × C ⥤ C where
  定义体: X.1 otimes X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 otimesₘ f.2

Depends on / 依赖: otimes
-/
def tensor : C × C ⥤ C where
  obj X := X.1 otimes X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 otimesₘ f.2

/--
Definition of `leftAssocTensor` / `leftAssocTensor` 的定义

English:
definition leftAssocTensor
  signature: : C × C × C ⥤ C where
  body: (X.1 otimes X.2.1) otimes X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 otimesₘ f.2.1) otimesₘ f.2.2

@[simp]

中文:
定义 leftAssocTensor
  签名: : C × C × C ⥤ C where
  定义体: (X.1 otimes X.2.1) otimes X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 otimesₘ f.2.1) otimesₘ f.2.2

@[simp]

Depends on / 依赖: otimes
-/
def leftAssocTensor : C × C × C ⥤ C where
  obj X := (X.1 otimes X.2.1) otimes X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 otimesₘ f.2.1) otimesₘ f.2.2

@[simp]
/--
theorem `leftAssocTensor_obj` / 定理 `leftAssocTensor_obj`

English:
theorem leftAssocTensor_obj
  given: (X)
  statement: (leftAssocTensor C).obj X = (X.1 otimes X.2.1) otimes X.2.2
  proof: rfl

@[simp]

中文:
定理 leftAssocTensor_obj
  条件: (X)
  结论: (leftAssocTensor C).obj X = (X.1 otimes X.2.1) otimes X.2.2
  证明: rfl

@[simp]
-/
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 otimes X.2.1) otimes X.2.2 :=
  rfl

@[simp]
/--
theorem `leftAssocTensor_map` / 定理 `leftAssocTensor_map`

English:
theorem leftAssocTensor_map
  given: {X Y} (f : X ⟶ Y)
  proof: rfl

中文:
定理 leftAssocTensor_map
  条件: {X Y} (f : X ⟶ Y)
  证明: rfl
-/
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) :
    (leftAssocTensor C).map f = (f.1 otimesₘ f.2.1) otimesₘ f.2.2 :=
  rfl

/--
Definition of `rightAssocTensor` / `rightAssocTensor` 的定义

English:
definition rightAssocTensor
  signature: : C × C × C ⥤ C where
  body: X.1 otimes X.2.1 otimes X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 otimesₘ f.2.1 otimesₘ f.2.2

@[simp]

中文:
定义 rightAssocTensor
  签名: : C × C × C ⥤ C where
  定义体: X.1 otimes X.2.1 otimes X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 otimesₘ f.2.1 otimesₘ f.2.2

@[simp]

Depends on / 依赖: otimes
-/
def rightAssocTensor : C × C × C ⥤ C where
  obj X := X.1 otimes X.2.1 otimes X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 otimesₘ f.2.1 otimesₘ f.2.2

@[simp]
/--
theorem `rightAssocTensor_obj` / 定理 `rightAssocTensor_obj`

English:
theorem rightAssocTensor_obj
  given: (X)
  statement: (rightAssocTensor C).obj X = X.1 otimes X.2.1 otimes X.2.2
  proof: rfl

@[simp]

中文:
定理 rightAssocTensor_obj
  条件: (X)
  结论: (rightAssocTensor C).obj X = X.1 otimes X.2.1 otimes X.2.2
  证明: rfl

@[simp]
-/
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 otimes X.2.1 otimes X.2.2 :=
  rfl

@[simp]
/--
theorem `rightAssocTensor_map` / 定理 `rightAssocTensor_map`

English:
theorem rightAssocTensor_map
  given: {X Y} (f : X ⟶ Y)
  proof: rfl

中文:
定理 rightAssocTensor_map
  条件: {X Y} (f : X ⟶ Y)
  证明: rfl
-/
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) :
    (rightAssocTensor C).map f = f.1 otimesₘ f.2.1 otimesₘ f.2.2 :=
  rfl

/-- The tensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category. -/
@[simps, implicit_reducible]
/--
Definition of `curriedTensor` / `curriedTensor` 的定义

English:
definition curriedTensor
  signature: : C ⥤ C ⥤ C where
  body: { obj := fun Y => X otimes Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

中文:
定义 curriedTensor
  签名: : C ⥤ C ⥤ C where
  定义体: { obj := fun Y => X otimes Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

Depends on / 依赖: otimes
-/
def curriedTensor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X otimes Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

variable {C}

/--
Definition of `tensorLeft` / `tensorLeft` 的定义

English:
abbreviation tensorLeft
  signature: (X : C)
  body: (curriedTensor C).obj X

中文:
缩写 tensorLeft
  签名: (X : C)
  定义体: (curriedTensor C).obj X

Depends on / 依赖: curriedTensor
-/
abbrev tensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X

/--
Definition of `tensorRight` / `tensorRight` 的定义

English:
abbreviation tensorRight
  signature: (X : C)
  body: (curriedTensor C).flip.obj X

中文:
缩写 tensorRight
  签名: (X : C)
  定义体: (curriedTensor C).flip.obj X

Depends on / 依赖: curriedTensor, flip.obj
-/
abbrev tensorRight (X : C) : C ⥤ C := (curriedTensor C).flip.obj X

variable (C)

/--
Definition of `tensorUnitLeft` / `tensorUnitLeft` 的定义

English:
abbreviation tensorUnitLeft
  signature: : C ⥤ C
  body: tensorLeft (𝟙_ C)

中文:
缩写 tensorUnitLeft
  签名: : C ⥤ C
  定义体: tensorLeft (𝟙_ C)

Depends on / 依赖: tensorLeft
-/
abbrev tensorUnitLeft : C ⥤ C := tensorLeft (𝟙_ C)

/--
Definition of `tensorUnitRight` / `tensorUnitRight` 的定义

English:
abbreviation tensorUnitRight
  signature: : C ⥤ C
  body: tensorRight (𝟙_ C)

中文:
缩写 tensorUnitRight
  签名: : C ⥤ C
  定义体: tensorRight (𝟙_ C)

Depends on / 依赖: tensorRight
-/
abbrev tensorUnitRight : C ⥤ C := tensorRight (𝟙_ C)

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
/-- The associator as a natural isomorphism. -/
@[simps!]
/--
Definition of `associatorNatIso` / `associatorNatIso` 的定义

English:
definition associatorNatIso
  signature: : leftAssocTensor C ≅ rightAssocTensor C
  body: NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

中文:
定义 associator自然数Iso
  签名: : leftAssocTensor C ≅ rightAssocTensor C
  定义体: NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

Depends on / 依赖: MonoidalCategory, MonoidalCategory.associator, NatIso, NatIso.ofComponents, associator, ofComponents
-/
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
/-- The left unitor as a natural isomorphism. -/
@[simps!]
/--
Definition of `leftUnitorNatIso` / `leftUnitorNatIso` 的定义

English:
definition leftUnitorNatIso
  signature: : tensorUnitLeft C ≅ 𝟭 C
  body: NatIso.ofComponents MonoidalCategory.leftUnitor

中文:
定义 leftUnitor自然数Iso
  签名: : tensorUnitLeft C ≅ 𝟭 C
  定义体: NatIso.ofComponents MonoidalCategory.leftUnitor

Depends on / 依赖: MonoidalCategory, MonoidalCategory.leftUnitor, NatIso, NatIso.ofComponents, leftUnitor, ofComponents
-/
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.leftUnitor

set_option backward.defeqAttrib.useBackward true in
/-- The right unitor as a natural isomorphism. -/
@[simps!]
/--
Definition of `rightUnitorNatIso` / `rightUnitorNatIso` 的定义

English:
definition rightUnitorNatIso
  signature: : tensorUnitRight C ≅ 𝟭 C
  body: NatIso.ofComponents MonoidalCategory.rightUnitor

中文:
定义 rightUnitor自然数Iso
  签名: : tensorUnitRight C ≅ 𝟭 C
  定义体: NatIso.ofComponents MonoidalCategory.rightUnitor

Depends on / 依赖: MonoidalCategory, MonoidalCategory.rightUnitor, NatIso, NatIso.ofComponents, ofComponents, rightUnitor
-/
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.rightUnitor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/
@[simps!]
/--
Definition of `curriedAssociatorNatIso` / `curriedAssociatorNatIso` 的定义

English:
definition curriedAssociatorNatIso
  signature: :
  body: NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α_ X₁ X₂ X₃)))

中文:
定义 curriedAssociator自然数Iso
  签名: :
  定义体: NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α_ X₁ X₂ X₃)))

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def curriedAssociatorNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedTensor C) ≅
      bifunctorComp₂₃ (curriedTensor C) (curriedTensor C) :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α_ X₁ X₂ X₃)))

section

variable {C}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `tensorLeftTensor` / `tensorLeftTensor` 的定义

English:
definition tensorLeftTensor
  signature: (X Y : C)
  body: NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]

中文:
定义 tensorLeftTensor
  签名: (X Y : C)
  定义体: NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, associator, ofComponents
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X otimes Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]
/--
theorem `tensorLeftTensor_hom_app` / 定理 `tensorLeftTensor_hom_app`

English:
theorem tensorLeftTensor_hom_app
  given: (X Y Z : C)
  proof: rfl

中文:
定理 tensorLeftTensor_hom_app
  条件: (X Y Z : C)
  证明: rfl
-/
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorLeftTensor_inv_app` / 定理 `tensorLeftTensor_inv_app`

English:
theorem tensorLeftTensor_inv_app
  given: (X Y Z : C)
  proof: by simp [tensorLeftTensor]

中文:
定理 tensorLeftTensor_inv_app
  条件: (X Y Z : C)
  证明: by simp [tensorLeftTensor]

Depends on / 依赖: tensorLeftTensor
-/
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensorLeftTensor]

variable (C)

/--
Definition of `tensoringLeft` / `tensoringLeft` 的定义

English:
abbreviation tensoringLeft
  signature: : C ⥤ C ⥤ C
  body: curriedTensor C

中文:
缩写 tensoringLeft
  签名: : C ⥤ C ⥤ C
  定义体: curriedTensor C

Depends on / 依赖: curriedTensor
-/
abbrev tensoringLeft : C ⥤ C ⥤ C := curriedTensor C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tensoringLeft C).Faithful
  body: by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

中文:
实例 :
  签名: (tensoringLeft C).忠实
  定义体: by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

Depends on / 依赖: congr_fun, injections, replace
-/
instance : (tensoringLeft C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/--
Definition of `tensoringRight` / `tensoringRight` 的定义

English:
abbreviation tensoringRight
  signature: : C ⥤ C ⥤ C
  body: (curriedTensor C).flip

中文:
缩写 tensoringRight
  签名: : C ⥤ C ⥤ C
  定义体: (curriedTensor C).flip

Depends on / 依赖: curriedTensor
-/
abbrev tensoringRight : C ⥤ C ⥤ C := (curriedTensor C).flip

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tensoringRight C).Faithful
  body: by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

中文:
实例 :
  签名: (tensoringRight C).忠实
  定义体: by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

Depends on / 依赖: congr_fun, injections, replace
-/
instance : (tensoringRight C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

variable {C}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `tensorRightTensor` / `tensorRightTensor` 的定义

English:
definition tensorRightTensor
  signature: (X Y : C)
  body: NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]

中文:
定义 tensorRightTensor
  签名: (X Y : C)
  定义体: NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, associator, ofComponents
-/
def tensorRightTensor (X Y : C) : tensorRight (X otimes Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]
/--
theorem `tensorRightTensor_hom_app` / 定理 `tensorRightTensor_hom_app`

English:
theorem tensorRightTensor_hom_app
  given: (X Y Z : C)
  proof: rfl

中文:
定理 tensorRightTensor_hom_app
  条件: (X Y Z : C)
  证明: rfl
-/
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorRightTensor_inv_app` / 定理 `tensorRightTensor_inv_app`

English:
theorem tensorRightTensor_inv_app
  given: (X Y Z : C)
  proof: by simp [tensorRightTensor]

中文:
定理 tensorRightTensor_inv_app
  条件: (X Y Z : C)
  证明: by simp [tensorRightTensor]

Depends on / 依赖: tensorRightTensor
-/
theorem tensorRightTensor_inv_app (X Y Z : C) :
    (tensorRightTensor X Y).inv.app Z = (associator Z X Y).hom := by simp [tensorRightTensor]

end

end

section

universe v₁ v₂ u₁ u₂

open CategoryTheory.Prod

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]
variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

@[simps! tensorObj tensorHom tensorUnit whiskerLeft whiskerRight associator
  leftUnitor rightUnitor]
/--
Instance `prodMonoidal` / 实例 `prodMonoidal`

English:
instance prodMonoidal
  signature: : MonoidalCategory (C₁ × C₂) where
  body: (X.1 otimes Y.1, X.2 otimes Y.2)
  tensorHom f g := (f.1 otimesₘ g.1) ×ₘ f.2 otimesₘ g.2
  whiskerLeft X _ _ f := whiskerLeft X.1 f.1 ×ₘ whiskerLeft X.2 f.2
  whiskerRight f X := whiskerRight f.1 X.1 ×ₘ whiskerRight f.2 X.2
  tensorHom_def := by simp [tensorHom_def]
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (fun_ X₁).prod (fun_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)

中文:
实例 prodMonoidal
  签名: : 幺半群范畴 (C₁ × C₂) where
  定义体: (X.1 otimes Y.1, X.2 otimes Y.2)
  tensorHom f g := (f.1 otimesₘ g.1) ×ₘ f.2 otimesₘ g.2
  whiskerLeft X _ _ f := whiskerLeft X.1 f.1 ×ₘ whiskerLeft X.2 f.2
  whiskerRight f X := whiskerRight f.1 X.1 ×ₘ whiskerRight f.2 X.2
  tensorHom_def := by simp [tensorHom_def]
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (fun_ X₁).prod (fun_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)

Depends on / 依赖: otimes
-/
instance prodMonoidal : MonoidalCategory (C₁ × C₂) where
  tensorObj X Y := (X.1 otimes Y.1, X.2 otimes Y.2)
  tensorHom f g := (f.1 otimesₘ g.1) ×ₘ f.2 otimesₘ g.2
  whiskerLeft X _ _ f := whiskerLeft X.1 f.1 ×ₘ whiskerLeft X.2 f.2
  whiskerRight f X := whiskerRight f.1 X.1 ×ₘ whiskerRight f.2 X.2
  tensorHom_def := by simp [tensorHom_def]
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (fun_ X₁).prod (fun_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)

end

end MonoidalCategory

namespace NatTrans

variable {J : Type*} [Category* J] {C : Type*} [Category* C] [MonoidalCategory C]
  {F G F' G' : J ⥤ C} (α : F ⟶ F') (β : G ⟶ G')

@[reassoc]
/--
lemma `tensor_naturality` / 引理 `tensor_naturality`

English:
lemma tensor_naturality
  given: {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y')
  proof: by simp

@[reassoc]

中文:
引理 tensor_naturality
  条件: {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y')
  证明: by simp

@[reassoc]
-/
lemma tensor_naturality {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f otimesₘ G.map g) ≫ (α.app Y otimesₘ β.app Y') =
      (α.app X otimesₘ β.app X') ≫ (F'.map f otimesₘ G'.map g) := by simp

@[reassoc]
/--
lemma `whiskerRight_app_tensor_app` / 引理 `whiskerRight_app_tensor_app`

English:
lemma whiskerRight_app_tensor_app
  given: {X Y : J} (f : X ⟶ Y) (X' : J)
  proof: by
  simpa using tensor_naturality α β f (𝟙 X')

@[reassoc]

中文:
引理 whiskerRight_app_tensor_app
  条件: {X Y : J} (f : X ⟶ Y) (X' : J)
  证明: by
  simpa using tensor_naturality α β f (𝟙 X')

@[reassoc]

Depends on / 依赖: tensor_naturality
-/
lemma whiskerRight_app_tensor_app {X Y : J} (f : X ⟶ Y) (X' : J) :
    F.map f ▷ G.obj X' ≫ (α.app Y otimesₘ β.app X') =
      (α.app X otimesₘ β.app X') ≫ F'.map f ▷ (G'.obj X') := by
  simpa using tensor_naturality α β f (𝟙 X')

@[reassoc]
/--
lemma `whiskerLeft_app_tensor_app` / 引理 `whiskerLeft_app_tensor_app`

English:
lemma whiskerLeft_app_tensor_app
  given: {X' Y' : J} (f : X' ⟶ Y') (X : J)
  proof: by
  simpa using tensor_naturality α β (𝟙 X) f

中文:
引理 whiskerLeft_app_tensor_app
  条件: {X' Y' : J} (f : X' ⟶ Y') (X : J)
  证明: by
  simpa using tensor_naturality α β (𝟙 X) f

Depends on / 依赖: tensor_naturality
-/
lemma whiskerLeft_app_tensor_app {X' Y' : J} (f : X' ⟶ Y') (X : J) :
    F.obj X ◁ G.map f ≫ (α.app X otimesₘ β.app Y') =
      (α.app X otimesₘ β.app X') ≫ F'.obj X ◁ G'.map f := by
  simpa using tensor_naturality α β (𝟙 X) f

end NatTrans

section ObjectProperty

open ObjectProperty

set_option backward.isDefEq.respectTransparency.types false in
-- See note [reducible non-instances]
/--
Definition of `MonoidalCategory.fullSubcategory` / `MonoidalCategory.fullSubcategory` 的定义

English:
abbreviation MonoidalCategory.fullSubcategory
  body: ⟨X.1 otimes Y.1, tensorObj X.1 Y.1 X.2 Y.2⟩
  whiskerLeft X _ _ f := homMk (X.obj ◁ f.hom)
  whiskerRight f X := homMk (f.hom ▷ X.obj)
  tensorHom f g := homMk (f.hom otimesₘ g.hom)
  tensorUnit := ⟨𝟙_ C, tensorUnit⟩
  associator X Y Z := P.fullyFaithfulι.preimageIso (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.fullyFaithfulι.preimageIso (fun_ X.1)
  rightUnitor X := P.fullyFaithfulι.preimageIso (ρ_ X.1)
  tensorHom_def _ _ := by ext; apply tensorHom_def

中文:
缩写 幺半群范畴.fullSubcategory
  定义体: ⟨X.1 otimes Y.1, tensorObj X.1 Y.1 X.2 Y.2⟩
  whiskerLeft X _ _ f := homMk (X.obj ◁ f.hom)
  whiskerRight f X := homMk (f.hom ▷ X.obj)
  tensorHom f g := homMk (f.hom otimesₘ g.hom)
  tensorUnit := ⟨𝟙_ C, tensorUnit⟩
  associator X Y Z := P.fullyFaithfulι.preimageIso (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.fullyFaithfulι.preimageIso (fun_ X.1)
  rightUnitor X := P.fullyFaithfulι.preimageIso (ρ_ X.1)
  tensorHom_def _ _ := by ext; apply tensorHom_def

Depends on / 依赖: otimes, tensorObj
-/
abbrev MonoidalCategory.fullSubcategory
    {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : ObjectProperty C)
    (tensorUnit : P (𝟙_ C))
    (tensorObj : forall X Y, P X -> P Y -> P (X otimes Y)) :
    MonoidalCategory P.FullSubcategory where
  tensorObj X Y := ⟨X.1 otimes Y.1, tensorObj X.1 Y.1 X.2 Y.2⟩
  whiskerLeft X _ _ f := homMk (X.obj ◁ f.hom)
  whiskerRight f X := homMk (f.hom ▷ X.obj)
  tensorHom f g := homMk (f.hom otimesₘ g.hom)
  tensorUnit := ⟨𝟙_ C, tensorUnit⟩
  associator X Y Z := P.fullyFaithfulι.preimageIso (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.fullyFaithfulι.preimageIso (fun_ X.1)
  rightUnitor X := P.fullyFaithfulι.preimageIso (ρ_ X.1)
  tensorHom_def _ _ := by ext; apply tensorHom_def

end ObjectProperty

end CategoryTheory
