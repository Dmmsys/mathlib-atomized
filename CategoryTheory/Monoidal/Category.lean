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

/-- Auxiliary structure to carry only the data fields of (and provide notation for)
`MonoidalCategory`. -/
/-
**CategoryTheory.MonoidalCategoryStruct** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory
`。
形式化陈述：MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where /-- curried
 tensor product of objects -/ tensorObj : C -> C -> C /-- left whiskering for mo
rphisms -/ whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tens
orObj X Y₂ /-- right whiskering for morphisms -/ whiskerRight {X₁ X₂ : C} (f : X
₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y /-- Tensor product of identity
 maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/ -- By default, it is defi
ned in terms of whiskering
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary structure to carry only the data fields of (and provide notation for)
`MonoidalCategory`.
-/
class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C → C → C
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
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X

namespace MonoidalCategory

export MonoidalCategoryStruct
  (tensorObj whiskerLeft whiskerRight tensorHom tensorUnit associator leftUnitor rightUnitor)

end MonoidalCategory

namespace MonoidalCategory

/-- Notation for `tensorObj`, the tensor product of objects in a monoidal category -/
scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorObj

/-- Notation for the `whiskerLeft` operator of monoidal categories -/
scoped infixr:81 " ◁ " => MonoidalCategoryStruct.whiskerLeft

/-- Notation for the `whiskerRight` operator of monoidal categories -/
scoped infixl:81 " ▷ " => MonoidalCategoryStruct.whiskerRight

/-- Notation for `tensorHom`, the tensor product of morphisms in a monoidal category -/
scoped infixr:70 " ⊗ₘ " => MonoidalCategoryStruct.tensorHom
-- TODO: Try setting this notation to `⊗` if the elaborator is improved and performs
-- better than currently on overloaded notations.

/-- Notation for `tensorUnit`, the two-sided identity of `⊗` -/
scoped notation "𝟙_ " C:arg => MonoidalCategoryStruct.tensorUnit C

/-- Notation for the monoidal `associator`: `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
scoped notation "α_" => MonoidalCategoryStruct.associator

/-- Notation for the `leftUnitor`: `𝟙_C ⊗ X ≃ X` -/
scoped notation "λ_" => MonoidalCategoryStruct.leftUnitor

/-- Notation for the `rightUnitor`: `X ⊗ 𝟙_C ≃ X` -/
scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

/-- The property that the pentagon relation is satisfied by four objects
in a category equipped with a `MonoidalCategoryStruct`. -/
/-
**CategoryTheory.MonoidalCategory.Pentagon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MonoidalCategory`。
形式化陈述：Pentagon {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C] (Y₁ Y₂ Y
₃ Y₄ : C) : Prop
参数：Y₁ Y₂ Y₃ Y₄ : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that the pentagon relation is satisfied by four objects
in a category equipped with a `MonoidalCategoryStruct`.
-/
def Pentagon {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ ⊗ Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ ⊗ Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ ⊗ Y₄)).hom

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
/-
**CategoryTheory.MonoidalCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategor
yStruct C where tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f 
otimesₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g)
参数：C : Type u；f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
继承自：MonoidalCategoryStruct C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  tensorHom_def {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := by
      cat_disch
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/
  id_tensorHom_id : ∀ X₁ X₂ : C, 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := by cat_disch
  /--
  Composition of tensor products is tensor product of compositions:
  `(f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)`
  -/
  tensorHom_comp_tensorHom :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
    cat_disch
  whiskerLeft_id : ∀ (X Y : C), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
    cat_disch
  id_whiskerRight : ∀ (X Y : C), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
    cat_disch
  /-- Naturality of the associator isomorphism: `(f₁ ⊗ₘ f₂) ⊗ₘ f₃ ≃ f₁ ⊗ₘ (f₂ ⊗ₘ f₃)` -/
  associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
    cat_disch
  /--
  Naturality of the left unitor, commutativity of `𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y ⟶ Y` and `𝟙_ C ⊗ X ⟶ X ⟶ Y`
  -/
  leftUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
    cat_disch
  /--
  Naturality of the right unitor: commutativity of `X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C ⟶ Y` and `X ⊗ 𝟙_ C ⟶ X ⟶ Y`
  -/
  rightUnitor_naturality :
    ∀ {X Y : C} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
    cat_disch
  /--
  The pentagon identity relating the isomorphism between `X ⊗ (Y ⊗ (Z ⊗ W))` and `((X ⊗ Y) ⊗ Z) ⊗ W`
  -/
  pentagon :
    ∀ W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    cat_disch
  /--
  The identity relating the isomorphisms between `X ⊗ (𝟙_ C ⊗ Y)`, `(X ⊗ 𝟙_ C) ⊗ Y` and `X ⊗ Y`
  -/
  triangle :
    ∀ X Y : C, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
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
A constructor for monoidal categories that requires `tensorHom` instead of `whiskerLeft` and
`whiskerRight`.
-/
/-
**CategoryTheory.MonoidalCategory.ofTensorHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.MonoidalCategory`。
形式化陈述：ofTensorHom {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C] (id_t
ensorHom_id : forall X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for monoidal categories that requires `tensorHom` instead of `whis
kerLeft` and
`whiskerRight`.
-/
abbrev ofTensorHom {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (id_tensorHom_id : ∀ X₁ X₂ : C, tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj X₁ X₂) := by
      cat_disch)
    (id_tensorHom : ∀ (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂), tensorHom (𝟙 X) f = whiskerLeft X f := by
      cat_disch)
    (tensorHom_id : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C), tensorHom f (𝟙 Y) = whiskerRight f Y := by
      cat_disch)
    (tensorHom_comp_tensorHom :
      ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
          cat_disch)
    (associator_naturality :
      ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
          (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
            cat_disch)
    (leftUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom (𝟙 (𝟙_ C)) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
          cat_disch)
    (rightUnitor_naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        tensorHom f (𝟙 (𝟙_ C)) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
          cat_disch)
    (pentagon :
      ∀ W X Y Z : C,
        tensorHom (associator W X Y).hom (𝟙 Z) ≫
            (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
          (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
            cat_disch)
    (triangle :
      ∀ X Y : C,
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
/-
**CategoryTheory.MonoidalCategory.id_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
参数：X : C；f : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_tensorHom (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    𝟙 X ⊗ₘ f = X ◁ f := by
  simp [tensorHom_def]

@[simp]
/-
**CategoryTheory.MonoidalCategory.tensorHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
参数：f : X₁ ⟶ X₂；Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorHom_id {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    f ⊗ₘ 𝟙 Y = f ▷ Y := by
  simp [tensorHom_def]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_comp (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g)
 = W ◁ f ≫ W ◁ g
参数：W : C；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_comp (W : C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g := by
  simp [← id_tensorHom]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.id_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：id_whiskerLeft {X Y : C} (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_
 Y).inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X Y : C} (f : X ⟶ Y),   CategoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_whiskerLeft {X Y : C} (f : X ⟶ Y) :
    𝟙_ C ◁ f = (λ_ X).hom ≫ f ≫ (λ_ Y).inv := by
  rw [← assoc, ← leftUnitor_naturality]; simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.tensor_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_whiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = 
(α_ X Y Z).hom ≫ X ◁ Y ◁ f ≫ (α_ X Y Z').inv
参数：X Y : C；f : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_whiskerLeft (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f ≫ (α_ X Y Z').inv := by
  simp only [← id_tensorHom]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.comp_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：comp_whiskerRight {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ 
Z = f ▷ Z ≫ g ▷ Z
参数：f : W ⟶ X；g : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_whiskerRight {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) :
    (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z := by
  simp [← tensorHom_id]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.whiskerRight_id** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_id {X Y : C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y)
.inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_naturality`：∀ {C : Type u} {
𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C]
 {X Y : C} (f : X ⟶ Y),   CategoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_id {X Y : C} (f : X ⟶ Y) :
    f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← assoc, ← rightUnitor_naturality]; simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.whiskerRight_tensor** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_tensor {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) =
 (α_ X Y Z).inv ≫ f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom
参数：f : X ⟶ X'；Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_tensor {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom := by
  simp only [← tensorHom_id]
  rw [associator_naturality]
  simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.whisker_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalCategory`。
形式化陈述：whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ 
X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X Y' Z).inv
参数：X : C；f : Y ⟶ Y'；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whisker_assoc (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X Y' Z).inv := by
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [← assoc, ← associator_naturality]
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.whisker_exchange** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：whisker_exchange {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f
 ▷ Y ≫ X ◁ g
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whisker_exchange {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensorHom_def'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g
 = X₁ ◁ g ≫ f ▷ Y₂
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
-/
theorem tensorHom_def' {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = X₁ ◁ g ≫ f ▷ Y₂ :=
  whisker_exchange f g ▸ tensorHom_def f g

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_comp_tensorHom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_comp_tensorHom {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y 
⟶ Z) : (V ◁ g) ≫ (f otimesₘ h) = f otimesₘ (g ≫ h)
参数：f : V ⟶ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_comp_tensorHom {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (V ◁ g) ≫ (f ⊗ₘ h) = f ⊗ₘ (g ≫ h) := by
  simp [tensorHom_def']

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_comp_tensorHom {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V
 ⟶ W) : (f ▷ V) ≫ (g otimesₘ h) = (f ≫ g) otimesₘ h
参数：f : X ⟶ Y；g : Y ⟶ Z；h : V ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_comp_tensorHom {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ▷ V) ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerLeft** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensorHom_comp_whiskerLeft {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y 
⟶ Z) : (f otimesₘ g) ≫ (W ◁ h) = f otimesₘ (g ≫ h)
参数：f : V ⟶ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorHom_comp_whiskerLeft {V W X Y Z : C} (f : V ⟶ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ₘ g) ≫ (W ◁ h) = f ⊗ₘ (g ≫ h) := by
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerRight** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensorHom_comp_whiskerRight {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V
 ⟶ W) : (f otimesₘ h) ≫ (g ▷ W) = (f ≫ g) otimesₘ h
参数：f : X ⟶ Y；g : Y ⟶ Z；h : V ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorHom_comp_whiskerRight {V W X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : V ⟶ W) :
    (f ⊗ₘ h) ≫ (g ▷ W) = (f ≫ g) ⊗ₘ h := by
  simp [tensorHom_def, whisker_exchange]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_inv_comp_tensorHom** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y Z : C}   (f : CategoryTheory.MonoidalCategorySt
ruct.tensorUnit C ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp (Catego
ryTheory.MonoidalCategoryStruct.leftUnitor X).inv       (CategoryTheory.Monoidal
CategoryStruct.tensorHom f g) =     CategoryTheory.CategoryStruct.comp g       (
CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.leftUn
itor Z).inv         (CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z))
参数：f : CategoryTheory.MonoidalCategoryStruct.tensorUnit C ⟶ Y；g : X ⟶ Z；Category
Theory.MonoidalCategoryStruct.leftUnitor X；CategoryTheory.MonoidalCategoryStruct
.tensorHom f g；CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCatego
ryStruct.leftUnitor Z).inv         (CategoryTheory.MonoidalCategoryStruct.whiske
rRight f Z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[reassoc] lemma leftUnitor_inv_comp_tensorHom {X Y Z : C} (f : 𝟙_ C ⟶ Y) (g : X ⟶ Z) :
    (λ_ X).inv ≫ (f ⊗ₘ g) = g ≫ (λ_ Z).inv ≫ f ▷ Z := by simp [tensorHom_def']
/-
**CategoryTheory.MonoidalCategory.rightUnitor_inv_comp_tensorHom** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C] {X Y Z : C}   (f : X ⟶ Y) (g : CategoryTheory.Monoid
alCategoryStruct.tensorUnit C ⟶ Z),   CategoryTheory.CategoryStruct.comp (Catego
ryTheory.MonoidalCategoryStruct.rightUnitor X).inv       (CategoryTheory.Monoida
lCategoryStruct.tensorHom f g) =     CategoryTheory.CategoryStruct.comp f       
(CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.right
Unitor Y).inv         (CategoryTheory.MonoidalCategoryStruct.whiskerLeft Y g))
参数：f : X ⟶ Y；g : CategoryTheory.MonoidalCategoryStruct.tensorUnit C ⟶ Z；Category
Theory.MonoidalCategoryStruct.rightUnitor X；CategoryTheory.MonoidalCategoryStruc
t.tensorHom f g；CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCateg
oryStruct.rightUnitor Y).inv         (CategoryTheory.MonoidalCategoryStruct.whis
kerLeft Y g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[reassoc] lemma rightUnitor_inv_comp_tensorHom {X Y Z : C} (f : X ⟶ Y) (g : 𝟙_ C ⟶ Z) :
    (ρ_ X).inv ≫ (f ⊗ₘ g) = f ≫ (ρ_ Y).inv ≫ Y ◁ g := by simp [tensorHom_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_hom_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) : X ◁ f.hom ≫ X ◁ f.inv 
= 𝟙 (X otimes Y)
参数：X : C；f : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
-/
theorem whiskerLeft_hom_inv (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.hom ≫ X ◁ f.inv = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.hom_inv_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：hom_inv_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) : f.hom ▷ Z ≫ f.inv ▷ Z
 = 𝟙 (X otimes Z)
参数：f : X ≅ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
-/
theorem hom_inv_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.hom ▷ Z ≫ f.inv ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) : X ◁ f.inv ≫ X ◁ f.hom 
= 𝟙 (X otimes Z)
参数：X : C；f : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
-/
theorem whiskerLeft_inv_hom (X : C) {Y Z : C} (f : Y ≅ Z) :
    X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.inv_hom_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：inv_hom_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) : f.inv ▷ Z ≫ f.hom ▷ Z
 = 𝟙 (Y otimes Z)
参数：f : X ≅ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
-/
theorem inv_hom_whiskerRight {X Y : C} (f : X ≅ Y) (Z : C) :
    f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_hom_inv'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : X ◁ f ≫ X ◁
 inv f = 𝟙 (X otimes Y)
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
-/
theorem whiskerLeft_hom_inv' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ f ≫ X ◁ inv f = 𝟙 (X ⊗ Y) := by
  rw [← whiskerLeft_comp, IsIso.hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.hom_inv_whiskerRight'** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MonoidalCategory`。
形式化陈述：hom_inv_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) : f ▷ Z ≫ in
v f ▷ Z = 𝟙 (X otimes Z)
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
-/
theorem hom_inv_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    f ▷ Z ≫ inv f ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : X ◁ inv f ≫
 X ◁ f = 𝟙 (X otimes Z)
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
-/
theorem whiskerLeft_inv_hom' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    X ◁ inv f ≫ X ◁ f = 𝟙 (X ⊗ Z) := by
  rw [← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.inv_hom_whiskerRight'** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MonoidalCategory`。
形式化陈述：inv_hom_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) : inv f ▷ Z 
≫ f ▷ Z = 𝟙 (Y otimes Z)
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
-/
theorem inv_hom_whiskerRight' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    inv f ▷ Z ≫ f ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight]

/-- The left whiskering of an isomorphism is an isomorphism. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.whiskerLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：whiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X otimes Y ≅ X otimes Z whe
re hom
参数：X : C；f : Y ≅ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left whiskering of an isomorphism is an isomorphism.
-/
def whiskerLeftIso (X : C) {Y Z : C} (f : Y ≅ Z) : X ⊗ Y ≅ X ⊗ Z where
  hom := X ◁ f.hom
  inv := X ◁ f.inv
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_isIso** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ f)
参数：X : C；f : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance whiskerLeft_isIso (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : IsIso (X ◁ f) :=
  (whiskerLeftIso X (asIso f)).isIso_hom

@[simp, push]
/-
**CategoryTheory.MonoidalCategory.inv_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X 
◁ inv f
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_hom_inv'`：whiskerLeft_hom_in
v' (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] : X ◁ f ≫ X ◁ inv f = 𝟙 (X otimes Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    inv (X ◁ f) = X ◁ inv f := by
  cat_disch

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeftIso_refl** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeftIso_refl (W X : C) : whiskerLeftIso W (Iso.refl X) = Iso.refl (
W otimes X)
参数：W X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
-/
lemma whiskerLeftIso_refl (W X : C) :
    whiskerLeftIso W (Iso.refl X) = Iso.refl (W ⊗ X) :=
  Iso.ext (whiskerLeft_id W X)

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeftIso_trans** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) : whisker
LeftIso W (f ≪≫ g) = whiskerLeftIso W f ≪≫ whiskerLeftIso W g
参数：W : C；f : X ≅ Y；g : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
-/
lemma whiskerLeftIso_trans (W : C) {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
    whiskerLeftIso W (f ≪≫ g) = whiskerLeftIso W f ≪≫ whiskerLeftIso W g :=
  Iso.ext (whiskerLeft_comp W f.hom g.hom)

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeftIso_symm** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) : (whiskerLeftIso W f).s
ymm = whiskerLeftIso W f.symm
参数：W : C；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeftIso_symm (W : C) {X Y : C} (f : X ≅ Y) :
    (whiskerLeftIso W f).symm = whiskerLeftIso W f.symm := rfl

/-- The right whiskering of an isomorphism is an isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.whiskerRightIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X otimes Z ≅ Y otimes Z wh
ere hom
参数：f : X ≅ Y；Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right whiskering of an isomorphism is an isomorphism.
-/
def whiskerRightIso {X Y : C} (f : X ≅ Y) (Z : C) : X ⊗ Z ≅ Y ⊗ Z where
  hom := f.hom ▷ Z
  inv := f.inv ▷ Z
/-
**CategoryTheory.MonoidalCategory.whiskerRight_isIso** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z)
参数：f : X ⟶ Y；Z : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance whiskerRight_isIso {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : IsIso (f ▷ Z) :=
  (whiskerRightIso (asIso f) Z).isIso_hom

@[simp, push]
/-
**CategoryTheory.MonoidalCategory.inv_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = i
nv f ▷ Z
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.hom_inv_whiskerRight'`：hom_inv_whiskerRi
ght' {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) : f ▷ Z ≫ inv f ▷ Z = 𝟙 (X otimes Z
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) [IsIso f] :
    inv (f ▷ Z) = inv f ▷ Z := by
  cat_disch

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerRightIso_refl** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRightIso_refl (X W : C) : whiskerRightIso (Iso.refl X) W = Iso.refl
 (X otimes W)
参数：X W : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
-/
lemma whiskerRightIso_refl (X W : C) :
    whiskerRightIso (Iso.refl X) W = Iso.refl (X ⊗ W) :=
  Iso.ext (id_whiskerRight X W)

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerRightIso_trans** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) : whiske
rRightIso (f ≪≫ g) W = whiskerRightIso f W ≪≫ whiskerRightIso g W
参数：f : X ≅ Y；g : Y ≅ Z；W : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
-/
lemma whiskerRightIso_trans {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) (W : C) :
    whiskerRightIso (f ≪≫ g) W = whiskerRightIso f W ≪≫ whiskerRightIso g W :=
  Iso.ext (comp_whiskerRight f.hom g.hom W)

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerRightIso_symm** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) : (whiskerRightIso f W)
.symm = whiskerRightIso f.symm W
参数：f : X ≅ Y；W : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRightIso_symm {X Y : C} (f : X ≅ Y) (W : C) :
    (whiskerRightIso f W).symm = whiskerRightIso f.symm W := rfl

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.tensorIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MonoidalCategory`。
形式化陈述：tensorIso {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') : X otimes X' ≅ Y otim
es Y' where hom
参数：f : X ≅ Y；g : X' ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two isomorphisms is an isomorphism.
-/
def tensorIso {X Y X' Y' : C} (f : X ≅ Y)
    (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' where
  hom := f.hom ⊗ₘ g.hom
  inv := f.inv ⊗ₘ g.inv
  hom_inv_id := by simp [Iso.hom_inv_id, Iso.hom_inv_id]
  inv_hom_id := by simp [Iso.inv_hom_id, Iso.inv_hom_id]

/-- Notation for `tensorIso`, the tensor product of isomorphisms -/
scoped infixr:70 " ⊗ᵢ " => tensorIso
-- TODO: Try setting this notation to `⊗` if the elaborator is improved and performs
-- better than currently on overloaded notations.

@[inherit_doc whiskerLeftIso]
scoped infixr:81 " ◁ᵢ " => whiskerLeftIso

@[inherit_doc whiskerRightIso]
scoped infixl:81 " ▷ᵢ " => whiskerRightIso

/-
**CategoryTheory.MonoidalCategory.tensorIso_def** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalCategory`。
形式化陈述：tensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') : f otimesᵢ g = wh
iskerRightIso f X' ≪≫ whiskerLeftIso Y g
参数：f : X ≅ Y；g : X' ≅ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
-/
theorem tensorIso_def {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ᵢ g = whiskerRightIso f X' ≪≫ whiskerLeftIso Y g :=
  Iso.ext (tensorHom_def f.hom g.hom)
/-
**CategoryTheory.MonoidalCategory.tensorIso_def'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：tensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') : f otimesᵢ g = w
hiskerLeftIso X g ≪≫ whiskerRightIso f Y'
参数：f : X ≅ Y；g : X' ≅ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
-/
theorem tensorIso_def' {X Y X' Y' : C} (f : X ≅ Y) (g : X' ≅ Y') :
    f ⊗ᵢ g = whiskerLeftIso X g ≪≫ whiskerRightIso f Y' :=
  Iso.ext (tensorHom_def' f.hom g.hom)
/-
**CategoryTheory.MonoidalCategory.tensor_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : I
sIso (f otimesₘ g)
参数：f : W ⟶ X；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance tensor_isIso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ₘ g) :=
  (asIso f ⊗ᵢ asIso g).isIso_hom

@[simp, push]
/-
**CategoryTheory.MonoidalCategory.inv_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.MonoidalCategory`。
形式化陈述：inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : inv
 (f otimesₘ g) = inv f otimesₘ inv g
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    inv (f ⊗ₘ g) = inv f ⊗ₘ inv g := by
  simp [tensorHom_def, whisker_exchange]

variable {W X Y Z : C}
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_dite** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_dite {P : Prop} [Decidable P] (X : C) {Y Z : C} (f : P -> (Y ⟶
 Z)) (f' : ¬P -> (Y ⟶ Z)) : X ◁ (if h : P then f h else f' h) = if h : P then X 
◁ f h else X ◁ f' h
参数：X : C；f : P -> (Y ⟶ Z)；f' : ¬P -> (Y ⟶ Z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem whiskerLeft_dite {P : Prop} [Decidable P]
    (X : C) {Y Z : C} (f : P → (Y ⟶ Z)) (f' : ¬P → (Y ⟶ Z)) :
      X ◁ (if h : P then f h else f' h) = if h : P then X ◁ f h else X ◁ f' h := by
  split_ifs <;> rfl
/-
**CategoryTheory.MonoidalCategory.dite_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：dite_whiskerRight {P : Prop} [Decidable P] {X Y : C} (f : P -> (X ⟶ Y)) (f
' : ¬P -> (X ⟶ Y)) (Z : C) : (if h : P then f h else f' h) ▷ Z = if h : P then f
 h ▷ Z else f' h ▷ Z
参数：f : P -> (X ⟶ Y)；f' : ¬P -> (X ⟶ Y)；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem dite_whiskerRight {P : Prop} [Decidable P]
    {X Y : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (Z : C) :
      (if h : P then f h else f' h) ▷ Z = if h : P then f h ▷ Z else f' h ▷ Z := by
  split_ifs <;> rfl
/-
**CategoryTheory.MonoidalCategory.tensor_dite** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoidalCategory`。
形式化陈述：tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (
Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f otimesₘ if h : P then g h else g' h) = if h : 
P then f otimesₘ g h else f otimesₘ g' h
参数：f : W ⟶ X；g : P -> (Y ⟶ Z)；g' : ¬P -> (Y ⟶ Z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (f ⊗ₘ if h : P then g h else g' h) =
    if h : P then f ⊗ₘ g h else f ⊗ₘ g' h := by split_ifs <;> rfl
/-
**CategoryTheory.MonoidalCategory.dite_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.MonoidalCategory`。
形式化陈述：dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P -> (
Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (if h : P then g h else g' h) otimesₘ f = if h : 
P then g h otimesₘ f else g' h otimesₘ f
参数：f : W ⟶ X；g : P -> (Y ⟶ Z)；g' : ¬P -> (Y ⟶ Z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z))
    (g' : ¬P → (Y ⟶ Z)) : (if h : P then g h else g' h) ⊗ₘ f =
    if h : P then g h ⊗ₘ f else g' h ⊗ₘ f := by split_ifs <;> rfl

@[simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) : X ◁ eqToHom f = eqToHo
m (congr_arg₂ tensorObj rfl f)
参数：X : C；f : Y = Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem whiskerLeft_eqToHom (X : C) {Y Z : C} (f : Y = Z) :
    X ◁ eqToHom f = eqToHom (congr_arg₂ tensorObj rfl f) := by
  cases f
  simp only [whiskerLeft_id, eqToHom_refl]

@[simp]
/-
**CategoryTheory.MonoidalCategory.eqToHom_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：eqToHom_whiskerRight {X Y : C} (f : X = Y) (Z : C) : eqToHom f ▷ Z = eqToH
om (congr_arg₂ tensorObj f rfl)
参数：f : X = Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_whiskerRight {X Y : C} (f : X = Y) (Z : C) :
    eqToHom f ▷ Z = eqToHom (congr_arg₂ tensorObj f rfl) := by
  cases f
  simp only [id_whiskerRight, eqToHom_refl]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_naturality_left** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ Y ▷ Z ≫
 (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y otimes Z)
参数：f : X ⟶ X'；Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_inv_naturality_left** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y 
otimes Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z
参数：f : X ⟶ X'；Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.whiskerRight_tensor_symm** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_tensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ Y ▷ Z = (
α_ X Y Z).hom ≫ f ▷ (Y otimes Z) ≫ (α_ X' Y Z).inv
参数：f : X ⟶ X'；Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_tensor_symm {X X' : C} (f : X ⟶ X') (Y Z : C) :
    f ▷ Y ▷ Z = (α_ X Y Z).hom ≫ f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_naturality_middle** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) : (X 
◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z
参数：X : C；f : Y ⟶ Y'；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_inv_naturality_middle** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
 X ◁ f ▷ Z ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z
参数：X : C；f : Y ⟶ Y'；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.whisker_assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) : X ◁ f ▷ Z = (
α_ X Y Z).inv ≫ (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom
参数：X : C；f : Y ⟶ Y'；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whisker_assoc_symm (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    X ◁ f ▷ Z = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z ≫ (α_ X Y' Z).hom := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_naturality_right** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes 
Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
参数：X Y : C；f : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_inv_naturality_right** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : X ◁ Y 
◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X otimes Y) ◁ f
参数：X Y : C；f : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f ≫ (α_ X Y Z').inv = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_whiskerLeft_symm** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_whiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : X ◁ Y ◁ f = (α
_ X Y Z).inv ≫ (X otimes Y) ◁ f ≫ (α_ X Y Z').hom
参数：X Y : C；f : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_whiskerLeft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    X ◁ Y ◁ f = (α_ X Y Z).inv ≫ (X ⊗ Y) ◁ f ≫ (α_ X Y Z').hom := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) : f ≫ (fun_ Y).inv = (fun_
 X).inv ≫ _ ◁ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv = (λ_ X).inv ≫ _ ◁ f := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.id_whiskerLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') : f = (fun_ X).inv ≫ 𝟙_ C ◁ f 
≫ (fun_ X').hom
参数：f : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_whiskerLeft_symm {X X' : C} (f : X ⟶ X') :
    f = (λ_ X).inv ≫ 𝟙_ C ◁ f ≫ (λ_ X').hom := by
  simp only [id_whiskerLeft, assoc, inv_hom_id, comp_id, inv_hom_id_assoc]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') : f ≫ (ρ_ X').inv = (ρ_
 X).inv ≫ f ▷ _
参数：f : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_inv_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ f ▷ _ := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.whiskerRight_id_symm** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_id_symm {X Y : C} (f : X ⟶ Y) : f = (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (
ρ_ Y).hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_id_symm {X Y : C} (f : X ⟶ Y) :
    f = (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom := by
  simp
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem whiskerLeft_iff {X Y : C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g := by simp
/-
**CategoryTheory.MonoidalCategory.whiskerRight_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：whiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem whiskerRight_iff {X Y : C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g := by simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/

section

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv : W ◁ (α_ X Y Z).inv ≫ (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y)
.inv ▷ Z = (α_ W X (Y otimes Z)).inv ≫ (α_ (W otimes X) Y Z).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (W X Y Z : C)
,   CategoryTheory.CategoryStr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom_hom_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv_inv_hom_hom_inv : (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv 
▷ Z ≫ (α_ (W otimes X) Y Z).hom = W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y otimes Z)).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_inv_hom_hom_inv :
    (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom =
      W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv := by
  rw [← cancel_epi (W ◁ (α_ X Y Z).inv), ← cancel_mono (α_ (W ⊗ X) Y Z).inv]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv_hom_hom_hom_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv_hom_hom_hom_inv : (α_ (W otimes X) Y Z).inv ≫ (α_ W X Y).hom 
▷ Z ≫ (α_ W (X otimes Y) Z).hom = (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom_hom_inv`：pentagon_i
nv_inv_hom_hom_inv : (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W oti
mes X) Y Z).hom = W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y …
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_hom_hom_hom_inv :
    (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom =
      (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_hom_inv_inv_inv_inv : W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y otimes Z)).
inv ≫ (α_ (W otimes X) Y Z).inv = (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv`：pentagon_inv : W ◁ (α_ X Y
 Z).inv ≫ (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z = (α_ W X (Y otimes Z))
.inv ≫ (α_ (W otimes X) Y Z).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_inv_inv_inv_inv :
    W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv =
      (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z := by
  simp [← cancel_epi (W ◁ (α_ X Y Z).inv)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_hom_hom_inv_hom_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_hom_hom_inv_hom_hom : (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otim
es Z)).hom ≫ W ◁ (α_ X Y Z).inv = (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv`：pentagon_h
om_inv_inv_inv_inv : W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y otimes Z)).inv ≫ (α_ (W oti
mes X) Y Z).inv = (α_ W (X otimes Y) Z).inv ≫ (α_ …
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_hom_inv_hom_hom :
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv =
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_hom_inv_inv_inv_hom : (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).
inv ≫ (α_ W (X otimes Y) Z).inv = (α_ (W otimes X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv`：pentagon_inv : W ◁ (α_ X Y
 Z).inv ≫ (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z = (α_ W X (Y otimes Z))
.inv ≫ (α_ (W otimes X) Y Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.hom_inv_whiskerRight`：hom_inv_whiskerRig
ht {X Y : C} (f : X ≅ Y) (Z : C) : f.hom ▷ Z ≫ f.inv ▷ Z = 𝟙 (X otimes Z)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_inv_inv_inv_hom :
    (α_ W X (Y ⊗ Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv =
      (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z := by
  rw [← cancel_epi (α_ W X (Y ⊗ Z)).inv, ← cancel_mono ((α_ W X Y).inv ▷ Z)]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_hom_hom_inv_inv_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_hom_hom_inv_inv_hom : (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).
hom ≫ (α_ W X (Y otimes Z)).inv = (α_ W X Y).inv ▷ Z ≫ (α_ (W otimes X) Y Z).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_hom`：pentagon_h
om_inv_inv_inv_hom : (α_ W X (Y otimes Z)).hom ≫ W ◁ (α_ X Y Z).inv ≫ (α_ W (X o
times Y) Z).inv = (α_ (W otimes X) Y Z).inv ≫ (α_ …
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_hom_inv_inv_hom :
    (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y ⊗ Z)).inv =
      (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv_hom_hom_hom_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv_hom_hom_hom_hom : (α_ W X Y).inv ▷ Z ≫ (α_ (W otimes X) Y Z).
hom ≫ (α_ W X (Y otimes Z)).hom = (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.hom_inv_whiskerRight_assoc`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCa
tegory C] {X Y : C}   (f : X ≅ Y) (Z : C) {Z_1 :…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (W X Y Z : C)
,   CategoryTheory.CategoryStr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_hom_hom_hom_hom :
    (α_ W X Y).inv ▷ Z ≫ (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom =
      (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom := by
  simp [← cancel_epi ((α_ W X Y).hom ▷ Z)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom_inv_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：pentagon_inv_inv_hom_inv_inv : (α_ W X (Y otimes Z)).inv ≫ (α_ (W otimes X
) Y Z).inv ≫ (α_ W X Y).hom ▷ Z = W ◁ (α_ X Y Z).inv ≫ (α_ W (X otimes Y) Z).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_hom_hom_hom_hom`：pentagon_i
nv_hom_hom_hom_hom : (α_ W X Y).inv ▷ Z ≫ (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y
 otimes Z)).hom = (α_ W (X otimes Y) Z).hom ≫ W ◁ …
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_inv_hom_inv_inv :
    (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv ≫ (α_ W X Y).hom ▷ Z =
      W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.triangle_assoc_comp_right** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：triangle_assoc_comp_right (X Y : C) : (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ 
Y) = X ◁ (fun_ Y).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.triangle`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : C),   
CategoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem triangle_assoc_comp_right (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom := by
  rw [← triangle, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_inv** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：triangle_assoc_comp_right_inv (X Y : C) : (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y)
.hom = X ◁ (fun_ Y).inv
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : C),   
CategoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.MonoidalCategory.inv_hom_whiskerRight`：inv_hom_whiskerRig
ht {X Y : C} (f : X ≅ Y) (Z : C) : f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y otimes Z)
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom`：whiskerLeft_inv_hom
 (X : C) {Y Z : C} (f : Y ≅ Z) : X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X otimes Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem triangle_assoc_comp_right_inv (X Y : C) :
    (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y).hom = X ◁ (λ_ Y).inv := by
  simp [← cancel_mono (X ◁ (λ_ Y).hom)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：triangle_assoc_comp_left_inv (X Y : C) : (X ◁ (fun_ Y).inv) ≫ (α_ X (𝟙_ C)
 Y).inv = (ρ_ X).inv ▷ Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right`：triangle_asso
c_comp_right (X Y : C) : (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (fun_ Y).h
om
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom`：whiskerLeft_inv_hom
 (X : C) {Y Z : C} (f : Y ≅ Z) : X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X otimes Z)
· 使用定理 `CategoryTheory.MonoidalCategory.inv_hom_whiskerRight`：inv_hom_whiskerRig
ht {X Y : C} (f : X ≅ Y) (Z : C) : f.inv ▷ Z ≫ f.hom ▷ Z = 𝟙 (Y otimes Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem triangle_assoc_comp_left_inv (X Y : C) :
    (X ◁ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  simp [← cancel_mono ((ρ_ X).hom ▷ Y)]

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight X Y : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`.
-/
@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_whiskerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom
 ≫ (fun_ (X otimes Y)).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_iff`：whiskerLeft_iff {X Y : 
C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_assoc`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (W X Y 
Z : C) {Z_1 : C}   (h :     Category…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : C),   
CategoryTheory.CategoryStruct.…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality_middle`：associator
_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z ≫ (α_ X
 Y' Z).hom = (α_ X Y Z).hom ≫ X ◁ f ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality_left`：associator_n
aturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ Y ▷ Z ≫ (α_ X' Y Z).hom =
 (α_ X Y Z).hom ≫ f ▷ (Y otimes Z)

--- 原说明 ---
We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight X Y : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)`.
-/
theorem leftUnitor_whiskerRight (X Y : C) :
    (λ_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, ← cancel_epi (α_ _ _ _).hom, ←
      cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_whiskerRight_assoc, triangle, associator_naturality_left]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_inv_whiskerRight (X Y : C) : (fun_ X).inv ▷ Y = (fun_ (X otimes
 Y)).inv ≫ (α_ (𝟙_ C) X Y).inv
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight`：leftUnitor_whis
kerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)
).hom
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_inv_whiskerRight (X Y : C) :
    (λ_ X).inv ▷ Y = (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ C) X Y).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_rightUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫
 (ρ_ (X otimes Y)).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_iff`：whiskerRight_iff {X Y 
: C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right`：triangle_asso
c_comp_right (X Y : C) : (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (fun_ Y).h
om
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_middle`：associ
ator_inv_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) : X ◁ f ▷ Z ≫
 (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ f) ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right`：associa
tor_inv_naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : X ◁ Y ◁ f ≫ (α_ X Y
 Z').inv = (α_ X Y Z).inv ≫ (X otimes Y) ◁ f
-/
theorem whiskerLeft_rightUnitor (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X ⊗ Y)).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv, ←
      cancel_epi (X ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, triangle_assoc_comp_right,
      associator_inv_naturality_right]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：whiskerLeft_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y))
.inv ≫ (α_ X Y (𝟙_ C)).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor`：whiskerLeft_rig
htUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).ho
m
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_rightUnitor_inv (X Y : C) :
    X ◁ (ρ_ Y).inv = (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_tensor_hom (X Y : C) : (fun_ (X otimes Y)).hom = (α_ (𝟙_ C) X Y
).inv ≫ (fun_ X).hom ▷ Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight`：leftUnitor_whis
kerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)
).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_tensor_hom (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_tensor_inv** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_tensor_inv (X Y : C) : (fun_ (X otimes Y)).inv = (fun_ X).inv ▷
 Y ≫ (α_ (𝟙_ C) X Y).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight`：leftUnitor_
inv_whiskerRight (X Y : C) : (fun_ X).inv ▷ Y = (fun_ (X otimes Y)).inv ≫ (α_ (𝟙
_ C) X Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_tensor_inv (X Y : C) :
    (λ_ (X ⊗ Y)).inv = (λ_ X).inv ▷ Y ≫ (α_ (𝟙_ C) X Y).hom := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.rightUnitor_tensor_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：rightUnitor_tensor_hom (X Y : C) : (ρ_ (X otimes Y)).hom = (α_ X Y (𝟙_ C))
.hom ≫ X ◁ (ρ_ Y).hom
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor`：whiskerLeft_rig
htUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).ho
m
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_tensor_hom (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：rightUnitor_tensor_inv (X Y : C) : (ρ_ (X otimes Y)).inv = X ◁ (ρ_ Y).inv 
≫ (α_ X Y (𝟙_ C)).inv
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv`：whiskerLeft
_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙
_ C)).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_tensor_inv (X Y : C) :
    (ρ_ (X ⊗ Y)).inv = X ◁ (ρ_ Y).inv ≫ (α_ X Y (𝟙_ C)).inv := by simp

end

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_inv_naturality** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (
h : Z ⟶ Z') : (f otimesₘ g otimesₘ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f
 otimesₘ g) otimesₘ h)
参数：f : X ⟶ X'；g : Y ⟶ Y'；h : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
  simp [tensorHom_def]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.associator_conjugation** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h :
 Z ⟶ Z') : (f otimesₘ g) otimesₘ h = (α_ X Y Z).hom ≫ (f otimesₘ g otimesₘ h) ≫ 
(α_ X' Y' Z').inv
参数：f : X ⟶ X'；g : Y ⟶ Y'；h : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality`：associator_in
v_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') : (f ot
imesₘ g otimesₘ h) ≫ (α_ X' Y' Z').inv = (α_ X …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g) ⊗ₘ h = (α_ X Y Z).hom ≫ (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_inv_conjugation** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') 
(h : Z ⟶ Z') : f otimesₘ g otimesₘ h = (α_ X Y Z).inv ≫ ((f otimesₘ g) otimesₘ h
) ≫ (α_ X' Y' Z').hom
参数：f : X ⟶ X'；g : Y ⟶ Y'；h : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ₘ g ⊗ₘ h = (α_ X Y Z).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom := by
  rw [associator_naturality, inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
/-
**CategoryTheory.MonoidalCategory.id_tensor_associator_naturality** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') : (𝟙 (X otimes
 Y) otimesₘ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X otimesₘ 𝟙 Y otimesₘ h)
参数：h : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom_id`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X₁ X₂
 : C),   CategoryTheory.MonoidalCateg…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
-/
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ₘ h) ≫ (α_ X Y Z').hom = (α_ X Y Z).hom ≫ (𝟙 X ⊗ₘ 𝟙 Y ⊗ₘ h) := by
  rw [← id_tensorHom_id, associator_naturality]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.id_tensor_associator_inv_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') : (f otime
sₘ 𝟙 (Y otimes Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f otimesₘ 𝟙 Y) otimesₘ
 𝟙 Z)
参数：f : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom_id`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X₁ X₂
 : C),   CategoryTheory.MonoidalCateg…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality`：associator_in
v_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') : (f ot
imesₘ g otimesₘ h) ≫ (α_ X' Y' Z').inv = (α_ X …
-/
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ₘ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ₘ 𝟙 Y) ⊗ₘ 𝟙 Z) := by
  rw [← id_tensorHom_id, associator_inv_naturality]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.hom_inv_id_tensor** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) : (f
.hom otimesₘ g) ≫ (f.inv otimesₘ h) = (𝟙 V otimesₘ g) ≫ (𝟙 V otimesₘ h)
参数：f : V ≅ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.hom ⊗ₘ g) ≫ (f.inv ⊗ₘ h) = (𝟙 V ⊗ₘ g) ≫ (𝟙 V ⊗ₘ h) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.inv_hom_id_tensor** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) : (f
.inv otimesₘ g) ≫ (f.hom otimesₘ h) = (𝟙 W otimesₘ g) ≫ (𝟙 W otimesₘ h)
参数：f : V ≅ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ₘ g) ≫ (f.hom ⊗ₘ h) = (𝟙 W ⊗ₘ g) ≫ (𝟙 W ⊗ₘ h) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_hom_inv_id** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) : (g
 otimesₘ f.hom) ≫ (h otimesₘ f.inv) = (g otimesₘ 𝟙 V) ≫ (h otimesₘ 𝟙 V)
参数：f : V ≅ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ f.hom) ≫ (h ⊗ₘ f.inv) = (g ⊗ₘ 𝟙 V) ≫ (h ⊗ₘ 𝟙 V) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_inv_hom_id** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) : (g
 otimesₘ f.inv) ≫ (h otimesₘ f.hom) = (g otimesₘ 𝟙 W) ≫ (h otimesₘ 𝟙 W)
参数：f : V ≅ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ f.inv) ≫ (h ⊗ₘ f.hom) = (g ⊗ₘ 𝟙 W) ≫ (h ⊗ₘ 𝟙 W) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.hom_inv_id_tensor'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : 
Y ⟶ Z) : (f otimesₘ g) ≫ (inv f otimesₘ h) = (𝟙 V otimesₘ g) ≫ (𝟙 V otimesₘ h)
参数：f : V ⟶ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ₘ g) ≫ (inv f ⊗ₘ h) = (𝟙 V ⊗ₘ g) ≫ (𝟙 V ⊗ₘ h) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.inv_hom_id_tensor'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : 
Y ⟶ Z) : (inv f otimesₘ g) ≫ (f otimesₘ h) = (𝟙 W otimesₘ g) ≫ (𝟙 W otimesₘ h)
参数：f : V ⟶ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ₘ g) ≫ (f ⊗ₘ h) = (𝟙 W ⊗ₘ g) ≫ (𝟙 W ⊗ₘ h) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_hom_inv_id'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : 
Y ⟶ Z) : (g otimesₘ f) ≫ (h otimesₘ inv f) = (g otimesₘ 𝟙 V) ≫ (h otimesₘ 𝟙 V)
参数：f : V ⟶ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ f) ≫ (h ⊗ₘ inv f) = (g ⊗ₘ 𝟙 V) ≫ (h ⊗ₘ 𝟙 V) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_inv_hom_id'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : 
Y ⟶ Z) : (g otimesₘ inv f) ≫ (h otimesₘ f) = (g otimesₘ 𝟙 W) ≫ (h otimesₘ 𝟙 W)
参数：f : V ⟶ W；g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ₘ inv f) ≫ (h ⊗ₘ f) = (g ⊗ₘ 𝟙 W) ≫ (h ⊗ₘ 𝟙 W) := by simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.comp_tensor_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 
Z) ≫ (g otimesₘ 𝟙 Z)
参数：f : W ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ₘ 𝟙 Z = (f ⊗ₘ 𝟙 Z) ≫ (g ⊗ₘ 𝟙 Z) := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.id_tensor_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ 
f) ≫ (𝟙 Z otimesₘ g)
参数：f : W ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ₘ f ≫ g = (𝟙 Z ⊗ₘ f) ≫ (𝟙 Z ⊗ₘ g) := by
  simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.id_tensor_comp_tensor_id** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y otimesₘ f) ≫ (g ot
imesₘ 𝟙 X) = g otimesₘ f
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ₘ f) ≫ (g ⊗ₘ 𝟙 X) = g ⊗ₘ f := by
  simp [tensorHom_def']

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_id_comp_id_tensor** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g otimesₘ 𝟙 W) ≫ (𝟙 Z 
otimesₘ f) = g otimesₘ f
参数：f : W ⟶ X；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ₘ 𝟙 W) ≫ (𝟙 Z ⊗ₘ f) = g ⊗ₘ f := by
  simp [tensorHom_def]
/-
**CategoryTheory.MonoidalCategory.tensor_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) otimesₘ f = 𝟙 (𝟙_ C) ot
imesₘ g ↔ f = g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ₘ f = 𝟙 (𝟙_ C) ⊗ₘ g ↔ f = g := by simp
/-
**CategoryTheory.MonoidalCategory.tensor_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f otimesₘ 𝟙 (𝟙_ C) = g otimesₘ 
𝟙 (𝟙_ C) ↔ f = g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ₘ 𝟙 (𝟙_ C) = g ⊗ₘ 𝟙 (𝟙_ C) ↔ f = g := by simp

section

variable (C)

attribute [local simp] whisker_exchange

/-- The tensor product expressed as a functor. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product expressed as a functor.
-/
def tensor : C × C ⥤ C where
  obj X := X.1 ⊗ X.2
  map {X Y : C × C} (f : X ⟶ Y) := f.1 ⊗ₘ f.2

/-- The left-associated triple tensor product as a functor. -/
/-
**CategoryTheory.MonoidalCategory.leftAssocTensor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：leftAssocTensor : C × C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left-associated triple tensor product as a functor.
-/
def leftAssocTensor : C × C × C ⥤ C where
  obj X := (X.1 ⊗ X.2.1) ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := (f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2

@[simp]
/-
**CategoryTheory.MonoidalCategory.leftAssocTensor_obj** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 otimes X.2.1) o
times X.2.2
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftAssocTensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl

@[simp]
/-
**CategoryTheory.MonoidalCategory.leftAssocTensor_map** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：leftAssocTensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 o
timesₘ f.2.1) otimesₘ f.2.2
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftAssocTensor_map {X Y} (f : X ⟶ Y) :
    (leftAssocTensor C).map f = (f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2 :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
/-
**CategoryTheory.MonoidalCategory.rightAssocTensor** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：rightAssocTensor : C × C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right-associated triple tensor product as a functor.
-/
def rightAssocTensor : C × C × C ⥤ C where
  obj X := X.1 ⊗ X.2.1 ⊗ X.2.2
  map {X Y : C × C × C} (f : X ⟶ Y) := f.1 ⊗ₘ f.2.1 ⊗ₘ f.2.2

@[simp]
/-
**CategoryTheory.MonoidalCategory.rightAssocTensor_obj** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 otimes X.2.1 o
times X.2.2
参数：X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightAssocTensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl

@[simp]
/-
**CategoryTheory.MonoidalCategory.rightAssocTensor_map** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：rightAssocTensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 
otimesₘ f.2.1 otimesₘ f.2.2
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightAssocTensor_map {X Y} (f : X ⟶ Y) :
    (rightAssocTensor C).map f = f.1 ⊗ₘ f.2.1 ⊗ₘ f.2.2 :=
  rfl

/-- The tensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.MonoidalCategory.curriedTensor** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.MonoidalCategory`。
形式化陈述：curriedTensor : C ⥤ C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product bifunctor `C ⥤ C ⥤ C` of a monoidal category.
-/
def curriedTensor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⊗ Y
      map := fun g => X ◁ g }
  map f :=
    { app := fun Y => f ▷ Y }

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
/-
**CategoryTheory.MonoidalCategory.tensorLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：tensorLeft (X : C) : C ⥤ C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the left with a fixed object, as a functor.
-/
abbrev tensorLeft (X : C) : C ⥤ C := (curriedTensor C).obj X

/-- Tensoring on the right with a fixed object, as a functor. -/
/-
**CategoryTheory.MonoidalCategory.tensorRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.MonoidalCategory`。
形式化陈述：tensorRight (X : C) : C ⥤ C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the right with a fixed object, as a functor.
-/
abbrev tensorRight (X : C) : C ⥤ C := (curriedTensor C).flip.obj X

variable (C)

/-- The functor `fun X ↦ 𝟙_ C ⊗ X`. -/
/-
**CategoryTheory.MonoidalCategory.tensorUnitLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：tensorUnitLeft : C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `fun X ↦ 𝟙_ C ⊗ X`.
-/
abbrev tensorUnitLeft : C ⥤ C := tensorLeft (𝟙_ C)

/-- The functor `fun X ↦ X ⊗ 𝟙_ C`. -/
/-
**CategoryTheory.MonoidalCategory.tensorUnitRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：tensorUnitRight : C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `fun X ↦ X ⊗ 𝟙_ C`.
-/
abbrev tensorUnitRight : C ⥤ C := tensorRight (𝟙_ C)

-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
/-- The associator as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.associatorNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator as a natural isomorphism.
-/
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents (fun _ => MonoidalCategory.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
/-- The left unitor as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.leftUnitorNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor as a natural isomorphism.
-/
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.leftUnitor

set_option backward.defeqAttrib.useBackward true in
/-- The right unitor as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.rightUnitorNatIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor as a natural isomorphism.
-/
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents MonoidalCategory.rightUnitor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.curriedAssociatorNatIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：curriedAssociatorNatIso : bifunctorComp₁₂ (curriedTensor C) (curriedTensor
 C) ≅ bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator as a natural isomorphism between trifunctors `C ⥤ C ⥤ C ⥤ C`.
-/
def curriedAssociatorNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedTensor C) ≅
      bifunctorComp₂₃ (curriedTensor C) (curriedTensor C) :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => NatIso.ofComponents
    (fun X₃ => α_ X₁ X₂ X₃)))

section

variable {C}

set_option backward.defeqAttrib.useBackward true in
/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
/-
**CategoryTheory.MonoidalCategory.tensorLeftTensor** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：tensorLeftTensor (X Y : C) : tensorLeft (X otimes Y) ≅ tensorLeft Y ⋙ tens
orLeft X
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun {Z} {Z'} f => by simp

@[simp]
/-
**CategoryTheory.MonoidalCategory.tensorLeftTensor_hom_app** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensorLeftTensor_hom_app (X Y Z : C) : (tensorLeftTensor X Y).hom.app Z = 
(associator X Y Z).hom
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorLeftTensor_hom_app (X Y Z : C) :
    (tensorLeftTensor X Y).hom.app Z = (associator X Y Z).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.MonoidalCategory.tensorLeftTensor_inv_app** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensorLeftTensor_inv_app (X Y Z : C) : (tensorLeftTensor X Y).inv.app Z = 
(associator X Y Z).inv
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorLeftTensor_inv_app (X Y Z : C) :
    (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by simp [tensorLeftTensor]

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
/-
**CategoryTheory.MonoidalCategory.tensoringLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：tensoringLeft : C ⥤ C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is an op-monoidal functor.
-/
abbrev tensoringLeft : C ⥤ C ⥤ C := curriedTensor C
/-
**CategoryTheory.MonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (tensoringLeft C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
/-
**CategoryTheory.MonoidalCategory.tensoringRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：tensoringRight : C ⥤ C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
abbrev tensoringRight : C ⥤ C ⥤ C := (curriedTensor C).flip

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (tensoringRight C).Faithful where
  map_injective {X} {Y} f g h := by
    injections h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

variable {C}

set_option backward.defeqAttrib.useBackward true in
/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
/-
**CategoryTheory.MonoidalCategory.tensorRightTensor** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：tensorRightTensor (X Y : C) : tensorRight (X otimes Y) ≅ tensorRight X ⋙ t
ensorRight Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun {Z} {Z'} f => by simp

@[simp]
/-
**CategoryTheory.MonoidalCategory.tensorRightTensor_hom_app** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensorRightTensor_hom_app (X Y Z : C) : (tensorRightTensor X Y).hom.app Z 
= (associator Z X Y).inv
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorRightTensor_hom_app (X Y Z : C) :
    (tensorRightTensor X Y).hom.app Z = (associator Z X Y).inv :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.MonoidalCategory.tensorRightTensor_inv_app** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensorRightTensor_inv_app (X Y Z : C) : (tensorRightTensor X Y).inv.app Z 
= (associator Z X Y).hom
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**CategoryTheory.MonoidalCategory.prodMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.MonoidalCategory`。
形式化陈述：prodMonoidal : MonoidalCategory (C₁ × C₂) where tensorObj X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance prodMonoidal : MonoidalCategory (C₁ × C₂) where
  tensorObj X Y := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom f g := (f.1 ⊗ₘ g.1) ×ₘ f.2 ⊗ₘ g.2
  whiskerLeft X _ _ f := whiskerLeft X.1 f.1 ×ₘ whiskerLeft X.2 f.2
  whiskerRight f X := whiskerRight f.1 X.1 ×ₘ whiskerRight f.2 X.2
  tensorHom_def := by simp [tensorHom_def]
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator X Y Z := (α_ X.1 Y.1 Z.1).prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).prod (ρ_ X₂)

end

end MonoidalCategory

namespace NatTrans

variable {J : Type*} [Category* J] {C : Type*} [Category* C] [MonoidalCategory C]
  {F G F' G' : J ⥤ C} (α : F ⟶ F') (β : G ⟶ G')

@[reassoc]
/-
**CategoryTheory.NatTrans.tensor_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.NatTrans`。
形式化陈述：tensor_naturality {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y') : (F.map f oti
mesₘ G.map g) ≫ (α.app Y otimesₘ β.app Y') = (α.app X otimesₘ β.app X') ≫ (F'.ma
p f otimesₘ G'.map g)
参数：f : X ⟶ Y；g : X' ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_naturality {X Y X' Y' : J} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⊗ₘ G.map g) ≫ (α.app Y ⊗ₘ β.app Y') =
      (α.app X ⊗ₘ β.app X') ≫ (F'.map f ⊗ₘ G'.map g) := by simp

@[reassoc]
/-
**CategoryTheory.NatTrans.whiskerRight_app_tensor_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.NatTrans`。
形式化陈述：whiskerRight_app_tensor_app {X Y : J} (f : X ⟶ Y) (X' : J) : F.map f ▷ G.o
bj X' ≫ (α.app Y otimesₘ β.app X') = (α.app X otimesₘ β.app X') ≫ F'.map f ▷ (G'
.obj X')
参数：f : X ⟶ Y；X' : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用引理 `CategoryTheory.NatTrans.tensor_naturality`：tensor_naturality {X Y X' Y' 
: J} (f : X ⟶ Y) (g : X' ⟶ Y') : (F.map f otimesₘ G.map g) ≫ (α.app Y otimesₘ β.
app Y') = (α.app X otimesₘ β.ap…
-/
lemma whiskerRight_app_tensor_app {X Y : J} (f : X ⟶ Y) (X' : J) :
    F.map f ▷ G.obj X' ≫ (α.app Y ⊗ₘ β.app X') =
      (α.app X ⊗ₘ β.app X') ≫ F'.map f ▷ (G'.obj X') := by
  simpa using tensor_naturality α β f (𝟙 X')

@[reassoc]
/-
**CategoryTheory.NatTrans.whiskerLeft_app_tensor_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.NatTrans`。
形式化陈述：whiskerLeft_app_tensor_app {X' Y' : J} (f : X' ⟶ Y') (X : J) : F.obj X ◁ G
.map f ≫ (α.app X otimesₘ β.app Y') = (α.app X otimesₘ β.app X') ≫ F'.obj X ◁ G'
.map f
参数：f : X' ⟶ Y'；X : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.NatTrans.tensor_naturality`：tensor_naturality {X Y X' Y' 
: J} (f : X ⟶ Y) (g : X' ⟶ Y') : (F.map f otimesₘ G.map g) ≫ (α.app Y otimesₘ β.
app Y') = (α.app X otimesₘ β.ap…
-/
lemma whiskerLeft_app_tensor_app {X' Y' : J} (f : X' ⟶ Y') (X : J) :
    F.obj X ◁ G.map f ≫ (α.app X ⊗ₘ β.app Y') =
      (α.app X ⊗ₘ β.app X') ≫ F'.obj X ◁ G'.map f := by
  simpa using tensor_naturality α β (𝟙 X) f

end NatTrans

section ObjectProperty

open ObjectProperty

set_option backward.isDefEq.respectTransparency.types false in
/-- The restriction of a monoidal category along an object property
that's closed under the monoidal structure. -/
-- See note [reducible non-instances]
/-
**CategoryTheory.MonoidalCategory.fullSubcategory** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       (P : CategoryTheory.ObjectProperty C
) →         P (CategoryTheory.MonoidalCategoryStruct.tensorUnit C) →           (
∀ (X Y : C), P X → P Y → P (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y)
) →             CategoryTheory.MonoidalCategory P.FullSubcategory
参数：P : CategoryTheory.ObjectProperty C；CategoryTheory.MonoidalCategoryStruct.ten
sorUnit C；∀ (X Y : C), P X → P Y → P (CategoryTheory.MonoidalCategoryStruct.tens
orObj X Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev MonoidalCategory.fullSubcategory
    {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : ObjectProperty C)
    (tensorUnit : P (𝟙_ C))
    (tensorObj : ∀ X Y, P X → P Y → P (X ⊗ Y)) :
    MonoidalCategory P.FullSubcategory where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, tensorObj X.1 Y.1 X.2 Y.2⟩
  whiskerLeft X _ _ f := homMk (X.obj ◁ f.hom)
  whiskerRight f X := homMk (f.hom ▷ X.obj)
  tensorHom f g := homMk (f.hom ⊗ₘ g.hom)
  tensorUnit := ⟨𝟙_ C, tensorUnit⟩
  associator X Y Z := P.fullyFaithfulι.preimageIso (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.fullyFaithfulι.preimageIso (λ_ X.1)
  rightUnitor X := P.fullyFaithfulι.preimageIso (ρ_ X.1)
  tensorHom_def _ _ := by ext; apply tensorHom_def

end ObjectProperty

end CategoryTheory

