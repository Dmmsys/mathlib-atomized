/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Bicategories

In this file we define typeclass for bicategories.

A bicategory `B` consists of
* objects `a : B`,
* 1-morphisms `f : a ⟶ b` between objects `a b : B`, and
* 2-morphisms `η : f ⟶ g` between 1-morphisms `f g : a ⟶ b` between objects `a b : B`.

We use `u`, `v`, and `w` as the universe variables for objects, 1-morphisms, and 2-morphisms,
respectively.

A typeclass for bicategories extends `CategoryTheory.CategoryStruct` typeclass. This means that
we have
* a composition `f ≫ g : a ⟶ c` for each 1-morphisms `f : a ⟶ b` and `g : b ⟶ c`, and
* an identity `𝟙 a : a ⟶ a` for each object `a : B`.

For each object `a b : B`, the collection of 1-morphisms `a ⟶ b` has a category structure. The
2-morphisms in the bicategory are implemented as the morphisms in this family of categories.

The composition of 1-morphisms is in fact an object part of a functor
`(a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c)`. The definition of bicategories in this file does not
require this functor directly. Instead, it requires the whiskering functions. For a 1-morphism
`f : a ⟶ b` and a 2-morphism `η : g ⟶ h` between 1-morphisms `g h : b ⟶ c`, there is a
2-morphism `whiskerLeft f η : f ≫ g ⟶ f ≫ h`. Similarly, for a 2-morphism `η : f ⟶ g`
between 1-morphisms `f g : a ⟶ b` and a 1-morphism `f : b ⟶ c`, there is a 2-morphism
`whiskerRight η h : f ≫ h ⟶ g ≫ h`. These satisfy the exchange law
`whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ`,
which is required as an axiom in the definition here.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

open Category Iso

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/--
Definition of `Bicategory` / `Bicategory` 的定义

English:
class Bicategory
  parameters: (B : Type u)
  extends: CategoryStruct.{v} B
  axioms and operations (18):
    - homCategory : forall a b : B, Category.{w} (a ⟶ b)  [default: by infer_instance]
    - whiskerLeft({a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h)) : f ≫ g ⟶ f ≫ h
    - whiskerRight({a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c)) : f ≫ h ⟶ g ≫ h
    - associator({a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)) : (f ≫ g) ≫ h ≅ f ≫ g ≫ h
    - leftUnitor({a b : B} (f : a ⟶ b)) : 𝟙 a ≫ f ≅ f
    - rightUnitor({a b : B} (f : a ⟶ b)) : f ≫ 𝟙 b ≅ f
    - whiskerLeft_id : forall {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g)  [default: by cat_disch]
    - whiskerLeft_comp : forall {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i), whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ  [default: by cat_disch]
    - id_whiskerLeft : forall {a b} {f g : a ⟶ b} (η : f ⟶ g), whiskerLeft (𝟙 a) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv  [default: by cat_disch]
    - comp_whiskerLeft : forall {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'), whiskerLeft (f ≫ g) η = (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv  [default: by cat_disch]
    - id_whiskerRight : forall {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerRight (𝟙 f) g = 𝟙 (f ≫ g)  [default: by cat_disch]
    - comp_whiskerRight : forall {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c), whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i  [default: by cat_disch]
    - whiskerRight_id : forall {a b} {f g : a ⟶ b} (η : f ⟶ g), whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv  [default: by cat_disch]
    - whiskerRight_comp : forall {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d), whiskerRight η (g ≫ h) = (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom  [default: by cat_disch]
    - whisker_assoc : forall {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d), whiskerRight (whiskerLeft f η) h = (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv  [default: by cat_disch]
    - whisker_exchange : forall {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i), whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ  [default: by cat_disch]
    - pentagon : forall {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e), whiskerRight (associator f g h).hom i ≫ (associator f (g ≫ h) i).hom ≫ whiskerLeft f (associator g h i).hom = (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom  [default: by cat_disch]
    - triangle : forall {a b c} (f : a ⟶ b) (g : b ⟶ c), (associator f (𝟙 b) g).hom ≫ whiskerLeft f (leftUnitor g).hom = whiskerRight (rightUnitor f).hom g  [default: by cat_disch]

中文:
类 双范畴
  参数: (B : 类型u)
  继承: CategoryStruct.{v} B
  公理与运算 (18 个):
    - homCategory : 对任意 a b : B, 范畴.{w} (a ⟶ b)  [默认: by infer_instance]
    - whiskerLeft({a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h)) : f ≫ g ⟶ f ≫ h
    - whiskerRight({a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c)) : f ≫ h ⟶ g ≫ h
    - associator({a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)) : (f ≫ g) ≫ h ≅ f ≫ g ≫ h
    - leftUnitor({a b : B} (f : a ⟶ b)) : 𝟙 a ≫ f ≅ f
    - rightUnitor({a b : B} (f : a ⟶ b)) : f ≫ 𝟙 b ≅ f
    - whiskerLeft_id : 对任意 {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g)  [默认: by cat_disch]
    - whiskerLeft_comp : 对任意 {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i), whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ  [默认: by cat_disch]
    - id_whiskerLeft : 对任意 {a b} {f g : a ⟶ b} (η : f ⟶ g), whiskerLeft (𝟙 a) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv  [默认: by cat_disch]
    - comp_whiskerLeft : 对任意 {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'), whiskerLeft (f ≫ g) η = (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv  [默认: by cat_disch]
    - id_whiskerRight : 对任意 {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerRight (𝟙 f) g = 𝟙 (f ≫ g)  [默认: by cat_disch]
    - comp_whiskerRight : 对任意 {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c), whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i  [默认: by cat_disch]
    - whiskerRight_id : 对任意 {a b} {f g : a ⟶ b} (η : f ⟶ g), whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv  [默认: by cat_disch]
    - whiskerRight_comp : 对任意 {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d), whiskerRight η (g ≫ h) = (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom  [默认: by cat_disch]
    - whisker_assoc : 对任意 {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d), whiskerRight (whiskerLeft f η) h = (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv  [默认: by cat_disch]
    - whisker_exchange : 对任意 {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i), whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ  [默认: by cat_disch]
    - pentagon : 对任意 {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e), whiskerRight (associator f g h).hom i ≫ (associator f (g ≫ h) i).hom ≫ whiskerLeft f (associator g h i).hom = (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom  [默认: by cat_disch]
    - triangle : 对任意 {a b c} (f : a ⟶ b) (g : b ⟶ c), (associator f (𝟙 b) g).hom ≫ whiskerLeft f (leftUnitor g).hom = whiskerRight (rightUnitor f).hom g  [默认: by cat_disch]

Depends on / 依赖: infer_instance
-/
class Bicategory (B : Type u) extends CategoryStruct.{v} B where
  /-- The category structure on the collection of 1-morphisms -/
  homCategory : forall a b : B, Category.{w} (a ⟶ b) := by infer_instance
  /-- Left whiskering for morphisms -/
  whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h
  /-- Right whiskering for morphisms -/
  whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h
  /-- The associator isomorphism: `(f ≫ g) ≫ h ≅ f ≫ g ≫ h` -/
  associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h ≅ f ≫ g ≫ h
  /-- The left unitor: `𝟙 a ≫ f ≅ f` -/
  leftUnitor {a b : B} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f
  /-- The right unitor: `f ≫ 𝟙 b ≅ f` -/
  rightUnitor {a b : B} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f
  -- axioms for left whiskering:
  whiskerLeft_id : forall {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := by
    cat_disch
  whiskerLeft_comp :
    forall {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
      whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := by
    cat_disch
  id_whiskerLeft :
    forall {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerLeft (𝟙 a) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := by
    cat_disch
  comp_whiskerLeft :
    forall {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
      whiskerLeft (f ≫ g) η =
        (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv := by
    cat_disch
  -- axioms for right whiskering:
  id_whiskerRight : forall {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := by
    cat_disch
  comp_whiskerRight :
    forall {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
      whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := by
    cat_disch
  whiskerRight_id :
    forall {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := by
    cat_disch
  whiskerRight_comp :
    forall {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
      whiskerRight η (g ≫ h) =
        (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom := by
    cat_disch
  -- associativity of whiskerings:
  whisker_assoc :
    forall {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
      whiskerRight (whiskerLeft f η) h =
        (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv := by
    cat_disch
  -- exchange law of left and right whiskerings:
  whisker_exchange :
    forall {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
      whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := by
    cat_disch
  -- pentagon identity:
  pentagon :
    forall {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
      whiskerRight (associator f g h).hom i ≫
          (associator f (g ≫ h) i).hom ≫ whiskerLeft f (associator g h i).hom =
        (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom := by
    cat_disch
  -- triangle identity:
  triangle :
    forall {a b c} (f : a ⟶ b) (g : b ⟶ c),
      (associator f (𝟙 b) g).hom ≫ whiskerLeft f (leftUnitor g).hom
      = whiskerRight (rightUnitor f).hom g := by
    cat_disch

namespace Bicategory

@[inherit_doc] scoped infixr:81 " ◁ " => Bicategory.whiskerLeft
@[inherit_doc] scoped infixl:81 " ▷ " => Bicategory.whiskerRight
@[inherit_doc] scoped notation "α_" => Bicategory.associator
@[inherit_doc] scoped notation "fun_" => Bicategory.leftUnitor
@[inherit_doc] scoped notation "ρ_" => Bicategory.rightUnitor

/-!
### Simp-normal form for 2-morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any 2-morphisms into simp-normal
form defined below. Rewriting into simp-normal form is also useful when applying (forthcoming)
`coherence` tactic.

The simp-normal form of 2-morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of 2-morphisms like `η₁ ≫ η₂ ≫ η₃ ≫ η₄ ≫ η₅` such that each `ηᵢ` is
  either a structural 2-morphisms (2-morphisms made up only of identities, associators, unitors)
  or non-structural 2-morphisms, and
2. each non-structural 2-morphism in the composition is of the form `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅`,
  where each `fᵢ` is a 1-morphism that is not the identity or a composite and `η` is a
  non-structural 2-morphisms that is also not the identity or a composite.

Note that `f₁ ◁ f₂ ◁ f₃ ◁ η ▷ f₄ ▷ f₅` is actually `f₁ ◁ (f₂ ◁ (f₃ ◁ ((η ▷ f₄) ▷ f₅)))`.
-/

attribute [instance_reducible, instance] homCategory

attribute [reassoc]
  whiskerLeft_comp id_whiskerLeft comp_whiskerLeft comp_whiskerRight whiskerRight_id
  whiskerRight_comp whisker_assoc whisker_exchange

attribute [reassoc (attr := simp)] pentagon triangle
/-
The following simp attributes are put in order to rewrite any 2-morphisms into normal forms. There
are associators and unitors in the RHS in the several simp lemmas here (e.g. `id_whiskerLeft`),
which at first glance look more complicated than the LHS, but they will be eventually reduced by
the pentagon or the triangle identities, and more generally, (forthcoming) `coherence` tactic.
-/
attribute [simp]
  whiskerLeft_id whiskerLeft_comp id_whiskerLeft comp_whiskerLeft id_whiskerRight comp_whiskerRight
  whiskerRight_id whiskerRight_comp whisker_assoc


variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_hom_inv` / 定理 `whiskerLeft_hom_inv`

English:
theorem whiskerLeft_hom_inv
  given: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h)
  proof: by rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_hom_inv
  条件: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h)
  证明: by rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g) := by rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_whiskerRight` / 定理 `hom_inv_whiskerRight`

English:
theorem hom_inv_whiskerRight
  given: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c)
  proof: by rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_whiskerRight
  条件: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c)
  证明: by rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight, hom_inv_id, id_whiskerRight
-/
theorem hom_inv_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
    η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h) := by rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_inv_hom` / 定理 `whiskerLeft_inv_hom`

English:
theorem whiskerLeft_inv_hom
  given: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h)
  proof: by rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_inv_hom
  条件: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h)
  证明: by rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: inv_hom_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem whiskerLeft_inv_hom (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h) := by rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_whiskerRight` / 定理 `inv_hom_whiskerRight`

English:
theorem inv_hom_whiskerRight
  given: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c)
  proof: by rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 inv_hom_whiskerRight
  条件: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c)
  证明: by rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight, id_whiskerRight, inv_hom_id
-/
theorem inv_hom_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
    η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h) := by rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_whiskerLeft_hom_inv` / 定理 `whiskerLeft_whiskerLeft_hom_inv`

English:
theorem whiskerLeft_whiskerLeft_hom_inv
  given: (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k)
  proof: by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_whiskerLeft_hom_inv
  条件: (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k)
  证明: by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: whiskerLeft_comp
-/
theorem whiskerLeft_whiskerLeft_hom_inv (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k) :
    f ◁ g ◁ η.hom ≫ f ◁ g ◁ η.inv = 𝟙 (f ≫ g ≫ h) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_whiskerRight_whiskerRight` / 定理 `hom_inv_whiskerRight_whiskerRight`

English:
theorem hom_inv_whiskerRight_whiskerRight
  given: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d)
  proof: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_whiskerRight_whiskerRight
  条件: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d)
  证明: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight
-/
theorem hom_inv_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d) :
    η.hom ▷ h ▷ k ≫ η.inv ▷ h ▷ k = 𝟙 ((f ≫ h) ≫ k) := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_whiskerLeft_inv_hom` / 定理 `whiskerLeft_whiskerLeft_inv_hom`

English:
theorem whiskerLeft_whiskerLeft_inv_hom
  given: (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k)
  proof: by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_whiskerLeft_inv_hom
  条件: (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k)
  证明: by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: whiskerLeft_comp
-/
theorem whiskerLeft_whiskerLeft_inv_hom (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k) :
    f ◁ g ◁ η.inv ≫ f ◁ g ◁ η.hom = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_whiskerRight_whiskerRight` / 定理 `inv_hom_whiskerRight_whiskerRight`

English:
theorem inv_hom_whiskerRight_whiskerRight
  given: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d)
  proof: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

中文:
定理 inv_hom_whiskerRight_whiskerRight
  条件: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d)
  证明: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight
-/
theorem inv_hom_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d) :
    η.inv ▷ h ▷ k ≫ η.hom ▷ h ▷ k = 𝟙 ((g ≫ h) ≫ k) := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_hom_inv_whiskerRight` / 定理 `whiskerLeft_hom_inv_whiskerRight`

English:
theorem whiskerLeft_hom_inv_whiskerRight
  given: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d)
  proof: by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_hom_inv_whiskerRight
  条件: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d)
  证明: by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: whiskerLeft_comp
-/
theorem whiskerLeft_hom_inv_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.hom ▷ k ≫ f ◁ η.inv ▷ k = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_inv_hom_whiskerRight` / 定理 `whiskerLeft_inv_hom_whiskerRight`

English:
theorem whiskerLeft_inv_hom_whiskerRight
  given: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d)
  proof: by
  simp [← whiskerLeft_comp]

中文:
定理 whiskerLeft_inv_hom_whiskerRight
  条件: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d)
  证明: by
  simp [← whiskerLeft_comp]

Depends on / 依赖: whiskerLeft_comp
-/
theorem whiskerLeft_inv_hom_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.inv ▷ k ≫ f ◁ η.hom ▷ k = 𝟙 (f ≫ h ≫ k) := by
  simp [← whiskerLeft_comp]

/-- The left whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps]
/--
Definition of `whiskerLeftIso` / `whiskerLeftIso` 的定义

English:
definition whiskerLeftIso
  signature: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h)
  body: f ◁ η.hom
  inv := f ◁ η.inv

中文:
定义 whiskerLeftIso
  签名: (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h)
  定义体: f ◁ η.hom
  inv := f ◁ η.inv
-/
def whiskerLeftIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ≫ g ≅ f ≫ h where
  hom := f ◁ η.hom
  inv := f ◁ η.inv

/--
Instance `whiskerLeft_isIso` / 实例 `whiskerLeft_isIso`

English:
instance whiskerLeft_isIso
  signature: (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η]
  body: (whiskerLeftIso f (asIso η)).isIso_hom

@[simp, push]

中文:
实例 whiskerLeft_isIso
  签名: (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [是同构 η]
  定义体: (whiskerLeftIso f (asIso η)).isIso_hom

@[simp, push]

Depends on / 依赖: isIso_hom, whiskerLeftIso
-/
instance whiskerLeft_isIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : IsIso (f ◁ η) :=
  (whiskerLeftIso f (asIso η)).isIso_hom

@[simp, push]
/--
theorem `inv_whiskerLeft` / 定理 `inv_whiskerLeft`

English:
theorem inv_whiskerLeft
  given: (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η]
  proof: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← whiskerLeft_comp, whiskerLeft_id, IsIso.hom_inv_id]

中文:
定理 inv_whiskerLeft
  条件: (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [是同构 η]
  证明: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← whiskerLeft_comp, whiskerLeft_id, IsIso.hom_inv_id]

Depends on / 依赖: IsIso.hom_inv_id, IsIso.inv_eq_of_hom_inv_id, hom_inv_id, inv_eq_of_hom_inv_id, whiskerLeft_comp, whiskerLeft_id
-/
theorem inv_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] :
    inv (f ◁ η) = f ◁ inv η := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← whiskerLeft_comp, whiskerLeft_id, IsIso.hom_inv_id]

/-- The right whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps!]
/--
Definition of `whiskerRightIso` / `whiskerRightIso` 的定义

English:
definition whiskerRightIso
  signature: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c)
  body: η.hom ▷ h
  inv := η.inv ▷ h

中文:
定义 whiskerRightIso
  签名: {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c)
  定义体: η.hom ▷ h
  inv := η.inv ▷ h
-/
def whiskerRightIso {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h where
  hom := η.hom ▷ h
  inv := η.inv ▷ h

/--
Instance `whiskerRight_isIso` / 实例 `whiskerRight_isIso`

English:
instance whiskerRight_isIso
  signature: {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η]
  body: (whiskerRightIso (asIso η) h).isIso_hom

@[simp, push]

中文:
实例 whiskerRight_isIso
  签名: {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [是同构 η]
  定义体: (whiskerRightIso (asIso η) h).isIso_hom

@[simp, push]

Depends on / 依赖: isIso_hom, whiskerRightIso
-/
instance whiskerRight_isIso {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : IsIso (η ▷ h) :=
  (whiskerRightIso (asIso η) h).isIso_hom

@[simp, push]
/--
theorem `inv_whiskerRight` / 定理 `inv_whiskerRight`

English:
theorem inv_whiskerRight
  given: {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η]
  proof: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← comp_whiskerRight, id_whiskerRight, IsIso.hom_inv_id]

@[inherit_doc whiskerLeftIso]
scoped infixr:82 " ◁ᵢ " => whiskerLeftIso

@[inherit_doc whiskerRightIso]
scoped infixl:82 " ▷ᵢ " => whiskerRightIso

@[reassoc (attr := simp)]

中文:
定理 inv_whiskerRight
  条件: {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [是同构 η]
  证明: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← comp_whiskerRight, id_whiskerRight, IsIso.hom_inv_id]

@[inherit_doc whiskerLeftIso]
scoped infixr:82 " ◁ᵢ " => whiskerLeftIso

@[inherit_doc whiskerRightIso]
scoped infixl:82 " ▷ᵢ " => whiskerRightIso

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, IsIso.inv_eq_of_hom_inv_id, comp_whiskerRight, hom_inv_id, id_whiskerRight, inv_eq_of_hom_inv_id
-/
theorem inv_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] :
    inv (η ▷ h) = inv η ▷ h := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← comp_whiskerRight, id_whiskerRight, IsIso.hom_inv_id]

@[inherit_doc whiskerLeftIso]
scoped infixr:82 " ◁ᵢ " => whiskerLeftIso

@[inherit_doc whiskerRightIso]
scoped infixl:82 " ▷ᵢ " => whiskerRightIso

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv` / 定理 `pentagon_inv`

English:
theorem pentagon_inv
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i =
      (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_inv_hom_hom_inv` / 定理 `pentagon_inv_inv_hom_hom_inv`

English:
theorem pentagon_inv_inv_hom_hom_inv
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: by
  rw [← cancel_epi (f ◁ (α_ g h i).inv)]; rw [← cancel_mono (α_ (f ≫ g) h i).inv]
  simp

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_inv_hom_hom_inv
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: by
  rw [← cancel_epi (f ◁ (α_ g h i).inv)]; rw [← cancel_mono (α_ (f ≫ g) h i).inv]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, cancel_mono
-/
theorem pentagon_inv_inv_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom =
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv := by
  rw [← cancel_epi (f ◁ (α_ g h i).inv)]; rw [← cancel_mono (α_ (f ≫ g) h i).inv]
  simp

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_hom_hom_hom_inv` / 定理 `pentagon_inv_hom_hom_hom_inv`

English:
theorem pentagon_inv_hom_hom_hom_inv
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_hom_hom_hom_inv
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_inv_hom_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom =
      (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_inv_inv_inv_inv` / 定理 `pentagon_hom_inv_inv_inv_inv`

English:
theorem pentagon_hom_inv_inv_inv_inv
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: by
  simp [← cancel_epi (f ◁ (α_ g h i).inv)]

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_inv_inv_inv_inv
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: by
  simp [← cancel_epi (f ◁ (α_ g h i).inv)]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi
-/
theorem pentagon_hom_inv_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
      (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  simp [← cancel_epi (f ◁ (α_ g h i).inv)]

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_hom_inv_hom_hom` / 定理 `pentagon_hom_hom_inv_hom_hom`

English:
theorem pentagon_hom_hom_inv_hom_hom
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_hom_inv_hom_hom
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_hom_hom_inv_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv =
      (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_inv_inv_inv_hom` / 定理 `pentagon_hom_inv_inv_inv_hom`

English:
theorem pentagon_hom_inv_inv_inv_hom
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: by
  rw [← cancel_epi (α_ f g (h ≫ i)).inv]; rw [← cancel_mono ((α_ f g h).inv ▷ i)]
  simp

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_inv_inv_inv_hom
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: by
  rw [← cancel_epi (α_ f g (h ≫ i)).inv]; rw [← cancel_mono ((α_ f g h).inv ▷ i)]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, cancel_mono
-/
theorem pentagon_hom_inv_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv =
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i := by
  rw [← cancel_epi (α_ f g (h ≫ i)).inv]; rw [← cancel_mono ((α_ f g h).inv ▷ i)]
  simp

@[reassoc (attr := simp)]
/--
theorem `pentagon_hom_hom_inv_inv_hom` / 定理 `pentagon_hom_hom_inv_inv_hom`

English:
theorem pentagon_hom_hom_inv_inv_hom
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 pentagon_hom_hom_inv_inv_hom
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv =
      (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_hom_hom_hom_hom` / 定理 `pentagon_inv_hom_hom_hom_hom`

English:
theorem pentagon_inv_hom_hom_hom_hom
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: by
  simp [← cancel_epi ((α_ f g h).hom ▷ i)]

@[reassoc (attr := simp)]

中文:
定理 pentagon_inv_hom_hom_hom_hom
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: by
  simp [← cancel_epi ((α_ f g h).hom ▷ i)]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi
-/
theorem pentagon_inv_hom_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
      (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom := by
  simp [← cancel_epi ((α_ f g h).hom ▷ i)]

@[reassoc (attr := simp)]
/--
theorem `pentagon_inv_inv_hom_inv_inv` / 定理 `pentagon_inv_inv_hom_inv_inv`

English:
theorem pentagon_inv_inv_hom_inv_inv
  given: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  proof: eq_of_inv_eq_inv (by simp)

中文:
定理 pentagon_inv_inv_hom_inv_inv
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  证明: eq_of_inv_eq_inv (by simp)

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem pentagon_inv_inv_hom_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i =
      f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv :=
  eq_of_inv_eq_inv (by simp)

/--
theorem `triangle_assoc_comp_left` / 定理 `triangle_assoc_comp_left`

English:
theorem triangle_assoc_comp_left
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: triangle f g

@[reassoc (attr := simp)]

中文:
定理 triangle_assoc_comp_left
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: triangle f g

@[reassoc (attr := simp)]

Depends on / 依赖: triangle
-/
theorem triangle_assoc_comp_left (f : a ⟶ b) (g : b ⟶ c) :
    (α_ f (𝟙 b) g).hom ≫ f ◁ (fun_ g).hom = (ρ_ f).hom ▷ g :=
  triangle f g

@[reassoc (attr := simp)]
/--
theorem `triangle_assoc_comp_right` / 定理 `triangle_assoc_comp_right`

English:
theorem triangle_assoc_comp_right
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by rw [← triangle, inv_hom_id_assoc]

@[reassoc (attr := simp)]

中文:
定理 triangle_assoc_comp_right
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by rw [← triangle, inv_hom_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: inv_hom_id_assoc, triangle
-/
theorem triangle_assoc_comp_right (f : a ⟶ b) (g : b ⟶ c) :
    (α_ f (𝟙 b) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (fun_ g).hom := by rw [← triangle, inv_hom_id_assoc]

@[reassoc (attr := simp)]
/--
theorem `triangle_assoc_comp_right_inv` / 定理 `triangle_assoc_comp_right_inv`

English:
theorem triangle_assoc_comp_right_inv
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  simp [← cancel_mono (f ◁ (fun_ g).hom)]

@[reassoc (attr := simp)]

中文:
定理 triangle_assoc_comp_right_inv
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  simp [← cancel_mono (f ◁ (fun_ g).hom)]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono, fun_
-/
theorem triangle_assoc_comp_right_inv (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ f).inv ▷ g ≫ (α_ f (𝟙 b) g).hom = f ◁ (fun_ g).inv := by
  simp [← cancel_mono (f ◁ (fun_ g).hom)]

@[reassoc (attr := simp)]
/--
theorem `triangle_assoc_comp_left_inv` / 定理 `triangle_assoc_comp_left_inv`

English:
theorem triangle_assoc_comp_left_inv
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  simp [← cancel_mono ((ρ_ f).hom ▷ g)]

@[reassoc]

中文:
定理 triangle_assoc_comp_left_inv
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  simp [← cancel_mono ((ρ_ f).hom ▷ g)]

@[reassoc]

Depends on / 依赖: cancel_mono
-/
theorem triangle_assoc_comp_left_inv (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (fun_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g := by
  simp [← cancel_mono ((ρ_ f).hom ▷ g)]

@[reassoc]
/--
theorem `associator_naturality_left` / 定理 `associator_naturality_left`

English:
theorem associator_naturality_left
  given: {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
  proof: by simp

@[reassoc]

中文:
定理 associator_naturality_left
  条件: {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
  证明: by simp

@[reassoc]
-/
theorem associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h) := by simp

@[reassoc]
/--
theorem `associator_inv_naturality_left` / 定理 `associator_inv_naturality_left`

English:
theorem associator_inv_naturality_left
  given: {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
  proof: by simp

@[reassoc]

中文:
定理 associator_inv_naturality_left
  条件: {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
  证明: by simp

@[reassoc]
-/
theorem associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) ≫ (α_ f' g h).inv = (α_ f g h).inv ≫ η ▷ g ▷ h := by simp

@[reassoc]
/--
theorem `whiskerRight_comp_symm` / 定理 `whiskerRight_comp_symm`

English:
theorem whiskerRight_comp_symm
  given: {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
  proof: by simp

@[reassoc]

中文:
定理 whiskerRight_comp_symm
  条件: {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
  证明: by simp

@[reassoc]
-/
theorem whiskerRight_comp_symm {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h = (α_ f g h).hom ≫ η ▷ (g ≫ h) ≫ (α_ f' g h).inv := by simp

@[reassoc]
/--
theorem `associator_naturality_middle` / 定理 `associator_naturality_middle`

English:
theorem associator_naturality_middle
  given: (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)
  proof: by simp

@[reassoc]

中文:
定理 associator_naturality_middle
  条件: (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)
  证明: by simp

@[reassoc]
-/
theorem associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ h := by simp

@[reassoc]
/--
theorem `associator_inv_naturality_middle` / 定理 `associator_inv_naturality_middle`

English:
theorem associator_inv_naturality_middle
  given: (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)
  proof: by simp

@[reassoc]

中文:
定理 associator_inv_naturality_middle
  条件: (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)
  证明: by simp

@[reassoc]
-/
theorem associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    f ◁ η ▷ h ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ (f ◁ η) ▷ h := by simp

@[reassoc]
/--
theorem `whisker_assoc_symm` / 定理 `whisker_assoc_symm`

English:
theorem whisker_assoc_symm
  given: (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)
  proof: by simp

@[reassoc]

中文:
定理 whisker_assoc_symm
  条件: (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)
  证明: by simp

@[reassoc]
-/
theorem whisker_assoc_symm (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    f ◁ η ▷ h = (α_ f g h).inv ≫ (f ◁ η) ▷ h ≫ (α_ f g' h).hom := by simp

@[reassoc]
/--
theorem `associator_naturality_right` / 定理 `associator_naturality_right`

English:
theorem associator_naturality_right
  given: (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h')
  proof: by simp

@[reassoc]

中文:
定理 associator_naturality_right
  条件: (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h')
  证明: by simp

@[reassoc]
-/
theorem associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ g ◁ η := by simp

@[reassoc]
/--
theorem `associator_inv_naturality_right` / 定理 `associator_inv_naturality_right`

English:
theorem associator_inv_naturality_right
  given: (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h')
  proof: by simp

@[reassoc]

中文:
定理 associator_inv_naturality_right
  条件: (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h')
  证明: by simp

@[reassoc]
-/
theorem associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η ≫ (α_ f g h').inv = (α_ f g h).inv ≫ (f ≫ g) ◁ η := by simp

@[reassoc]
/--
theorem `comp_whiskerLeft_symm` / 定理 `comp_whiskerLeft_symm`

English:
theorem comp_whiskerLeft_symm
  given: (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h')
  proof: by simp

@[reassoc]

中文:
定理 comp_whiskerLeft_symm
  条件: (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h')
  证明: by simp

@[reassoc]
-/
theorem comp_whiskerLeft_symm (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η = (α_ f g h).inv ≫ (f ≫ g) ◁ η ≫ (α_ f g h').hom := by simp

@[reassoc]
/--
theorem `leftUnitor_naturality` / 定理 `leftUnitor_naturality`

English:
theorem leftUnitor_naturality
  given: {f g : a ⟶ b} (η : f ⟶ g)
  proof: by
  simp

@[reassoc]

中文:
定理 leftUnitor_naturality
  条件: {f g : a ⟶ b} (η : f ⟶ g)
  证明: by
  simp

@[reassoc]
-/
theorem leftUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η ≫ (fun_ g).hom = (fun_ f).hom ≫ η := by
  simp

@[reassoc]
/--
theorem `leftUnitor_inv_naturality` / 定理 `leftUnitor_inv_naturality`

English:
theorem leftUnitor_inv_naturality
  given: {f g : a ⟶ b} (η : f ⟶ g)
  proof: by simp

中文:
定理 leftUnitor_inv_naturality
  条件: {f g : a ⟶ b} (η : f ⟶ g)
  证明: by simp
-/
theorem leftUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (fun_ g).inv = (fun_ f).inv ≫ 𝟙 a ◁ η := by simp

/--
theorem `id_whiskerLeft_symm` / 定理 `id_whiskerLeft_symm`

English:
theorem id_whiskerLeft_symm
  given: {f g : a ⟶ b} (η : f ⟶ g)
  statement: η = (fun_ f).inv ≫ 𝟙 a ◁ η ≫ (fun_ g).hom
  proof: by
  simp

@[reassoc]

中文:
定理 id_whiskerLeft_symm
  条件: {f g : a ⟶ b} (η : f ⟶ g)
  结论: η = (fun_ f).inv ≫ 𝟙 a ◁ η ≫ (fun_ g).hom
  证明: by
  simp

@[reassoc]
-/
theorem id_whiskerLeft_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (fun_ f).inv ≫ 𝟙 a ◁ η ≫ (fun_ g).hom := by
  simp

@[reassoc]
/--
theorem `rightUnitor_naturality` / 定理 `rightUnitor_naturality`

English:
theorem rightUnitor_naturality
  given: {f g : a ⟶ b} (η : f ⟶ g)
  proof: by simp

@[reassoc]

中文:
定理 rightUnitor_naturality
  条件: {f g : a ⟶ b} (η : f ⟶ g)
  证明: by simp

@[reassoc]
-/
theorem rightUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η := by simp

@[reassoc]
/--
theorem `rightUnitor_inv_naturality` / 定理 `rightUnitor_inv_naturality`

English:
theorem rightUnitor_inv_naturality
  given: {f g : a ⟶ b} (η : f ⟶ g)
  proof: by simp

中文:
定理 rightUnitor_inv_naturality
  条件: {f g : a ⟶ b} (η : f ⟶ g)
  证明: by simp
-/
theorem rightUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (ρ_ g).inv = (ρ_ f).inv ≫ η ▷ 𝟙 b := by simp

/--
theorem `whiskerRight_id_symm` / 定理 `whiskerRight_id_symm`

English:
theorem whiskerRight_id_symm
  given: {f g : a ⟶ b} (η : f ⟶ g)
  statement: η = (ρ_ f).inv ≫ η ▷ 𝟙 b ≫ (ρ_ g).hom
  proof: by
  simp

中文:
定理 whiskerRight_id_symm
  条件: {f g : a ⟶ b} (η : f ⟶ g)
  结论: η = (ρ_ f).inv ≫ η ▷ 𝟙 b ≫ (ρ_ g).hom
  证明: by
  simp
-/
theorem whiskerRight_id_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (ρ_ f).inv ≫ η ▷ 𝟙 b ≫ (ρ_ g).hom := by
  simp

/--
theorem `whiskerLeft_iff` / 定理 `whiskerLeft_iff`

English:
theorem whiskerLeft_iff
  given: {f g : a ⟶ b} (η θ : f ⟶ g)
  statement: 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ
  proof: by simp

中文:
定理 whiskerLeft_iff
  条件: {f g : a ⟶ b} (η θ : f ⟶ g)
  结论: 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ
  证明: by simp
-/
theorem whiskerLeft_iff {f g : a ⟶ b} (η θ : f ⟶ g) : 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ := by simp

/--
theorem `whiskerRight_iff` / 定理 `whiskerRight_iff`

English:
theorem whiskerRight_iff
  given: {f g : a ⟶ b} (η θ : f ⟶ g)
  statement: η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ
  proof: by simp

中文:
定理 whiskerRight_iff
  条件: {f g : a ⟶ b} (η θ : f ⟶ g)
  结论: η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ
  证明: by simp
-/
theorem whiskerRight_iff {f g : a ⟶ b} (η θ : f ⟶ g) : η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ := by simp

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight f g : 𝟙 f ▷ g = 𝟙 (f ≫ g)`.
-/
@[reassoc, simp]
/--
theorem `leftUnitor_whiskerRight` / 定理 `leftUnitor_whiskerRight`

English:
theorem leftUnitor_whiskerRight
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [← cancel_epi (α_ _ _ _).hom]; rw [←
      cancel_epi ((α_ _ _ _).hom ▷ _)]; rw [pentagon_assoc]; rw [triangle]; rw [← associator_naturality_middle]; rw [←
      comp_whiskerRight_assoc]; rw [triangle]; rw [associator_naturality_left]

@[reassoc, simp]

中文:
定理 leftUnitor_whiskerRight
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [← cancel_epi (α_ _ _ _).hom]; rw [←
      cancel_epi ((α_ _ _ _).hom ▷ _)]; rw [pentagon_assoc]; rw [triangle]; rw [← associator_naturality_middle]; rw [←
      comp_whiskerRight_assoc]; rw [triangle]; rw [associator_naturality_left]

@[reassoc, simp]

Depends on / 依赖: associator_naturality_left, associator_naturality_middle, cancel_epi, comp_whiskerRight_assoc, pentagon_assoc, triangle, whiskerLeft_comp, whiskerLeft_iff
-/
theorem leftUnitor_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (fun_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (fun_ (f ≫ g)).hom := by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [← cancel_epi (α_ _ _ _).hom]; rw [←
      cancel_epi ((α_ _ _ _).hom ▷ _)]; rw [pentagon_assoc]; rw [triangle]; rw [← associator_naturality_middle]; rw [←
      comp_whiskerRight_assoc]; rw [triangle]; rw [associator_naturality_left]

@[reassoc, simp]
/--
theorem `leftUnitor_inv_whiskerRight` / 定理 `leftUnitor_inv_whiskerRight`

English:
theorem leftUnitor_inv_whiskerRight
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc, simp]

中文:
定理 leftUnitor_inv_whiskerRight
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc, simp]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem leftUnitor_inv_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (fun_ f).inv ▷ g = (fun_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
/--
theorem `whiskerLeft_rightUnitor` / 定理 `whiskerLeft_rightUnitor`

English:
theorem whiskerLeft_rightUnitor
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [← cancel_epi (α_ _ _ _).inv]; rw [←
      cancel_epi (f ◁ (α_ _ _ _).inv)]; rw [pentagon_inv_assoc]; rw [triangle_assoc_comp_right]; rw [←
      associator_inv_naturality_middle]; rw [← whiskerLeft_comp_assoc]; rw [triangle_assoc_comp_right]; rw [associator_inv_naturality_right]

@[reassoc, simp]

中文:
定理 whiskerLeft_rightUnitor
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [← cancel_epi (α_ _ _ _).inv]; rw [←
      cancel_epi (f ◁ (α_ _ _ _).inv)]; rw [pentagon_inv_assoc]; rw [triangle_assoc_comp_right]; rw [←
      associator_inv_naturality_middle]; rw [← whiskerLeft_comp_assoc]; rw [triangle_assoc_comp_right]; rw [associator_inv_naturality_right]

@[reassoc, simp]

Depends on / 依赖: associator_inv_naturality_middle, associator_inv_naturality_right, cancel_epi, comp_whiskerRight, pentagon_inv_assoc, triangle_assoc_comp_right, whiskerLeft_comp_assoc, whiskerRight_iff
-/
theorem whiskerLeft_rightUnitor (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).hom := by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [← cancel_epi (α_ _ _ _).inv]; rw [←
      cancel_epi (f ◁ (α_ _ _ _).inv)]; rw [pentagon_inv_assoc]; rw [triangle_assoc_comp_right]; rw [←
      associator_inv_naturality_middle]; rw [← whiskerLeft_comp_assoc]; rw [triangle_assoc_comp_right]; rw [associator_inv_naturality_right]

@[reassoc, simp]
/--
theorem `whiskerLeft_rightUnitor_inv` / 定理 `whiskerLeft_rightUnitor_inv`

English:
theorem whiskerLeft_rightUnitor_inv
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: eq_of_inv_eq_inv (by simp)

中文:
定理 whiskerLeft_rightUnitor_inv
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: eq_of_inv_eq_inv (by simp)

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem whiskerLeft_rightUnitor_inv (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g (𝟙 c)).hom :=
  eq_of_inv_eq_inv (by simp)

/-
It is not so obvious whether `leftUnitor_whiskerRight` or `leftUnitor_comp` should be a simp
lemma. Our choice is the former. One reason is that the latter yields the following loop:
[id_whiskerLeft] : 𝟙 a ◁ (ρ_ f).hom ==> (λ_ (f ≫ 𝟙 b)).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv
[leftUnitor_comp] : (λ_ (f ≫ 𝟙 b)).hom ==> (α_ (𝟙 a) f (𝟙 b)).inv ≫ (λ_ f).hom ▷ 𝟙 b
[whiskerRight_id] : (λ_ f).hom ▷ 𝟙 b ==> (ρ_ (𝟙 a ≫ f)).hom ≫ (λ_ f).hom ≫ (ρ_ f).inv
[rightUnitor_comp] : (ρ_ (𝟙 a ≫ f)).hom ==> (α_ (𝟙 a) f (𝟙 b)).hom ≫ 𝟙 a ◁ (ρ_ f).hom
-/
@[reassoc]
/--
theorem `leftUnitor_comp` / 定理 `leftUnitor_comp`

English:
theorem leftUnitor_comp
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by simp

@[reassoc]

中文:
定理 leftUnitor_comp
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by simp

@[reassoc]
-/
theorem leftUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (fun_ (f ≫ g)).hom = (α_ (𝟙 a) f g).inv ≫ (fun_ f).hom ▷ g := by simp

@[reassoc]
/--
theorem `leftUnitor_comp_inv` / 定理 `leftUnitor_comp_inv`

English:
theorem leftUnitor_comp_inv
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by simp

@[reassoc]

中文:
定理 leftUnitor_comp_inv
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by simp

@[reassoc]
-/
theorem leftUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (fun_ (f ≫ g)).inv = (fun_ f).inv ▷ g ≫ (α_ (𝟙 a) f g).hom := by simp

@[reassoc]
/--
theorem `rightUnitor_comp` / 定理 `rightUnitor_comp`

English:
theorem rightUnitor_comp
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by simp

@[reassoc]

中文:
定理 rightUnitor_comp
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by simp

@[reassoc]
-/
theorem rightUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c)).hom ≫ f ◁ (ρ_ g).hom := by simp

@[reassoc]
/--
theorem `rightUnitor_comp_inv` / 定理 `rightUnitor_comp_inv`

English:
theorem rightUnitor_comp_inv
  given: (f : a ⟶ b) (g : b ⟶ c)
  proof: by simp

@[simp]

中文:
定理 rightUnitor_comp_inv
  条件: (f : a ⟶ b) (g : b ⟶ c)
  证明: by simp

@[simp]
-/
theorem rightUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ (f ≫ g)).inv = f ◁ (ρ_ g).inv ≫ (α_ f g (𝟙 c)).inv := by simp

@[simp]
/--
theorem `unitors_equal` / 定理 `unitors_equal`

English:
theorem unitors_equal
  statement: (fun_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom
  proof: by
  rw [← whiskerLeft_iff]; rw [← cancel_epi (α_ _ _ _).hom]; rw [← cancel_mono (ρ_ _).hom]; rw [triangle]; rw [←
      rightUnitor_comp]; rw [rightUnitor_naturality]

@[simp]

中文:
定理 unitors_equal
  结论: (fun_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom
  证明: by
  rw [← whiskerLeft_iff]; rw [← cancel_epi (α_ _ _ _).hom]; rw [← cancel_mono (ρ_ _).hom]; rw [triangle]; rw [←
      rightUnitor_comp]; rw [rightUnitor_naturality]

@[simp]

Depends on / 依赖: cancel_epi, cancel_mono, rightUnitor_comp, rightUnitor_naturality, triangle, whiskerLeft_iff
-/
theorem unitors_equal : (fun_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  rw [← whiskerLeft_iff]; rw [← cancel_epi (α_ _ _ _).hom]; rw [← cancel_mono (ρ_ _).hom]; rw [triangle]; rw [←
      rightUnitor_comp]; rw [rightUnitor_naturality]

@[simp]
/--
theorem `unitors_inv_equal` / 定理 `unitors_inv_equal`

English:
theorem unitors_inv_equal
  statement: (fun_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv
  proof: by simp [Iso.inv_eq_inv]

中文:
定理 unitors_inv_equal
  结论: (fun_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv
  证明: by simp [Iso.inv_eq_inv]

Depends on / 依赖: Iso.inv_eq_inv, inv_eq_inv
-/
theorem unitors_inv_equal : (fun_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by simp [Iso.inv_eq_inv]

section

attribute [local simp] whisker_exchange

/-- Precomposition of a 1-morphism as a functor. -/
@[simps]
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: (c : B) (f : a ⟶ b)
  body: (f ≫ ·)
  map := (f ◁ ·)

中文:
定义 precomp
  签名: (c : B) (f : a ⟶ b)
  定义体: (f ≫ ·)
  map := (f ◁ ·)
-/
def precomp (c : B) (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj := (f ≫ ·)
  map := (f ◁ ·)

set_option backward.defeqAttrib.useBackward true in
/-- Precomposition of a 1-morphism as a functor from the category of 1-morphisms `a ⟶ b` into the
category of functors `(b ⟶ c) ⥤ (a ⟶ c)`. -/
@[simps]
/--
Definition of `precomposing` / `precomposing` 的定义

English:
definition precomposing
  signature: (a b c : B)
  body: precomp c f
  map η := { app := (η ▷ ·) }

中文:
定义 precomposing
  签名: (a b c : B)
  定义体: precomp c f
  map η := { app := (η ▷ ·) }

Depends on / 依赖: precomp
-/
def precomposing (a b c : B) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) where
  obj f := precomp c f
  map η := { app := (η ▷ ·) }

/-- Postcomposition of a 1-morphism as a functor. -/
@[simps]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: (a : B) (f : b ⟶ c)
  body: (· ≫ f)
  map := (· ▷ f)

中文:
定义 postcomp
  签名: (a : B) (f : b ⟶ c)
  定义体: (· ≫ f)
  map := (· ▷ f)
-/
def postcomp (a : B) (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj := (· ≫ f)
  map := (· ▷ f)

set_option backward.defeqAttrib.useBackward true in
/-- Postcomposition of a 1-morphism as a functor from the category of 1-morphisms `b ⟶ c` into the
category of functors `(a ⟶ b) ⥤ (a ⟶ c)`. -/
@[simps]
/--
Definition of `postcomposing` / `postcomposing` 的定义

English:
definition postcomposing
  signature: (a b c : B)
  body: postcomp a f
  map η := { app := (· ◁ η) }

中文:
定义 postcomposing
  签名: (a b c : B)
  定义体: postcomp a f
  map η := { app := (· ◁ η) }

Depends on / 依赖: postcomp
-/
def postcomposing (a b c : B) : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := postcomp a f
  map η := { app := (· ◁ η) }

set_option backward.defeqAttrib.useBackward true in
/-- Left component of the associator as a natural isomorphism. -/
@[simps!]
/--
Definition of `associatorNatIsoLeft` / `associatorNatIsoLeft` 的定义

English:
definition associatorNatIsoLeft
  signature: (a : B) (g : b ⟶ c) (h : c ⟶ d)
  body: NatIso.ofComponents (α_ · g h)

中文:
定义 associator自然数IsoLeft
  签名: (a : B) (g : b ⟶ c) (h : c ⟶ d)
  定义体: NatIso.ofComponents (α_ · g h)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def associatorNatIsoLeft (a : B) (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposing a ..).obj g ⋙ (postcomposing ..).obj h ≅ (postcomposing ..).obj (g ≫ h) :=
  NatIso.ofComponents (α_ · g h)

set_option backward.defeqAttrib.useBackward true in
/-- Middle component of the associator as a natural isomorphism. -/
@[simps!]
/--
Definition of `associatorNatIsoMiddle` / `associatorNatIsoMiddle` 的定义

English:
definition associatorNatIsoMiddle
  signature: (f : a ⟶ b) (h : c ⟶ d)
  body: NatIso.ofComponents (α_ f · h)

中文:
定义 associator自然数IsoMiddle
  签名: (f : a ⟶ b) (h : c ⟶ d)
  定义体: NatIso.ofComponents (α_ f · h)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def associatorNatIsoMiddle (f : a ⟶ b) (h : c ⟶ d) :
    (precomposing ..).obj f ⋙ (postcomposing ..).obj h ≅
      (postcomposing ..).obj h ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f · h)

set_option backward.defeqAttrib.useBackward true in
/-- Right component of the associator as a natural isomorphism. -/
@[simps!]
/--
Definition of `associatorNatIsoRight` / `associatorNatIsoRight` 的定义

English:
definition associatorNatIsoRight
  signature: (f : a ⟶ b) (g : b ⟶ c) (d : B)
  body: NatIso.ofComponents (α_ f g ·)

中文:
定义 associator自然数IsoRight
  签名: (f : a ⟶ b) (g : b ⟶ c) (d : B)
  定义体: NatIso.ofComponents (α_ f g ·)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def associatorNatIsoRight (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposing _ _ d).obj (f ≫ g) ≅ (precomposing ..).obj g ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f g ·)

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor as a natural isomorphism. -/
@[simps!]
/--
Definition of `leftUnitorNatIso` / `leftUnitorNatIso` 的定义

English:
definition leftUnitorNatIso
  signature: (a b : B)
  body: NatIso.ofComponents (fun_ ·)

中文:
定义 leftUnitor自然数Iso
  签名: (a b : B)
  定义体: NatIso.ofComponents (fun_ ·)

Depends on / 依赖: NatIso, NatIso.ofComponents, fun_, ofComponents
-/
def leftUnitorNatIso (a b : B) : (precomposing _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (fun_ ·)

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor as a natural isomorphism. -/
@[simps!]
/--
Definition of `rightUnitorNatIso` / `rightUnitorNatIso` 的定义

English:
definition rightUnitorNatIso
  signature: (a b : B)
  body: NatIso.ofComponents (ρ_ ·)

中文:
定义 rightUnitor自然数Iso
  签名: (a b : B)
  定义体: NatIso.ofComponents (ρ_ ·)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def rightUnitorNatIso (a b : B) : (postcomposing a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (ρ_ ·)

end

end Bicategory

end CategoryTheory
