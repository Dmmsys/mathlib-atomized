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
/-- In a bicategory, we can compose the 1-morphisms `f : a ⟶ b` and `g : b ⟶ c` to obtain
a 1-morphism `f ≫ g : a ⟶ c`. This composition does not need to be strictly associative,
but there is a specified associator, `α_ f g h : (f ≫ g) ≫ h ≅ f ≫ (g ≫ h)`.
There is an identity 1-morphism `𝟙 a : a ⟶ a`, with specified left and right unitor
isomorphisms `λ_ f : 𝟙 a ≫ f ≅ f` and `ρ_ f : f ≫ 𝟙 a ≅ f`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://ncatlab.org/nlab/show/bicategory.
-/
/-
**CategoryTheory.Bicategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：Bicategory (B : Type u) extends CategoryStruct.{v} B where /-- The categor
y structure on the collection of 1-morphisms -/ homCategory : forall a b : B, Ca
tegory.{w} (a ⟶ b)
参数：B : Type u。
继承自：CategoryStruct.{v} B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a bicategory, we can compose the 1-morphisms `f : a ⟶ b` and `g : b ⟶ c` to o
btain
a 1-morphism `f ≫ g : a ⟶ c`. This composition does not need to be strictly asso
ciative,
but there is a specified associator, `α_ f g h : (f ≫ g) ≫ h ≅ f ≫ (g ≫ h)`.
There is an identity 1-morphism `𝟙 a : a ⟶ a`, with specified left and right uni
tor
isomorphisms `λ_ f : 𝟙 a ≫ f ≅ f` and `ρ_ f : f ≫ 𝟙 a ≅ f`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://ncatlab.org/nlab/show/bicategory.
-/
class Bicategory (B : Type u) extends CategoryStruct.{v} B where
  /-- The category structure on the collection of 1-morphisms -/
  homCategory : ∀ a b : B, Category.{w} (a ⟶ b) := by infer_instance
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
  whiskerLeft_id : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := by
    cat_disch
  whiskerLeft_comp :
    ∀ {a b c} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i),
      whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := by
    cat_disch
  id_whiskerLeft :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerLeft (𝟙 a) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := by
    cat_disch
  comp_whiskerLeft :
    ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h'),
      whiskerLeft (f ≫ g) η =
        (associator f g h).hom ≫ whiskerLeft f (whiskerLeft g η) ≫ (associator f g h').inv := by
    cat_disch
  -- axioms for right whiskering:
  id_whiskerRight : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := by
    cat_disch
  comp_whiskerRight :
    ∀ {a b c} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c),
      whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := by
    cat_disch
  whiskerRight_id :
    ∀ {a b} {f g : a ⟶ b} (η : f ⟶ g),
      whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := by
    cat_disch
  whiskerRight_comp :
    ∀ {a b c d} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d),
      whiskerRight η (g ≫ h) =
        (associator f g h).inv ≫ whiskerRight (whiskerRight η g) h ≫ (associator f' g h).hom := by
    cat_disch
  -- associativity of whiskerings:
  whisker_assoc :
    ∀ {a b c d} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d),
      whiskerRight (whiskerLeft f η) h =
        (associator f g h).hom ≫ whiskerLeft f (whiskerRight η h) ≫ (associator f g' h).inv := by
    cat_disch
  -- exchange law of left and right whiskerings:
  whisker_exchange :
    ∀ {a b c} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
      whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := by
    cat_disch
  -- pentagon identity:
  pentagon :
    ∀ {a b c d e} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
      whiskerRight (associator f g h).hom i ≫
          (associator f (g ≫ h) i).hom ≫ whiskerLeft f (associator g h i).hom =
        (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom := by
    cat_disch
  -- triangle identity:
  triangle :
    ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      (associator f (𝟙 b) g).hom ≫ whiskerLeft f (leftUnitor g).hom
      = whiskerRight (rightUnitor f).hom g := by
    cat_disch

namespace Bicategory

@[inherit_doc] scoped infixr:81 " ◁ " => Bicategory.whiskerLeft
@[inherit_doc] scoped infixl:81 " ▷ " => Bicategory.whiskerRight
@[inherit_doc] scoped notation "α_" => Bicategory.associator
@[inherit_doc] scoped notation "λ_" => Bicategory.leftUnitor
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
/-
**CategoryTheory.Bicategory.whiskerLeft_hom_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ◁ η.hom ≫ f 
◁ η.inv = 𝟙 (f ≫ g)
参数：f : a ⟶ b；η : g ≅ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
-/
theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g) := by rw [← whiskerLeft_comp, hom_inv_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.hom_inv_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：hom_inv_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.hom ▷ h ≫ η
.inv ▷ h = 𝟙 (f ≫ h)
参数：η : f ≅ g；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
-/
theorem hom_inv_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
    η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h) := by rw [← comp_whiskerRight, hom_inv_id, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.whiskerLeft_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：whiskerLeft_inv_hom (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ◁ η.inv ≫ f 
◁ η.hom = 𝟙 (f ≫ h)
参数：f : a ⟶ b；η : g ≅ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
-/
theorem whiskerLeft_inv_hom (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h) := by rw [← whiskerLeft_comp, inv_hom_id, whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.inv_hom_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：inv_hom_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.inv ▷ h ≫ η
.hom ▷ h = 𝟙 (g ≫ h)
参数：η : f ≅ g；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
-/
theorem inv_hom_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) :
    η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h) := by rw [← comp_whiskerRight, inv_hom_id, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.whiskerLeft_whiskerLeft_hom_inv** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：whiskerLeft_whiskerLeft_hom_inv (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η :
 h ≅ k) : f ◁ g ◁ η.hom ≫ f ◁ g ◁ η.inv = 𝟙 (f ≫ g ≫ h)
参数：f : a ⟶ b；g : b ⟶ c；η : h ≅ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_whiskerLeft_hom_inv (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k) :
    f ◁ g ◁ η.hom ≫ f ◁ g ◁ η.inv = 𝟙 (f ≫ g ≫ h) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.hom_inv_whiskerRight_whiskerRight** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：hom_inv_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k
 : c ⟶ d) : η.hom ▷ h ▷ k ≫ η.inv ▷ h ▷ k = 𝟙 ((f ≫ h) ≫ k)
参数：η : f ≅ g；h : b ⟶ c；k : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_inv_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d) :
    η.hom ▷ h ▷ k ≫ η.inv ▷ h ▷ k = 𝟙 ((f ≫ h) ≫ k) := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.whiskerLeft_whiskerLeft_inv_hom** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：whiskerLeft_whiskerLeft_inv_hom (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η :
 h ≅ k) : f ◁ g ◁ η.inv ≫ f ◁ g ◁ η.hom = 𝟙 (f ≫ g ≫ k)
参数：f : a ⟶ b；g : b ⟶ c；η : h ≅ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_whiskerLeft_inv_hom (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ≅ k) :
    f ◁ g ◁ η.inv ≫ f ◁ g ◁ η.hom = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.inv_hom_whiskerRight_whiskerRight** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：inv_hom_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k
 : c ⟶ d) : η.inv ▷ h ▷ k ≫ η.hom ▷ h ▷ k = 𝟙 ((g ≫ h) ≫ k)
参数：η : f ≅ g；h : b ⟶ c；k : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_hom_whiskerRight_whiskerRight {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) (k : c ⟶ d) :
    η.inv ▷ h ▷ k ≫ η.hom ▷ h ▷ k = 𝟙 ((g ≫ h) ≫ k) := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.whiskerLeft_hom_inv_whiskerRight** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：whiskerLeft_hom_inv_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k 
: c ⟶ d) : f ◁ η.hom ▷ k ≫ f ◁ η.inv ▷ k = 𝟙 (f ≫ g ≫ k)
参数：f : a ⟶ b；η : g ≅ h；k : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.hom_inv_whiskerRight`：hom_inv_whiskerRight {f 
g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h)
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_hom_inv_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.hom ▷ k ≫ f ◁ η.inv ▷ k = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.whiskerLeft_inv_hom_whiskerRight** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：whiskerLeft_inv_hom_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k 
: c ⟶ d) : f ◁ η.inv ▷ k ≫ f ◁ η.hom ▷ k = 𝟙 (f ≫ h ≫ k)
参数：f : a ⟶ b；η : g ≅ h；k : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.inv_hom_whiskerRight`：inv_hom_whiskerRight {f 
g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h)
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_inv_hom_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.inv ▷ k ≫ f ◁ η.hom ▷ k = 𝟙 (f ≫ h ≫ k) := by
  simp [← whiskerLeft_comp]

/-- The left whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps]
/-
**CategoryTheory.Bicategory.whiskerLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Bicategory`。
形式化陈述：whiskerLeftIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ≫ g ≅ f ≫ h where
 hom
参数：f : a ⟶ b；η : g ≅ h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left whiskering of a 2-isomorphism is a 2-isomorphism.
-/
def whiskerLeftIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ≫ g ≅ f ≫ h where
  hom := f ◁ η.hom
  inv := f ◁ η.inv
/-
**CategoryTheory.Bicategory.whiskerLeft_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：whiskerLeft_isIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : IsIso 
(f ◁ η)
参数：f : a ⟶ b；η : g ⟶ h。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance whiskerLeft_isIso (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : IsIso (f ◁ η) :=
  (whiskerLeftIso f (asIso η)).isIso_hom

@[simp, push]
/-
**CategoryTheory.Bicategory.inv_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：inv_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁
 η) = f ◁ inv η
参数：f : a ⟶ b；η : g ⟶ h。
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
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) [IsIso η] :
    inv (f ◁ η) = f ◁ inv η := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp only [← whiskerLeft_comp, whiskerLeft_id, IsIso.hom_inv_id]

/-- The right whiskering of a 2-isomorphism is a 2-isomorphism. -/
@[simps!]
/-
**CategoryTheory.Bicategory.whiskerRightIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：whiskerRightIso {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h wher
e hom
参数：η : f ≅ g；h : b ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right whiskering of a 2-isomorphism is a 2-isomorphism.
-/
def whiskerRightIso {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h where
  hom := η.hom ▷ h
  inv := η.inv ▷ h
/-
**CategoryTheory.Bicategory.whiskerRight_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：whiskerRight_isIso {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : IsIso
 (η ▷ h)
参数：η : f ⟶ g；h : b ⟶ c。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance whiskerRight_isIso {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : IsIso (η ▷ h) :=
  (whiskerRightIso (asIso η) h).isIso_hom

@[simp, push]
/-
**CategoryTheory.Bicategory.inv_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：inv_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η 
▷ h) = inv η ▷ h
参数：η : f ⟶ g；h : b ⟶ c。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**CategoryTheory.Bicategory.pentagon_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Bicategory`。
形式化陈述：pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : f ◁ (α_ g h
 i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i = (α_ f g (h ≫ i)).inv ≫ (α_
 (f ≫ g) h i).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.pentagon`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
   CategoryTheory.Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i =
      (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_inv_inv_hom_hom_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_inv_inv_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom = f ◁ (α_ 
g h i).hom ≫ (α_ f g (h ≫ i)).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv_assoc`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i
 : d ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_inv_hom_assoc`：∀ {B : Type u} [ins
t : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ 
h) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_inv_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom =
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv := by
  rw [← cancel_epi (f ◁ (α_ g h i).inv), ← cancel_mono (α_ (f ≫ g) h i).inv]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_inv_hom_hom_hom_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_inv_hom_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom = (α_ f g 
(h ≫ i)).hom ≫ f ◁ (α_ g h i).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv_inv_hom_hom_inv`：pentagon_inv_inv
_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : (α_ f (g ≫ h) i).
inv ≫ (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).…
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_hom_hom_hom_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom =
      (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_hom_inv_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv = (α_ f (g
 ≫ h) i).inv ≫ (α_ f g h).inv ▷ i
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_inv_hom_assoc`：∀ {B : Type u} [ins
t : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ 
h) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv`：pentagon_inv (f : a ⟶ b) (g : b 
⟶ c) (h : c ⟶ d) (i : d ⟶ e) : f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f
 g h).inv ▷ i = (α_ f g (h ≫…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_inv_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
      (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  simp [← cancel_epi (f ◁ (α_ g h i).inv)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_hom_hom_inv_hom_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_hom_hom_inv_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv = (α_ f g 
h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_inv`：pentagon_hom_inv
_inv_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : f ◁ (α_ g h i).ho
m ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).…
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_hom_inv_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv =
      (α_ f g h).hom ▷ i ≫ (α_ f (g ≫ h) i).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_hom_inv_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv = (α_ (f ≫
 g) h i).inv ≫ (α_ f g h).hom ▷ i
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv`：pentagon_inv (f : a ⟶ b) (g : b 
⟶ c) (h : c ⟶ d) (i : d ⟶ e) : f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv ≫ (α_ f
 g h).inv ▷ i = (α_ f g (h ≫…
· 使用定理 `CategoryTheory.Bicategory.hom_inv_whiskerRight`：hom_inv_whiskerRight {f 
g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_inv_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g (h ≫ i)).hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv =
    (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i := by
  rw [← cancel_epi (α_ f g (h ≫ i)).inv, ← cancel_mono ((α_ f g h).inv ▷ i)]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_hom_hom_inv_inv_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv = (α_ f g 
h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_hom`：pentagon_hom_inv
_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : (α_ f g (h ≫ i)).
hom ≫ f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).…
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv =
      (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_inv_hom_hom_hom_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_inv_hom_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom = (α_ f (g
 ≫ h) i).hom ≫ f ◁ (α_ g h i).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.hom_inv_whiskerRight_assoc`：∀ {B : Type u} [in
st : CategoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶
 c) {Z : a ⟶ c}   (h_1 : CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Bicategory.pentagon`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
   CategoryTheory.Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_hom_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
      (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom := by
  simp [← cancel_epi ((α_ f g h).hom ▷ i)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.pentagon_inv_inv_hom_inv_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：pentagon_inv_inv_hom_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ 
e) : (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i = f ◁ (α_ 
g h i).inv ≫ (α_ f (g ≫ h) i).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : d ⟶ e。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv_hom_hom_hom_hom`：pentagon_inv_hom
_hom_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) : (α_ f g h).inv ▷ 
i ≫ (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).…
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pentagon_inv_inv_hom_inv_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv ≫ (α_ f g h).hom ▷ i =
      f ◁ (α_ g h i).inv ≫ (α_ f (g ≫ h) i).inv :=
  eq_of_inv_eq_inv (by simp)
/-
**CategoryTheory.Bicategory.triangle_assoc_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bicategory`。
形式化陈述：triangle_assoc_comp_left (f : a ⟶ b) (g : b ⟶ c) : (α_ f (𝟙 b) g).hom ≫ f 
◁ (fun_ g).hom = (ρ_ f).hom ▷ g
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.triangle`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.CategorySt
ruct.comp (CategoryTheor…
-/
theorem triangle_assoc_comp_left (f : a ⟶ b) (g : b ⟶ c) :
    (α_ f (𝟙 b) g).hom ≫ f ◁ (λ_ g).hom = (ρ_ f).hom ▷ g :=
  triangle f g

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.triangle_assoc_comp_right** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：triangle_assoc_comp_right (f : a ⟶ b) (g : b ⟶ c) : (α_ f (𝟙 b) g).inv ≫ (
ρ_ f).hom ▷ g = f ◁ (fun_ g).hom
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.triangle`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.CategorySt
ruct.comp (CategoryTheor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem triangle_assoc_comp_right (f : a ⟶ b) (g : b ⟶ c) :
    (α_ f (𝟙 b) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (λ_ g).hom := by rw [← triangle, inv_hom_id_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.triangle_assoc_comp_right_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Bicategory`。
形式化陈述：triangle_assoc_comp_right_inv (f : a ⟶ b) (g : b ⟶ c) : (ρ_ f).inv ▷ g ≫ (
α_ f (𝟙 b) g).hom = f ◁ (fun_ g).inv
参数：f : a ⟶ b；g : b ⟶ c。
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
· 使用定理 `CategoryTheory.Bicategory.triangle`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.CategorySt
ruct.comp (CategoryTheor…
· 使用定理 `CategoryTheory.Bicategory.inv_hom_whiskerRight`：inv_hom_whiskerRight {f 
g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h)
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_inv_hom`：whiskerLeft_inv_hom (f : 
a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem triangle_assoc_comp_right_inv (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ f).inv ▷ g ≫ (α_ f (𝟙 b) g).hom = f ◁ (λ_ g).inv := by
  simp [← cancel_mono (f ◁ (λ_ g).hom)]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.triangle_assoc_comp_left_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：triangle_assoc_comp_left_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (fun_ g).inv ≫ 
(α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g
参数：f : a ⟶ b；g : b ⟶ c。
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
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc_comp_right`：triangle_assoc_comp
_right (f : a ⟶ b) (g : b ⟶ c) : (α_ f (𝟙 b) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (fun_
 g).hom
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_inv_hom`：whiskerLeft_inv_hom (f : 
a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ◁ η.inv ≫ f ◁ η.hom = 𝟙 (f ≫ h)
· 使用定理 `CategoryTheory.Bicategory.inv_hom_whiskerRight`：inv_hom_whiskerRight {f 
g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.inv ▷ h ≫ η.hom ▷ h = 𝟙 (g ≫ h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem triangle_assoc_comp_left_inv (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g := by
  simp [← cancel_mono ((ρ_ f).hom ▷ g)]

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_naturality_left** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c 
⟶ d) : η ▷ g ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h)
参数：η : f ⟶ f'；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h ≫ (α_ f' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h) := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_inv_naturality_left** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory`。
形式化陈述：associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h 
: c ⟶ d) : η ▷ (g ≫ h) ≫ (α_ f' g h).inv = (α_ f g h).inv ≫ η ▷ g ▷ h
参数：η : f ⟶ f'；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
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
theorem associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) ≫ (α_ f' g h).inv = (α_ f g h).inv ≫ η ▷ g ▷ h := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.whiskerRight_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Bicategory`。
形式化陈述：whiskerRight_comp_symm {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d)
 : η ▷ g ▷ h = (α_ f g h).hom ≫ η ▷ (g ≫ h) ≫ (α_ f' g h).inv
参数：η : f ⟶ f'；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
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
theorem whiskerRight_comp_symm {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h = (α_ f g h).hom ≫ η ▷ (g ≫ h) ≫ (α_ f' g h).inv := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_naturality_middle** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Bicategory`。
形式化陈述：associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d) : (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ h
参数：f : a ⟶ b；η : g ⟶ g'；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
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
theorem associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h ≫ (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ h := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_inv_naturality_middle** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (
h : c ⟶ d) : f ◁ η ▷ h ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ (f ◁ η) ▷ h
参数：f : a ⟶ b；η : g ⟶ g'；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    f ◁ η ▷ h ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ (f ◁ η) ▷ h := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.whisker_assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：whisker_assoc_symm (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) : f
 ◁ η ▷ h = (α_ f g h).inv ≫ (f ◁ η) ▷ h ≫ (α_ f g' h).hom
参数：f : a ⟶ b；η : g ⟶ g'；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
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
theorem whisker_assoc_symm (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    f ◁ η ▷ h = (α_ f g h).inv ≫ (f ◁ η) ▷ h ≫ (α_ f g' h).hom := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_naturality_right** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Bicategory`。
形式化陈述：associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h 
⟶ h') : (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ g ◁ η
参数：f : a ⟶ b；g : b ⟶ c；η : h ⟶ h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
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
theorem associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η ≫ (α_ f g h').hom = (α_ f g h).hom ≫ f ◁ g ◁ η := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.associator_inv_naturality_right** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h') : f ◁ g ◁ η ≫ (α_ f g h').inv = (α_ f g h).inv ≫ (f ≫ g) ◁ η
参数：f : a ⟶ b；g : b ⟶ c；η : h ⟶ h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η ≫ (α_ f g h').inv = (α_ f g h).inv ≫ (f ≫ g) ◁ η := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.comp_whiskerLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：comp_whiskerLeft_symm (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') 
: f ◁ g ◁ η = (α_ f g h).inv ≫ (f ≫ g) ◁ η ≫ (α_ f g h').hom
参数：f : a ⟶ b；g : b ⟶ c；η : h ⟶ h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
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
theorem comp_whiskerLeft_symm (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    f ◁ g ◁ η = (α_ f g h).inv ≫ (f ≫ g) ◁ η ≫ (α_ f g h').hom := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.leftUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：leftUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) : 𝟙 a ◁ η ≫ (fun_ g).hom =
 (fun_ f).hom ≫ η
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
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
theorem leftUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η ≫ (λ_ g).hom = (λ_ f).hom ≫ η := by
  simp

@[reassoc]
/-
**CategoryTheory.Bicategory.leftUnitor_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：leftUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) : η ≫ (fun_ g).inv = (
fun_ f).inv ≫ 𝟙 a ◁ η
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (λ_ g).inv = (λ_ f).inv ≫ 𝟙 a ◁ η := by simp
/-
**CategoryTheory.Bicategory.id_whiskerLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：id_whiskerLeft_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (fun_ f).inv ≫ 𝟙 a ◁ η
 ≫ (fun_ g).hom
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
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
theorem id_whiskerLeft_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (λ_ f).inv ≫ 𝟙 a ◁ η ≫ (λ_ g).hom := by
  simp

@[reassoc]
/-
**CategoryTheory.Bicategory.rightUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Bicategory`。
形式化陈述：rightUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) : η ▷ 𝟙 b ≫ (ρ_ g).hom = 
(ρ_ f).hom ≫ η
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
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
theorem rightUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.rightUnitor_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：rightUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) : η ≫ (ρ_ g).inv = (ρ
_ f).inv ≫ η ▷ 𝟙 b
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (ρ_ g).inv = (ρ_ f).inv ≫ η ▷ 𝟙 b := by simp
/-
**CategoryTheory.Bicategory.whiskerRight_id_symm** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：whiskerRight_id_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (ρ_ f).inv ≫ η ▷ 𝟙 b 
≫ (ρ_ g).hom
参数：η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
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
theorem whiskerRight_id_symm {f g : a ⟶ b} (η : f ⟶ g) : η = (ρ_ f).inv ≫ η ▷ 𝟙 b ≫ (ρ_ g).hom := by
  simp
/-
**CategoryTheory.Bicategory.whiskerLeft_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：whiskerLeft_iff {f g : a ⟶ b} (η θ : f ⟶ g) : 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ
参数：η θ : f ⟶ g。
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
· 使用定理 `CategoryTheory.Bicategory.id_whiskerLeft`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bica
tegory.whiskerLeft (CategoryTh…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem whiskerLeft_iff {f g : a ⟶ b} (η θ : f ⟶ g) : 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ := by simp
/-
**CategoryTheory.Bicategory.whiskerRight_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：whiskerRight_iff {f g : a ⟶ b} (η θ : f ⟶ g) : η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ
参数：η θ : f ⟶ g。
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
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_id`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b : B} {f g : a ⟶ b} (η : f ⟶ g),   CategoryTheory.Bic
ategory.whiskerRight η (Categor…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem whiskerRight_iff {f g : a ⟶ b} (η θ : f ⟶ g) : η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ := by simp

/-- We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight f g : 𝟙 f ▷ g = 𝟙 (f ≫ g)`.
-/
@[reassoc, simp]
/-
**CategoryTheory.Bicategory.leftUnitor_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Bicategory`。
形式化陈述：leftUnitor_whiskerRight (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).hom ▷ g = (α_ (
𝟙 a) f g).hom ≫ (fun_ (f ≫ g)).hom
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_iff`：whiskerLeft_iff {f g : a ⟶ b}
 (η θ : f ⟶ g) : 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Bicategory.pentagon_assoc`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d
 ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `CategoryTheory.Bicategory.triangle`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.CategorySt
ruct.comp (CategoryTheor…
· 使用定理 `CategoryTheory.Bicategory.associator_naturality_middle`：associator_natur
ality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) : (f ◁ η) ▷ h ≫
 (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ …
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight_assoc`：∀ {B : Type u} [self 
: CategoryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ 
h) (i : b ⟶ c)   {Z : a ⟶ c} (h_1 : Cat…
· 使用定理 `CategoryTheory.Bicategory.associator_naturality_left`：associator_natural
ity_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) : η ▷ g ▷ h ≫ (α_ f
' g h).hom = (α_ f g h).hom ≫ η ▷ (g ≫ h)

--- 原说明 ---
We state it as a simp lemma, which is regarded as an involved version of
`id_whiskerRight f g : 𝟙 f ▷ g = 𝟙 (f ≫ g)`.
-/
theorem leftUnitor_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (λ_ (f ≫ g)).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, ← cancel_epi (α_ _ _ _).hom, ←
      cancel_epi ((α_ _ _ _).hom ▷ _), pentagon_assoc, triangle, ← associator_naturality_middle, ←
      comp_whiskerRight_assoc, triangle, associator_naturality_left]

@[reassoc, simp]
/-
**CategoryTheory.Bicategory.leftUnitor_inv_whiskerRight** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Bicategory`。
形式化陈述：leftUnitor_inv_whiskerRight (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).inv ▷ g = (
fun_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv
参数：f : a ⟶ b；g : b ⟶ c。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_whiskerRight`：leftUnitor_whiskerRig
ht (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (fun_ (f ≫ 
g)).hom
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_inv_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ f).inv ▷ g = (λ_ (f ≫ g)).inv ≫ (α_ (𝟙 a) f g).inv :=
  eq_of_inv_eq_inv (by simp)

@[reassoc, simp]
/-
**CategoryTheory.Bicategory.whiskerLeft_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Bicategory`。
形式化陈述：whiskerLeft_rightUnitor (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g
 (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).hom
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_iff`：whiskerRight_iff {f g : a ⟶ 
b} (η θ : f ⟶ g) : η ▷ 𝟙 b = θ ▷ 𝟙 b ↔ η = θ
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv_assoc`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i
 : d ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc_comp_right`：triangle_assoc_comp
_right (f : a ⟶ b) (g : b ⟶ c) : (α_ f (𝟙 b) g).inv ≫ (ρ_ f).hom ▷ g = f ◁ (fun_
 g).hom
· 使用定理 `CategoryTheory.Bicategory.associator_inv_naturality_middle`：associator_i
nv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) : f ◁ η
 ▷ h ≫ (α_ f g' h).inv = (α_ f g h).inv ≫ (f ◁ η…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp_assoc`：∀ {B : Type u} [self :
 CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h
) (θ : h ⟶ i)   {Z : a ⟶ c} (h_1 : Cat…
· 使用定理 `CategoryTheory.Bicategory.associator_inv_naturality_right`：associator_in
v_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') : f ◁ g ◁
 η ≫ (α_ f g h').inv = (α_ f g h).inv ≫ (f ≫ g)…
-/
theorem whiskerLeft_rightUnitor (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, ← cancel_epi (α_ _ _ _).inv, ←
      cancel_epi (f ◁ (α_ _ _ _).inv), pentagon_inv_assoc, triangle_assoc_comp_right, ←
      associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, triangle_assoc_comp_right,
      associator_inv_naturality_right]

@[reassoc, simp]
/-
**CategoryTheory.Bicategory.whiskerLeft_rightUnitor_inv** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Bicategory`。
形式化陈述：whiskerLeft_rightUnitor_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).inv = (ρ_
 (f ≫ g)).inv ≫ (α_ f g (𝟙 c)).hom
参数：f : a ⟶ b；g : b ⟶ c。
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
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_rightUnitor_inv (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g (𝟙 c)).hom :=
  eq_of_inv_eq_inv (by simp)

/-
It is not so obvious whether `leftUnitor_whiskerRight` or `leftUnitor_comp` should be a simp
lemma. Our choice is the former. One reason is that the latter yields the following loop:
[id_whiskerLeft]   : 𝟙 a ◁ (ρ_ f).hom ==> (λ_ (f ≫ 𝟙 b)).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv
[leftUnitor_comp]  : (λ_ (f ≫ 𝟙 b)).hom ==> (α_ (𝟙 a) f (𝟙 b)).inv ≫ (λ_ f).hom ▷ 𝟙 b
[whiskerRight_id]  : (λ_ f).hom ▷ 𝟙 b ==> (ρ_ (𝟙 a ≫ f)).hom ≫ (λ_ f).hom ≫ (ρ_ f).inv
[rightUnitor_comp] : (ρ_ (𝟙 a ≫ f)).hom ==> (α_ (𝟙 a) f (𝟙 b)).hom ≫ 𝟙 a ◁ (ρ_ f).hom
-/
@[reassoc]
/-
**CategoryTheory.Bicategory.leftUnitor_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：leftUnitor_comp (f : a ⟶ b) (g : b ⟶ c) : (fun_ (f ≫ g)).hom = (α_ (𝟙 a) f
 g).inv ≫ (fun_ f).hom ▷ g
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_whiskerRight`：leftUnitor_whiskerRig
ht (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (fun_ (f ≫ 
g)).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
It is not so obvious whether `leftUnitor_whiskerRight` or `leftUnitor_comp` shou
ld be a simp
lemma. Our choice is the former. One reason is that the latter yields the follow
ing loop:
[id_whiskerLeft]   : 𝟙 a ◁ (ρ_ f).hom ==> (λ_ (f ≫ 𝟙 b)).hom ≫ (ρ_ f).hom ≫ (λ_ 
f).inv
[leftUnitor_comp]  : (λ_ (f ≫ 𝟙 b)).hom ==> (α_ (𝟙 a) f (𝟙 b)).inv ≫ (λ_ f).hom 
▷ 𝟙 b
[whiskerRight_id]  : (λ_ f).hom ▷ 𝟙 b ==> (ρ_ (𝟙 a ≫ f)).hom ≫ (λ_ f).hom ≫ (ρ_ 
f).inv
[rightUnitor_comp] : (ρ_ (𝟙 a ≫ f)).hom ==> (α_ (𝟙 a) f (𝟙 b)).hom ≫ 𝟙 a ◁ (ρ_ f
).hom
-/
theorem leftUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ (f ≫ g)).hom = (α_ (𝟙 a) f g).inv ≫ (λ_ f).hom ▷ g := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.leftUnitor_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：leftUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) : (fun_ (f ≫ g)).inv = (fun_ f
).inv ▷ g ≫ (α_ (𝟙 a) f g).hom
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_inv_whiskerRight`：leftUnitor_inv_wh
iskerRight (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).inv ▷ g = (fun_ (f ≫ g)).inv ≫ (α_
 (𝟙 a) f g).inv
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
theorem leftUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (λ_ (f ≫ g)).inv = (λ_ f).inv ▷ g ≫ (α_ (𝟙 a) f g).hom := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.rightUnitor_comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：rightUnitor_comp (f : a ⟶ b) (g : b ⟶ c) : (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c
)).hom ≫ f ◁ (ρ_ g).hom
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c)).hom ≫ f ◁ (ρ_ g).hom := by simp

@[reassoc]
/-
**CategoryTheory.Bicategory.rightUnitor_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：rightUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) : (ρ_ (f ≫ g)).inv = f ◁ (ρ_ 
g).inv ≫ (α_ f g (𝟙 c)).inv
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor_inv`：whiskerLeft_right
Unitor_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g
 (𝟙 c)).hom
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
theorem rightUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (ρ_ (f ≫ g)).inv = f ◁ (ρ_ g).inv ≫ (α_ f g (𝟙 c)).inv := by simp

@[simp]
/-
**CategoryTheory.Bicategory.unitors_equal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Bicategory`。
形式化陈述：unitors_equal : (fun_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_iff`：whiskerLeft_iff {f g : a ⟶ b}
 (η θ : f ⟶ g) : 𝟙 a ◁ η = 𝟙 a ◁ θ ↔ η = θ
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.Bicategory.triangle`：∀ {B : Type u} [self : CategoryTheor
y.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.CategorySt
ruct.comp (CategoryTheor…
· 使用定理 `CategoryTheory.Bicategory.rightUnitor_comp`：rightUnitor_comp (f : a ⟶ b)
 (g : b ⟶ c) : (ρ_ (f ≫ g)).hom = (α_ f g (𝟙 c)).hom ≫ f ◁ (ρ_ g).hom
· 使用定理 `CategoryTheory.Bicategory.rightUnitor_naturality`：rightUnitor_naturality
 {f g : a ⟶ b} (η : f ⟶ g) : η ▷ 𝟙 b ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η
-/
theorem unitors_equal : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  rw [← whiskerLeft_iff, ← cancel_epi (α_ _ _ _).hom, ← cancel_mono (ρ_ _).hom, triangle, ←
      rightUnitor_comp, rightUnitor_naturality]

@[simp]
/-
**CategoryTheory.Bicategory.unitors_inv_equal** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：unitors_inv_equal : (fun_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.unitors_equal`：unitors_equal : (fun_ (𝟙 a)).ho
m = (ρ_ (𝟙 a)).hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitors_inv_equal : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by simp [Iso.inv_eq_inv]

section

attribute [local simp] whisker_exchange

/-- Precomposition of a 1-morphism as a functor. -/
@[simps]
/-
**CategoryTheory.Bicategory.precomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bi
category`。
形式化陈述：precomp (c : B) (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where obj
参数：c : B；f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition of a 1-morphism as a functor.
-/
def precomp (c : B) (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj := (f ≫ ·)
  map := (f ◁ ·)

set_option backward.defeqAttrib.useBackward true in
/-- Precomposition of a 1-morphism as a functor from the category of 1-morphisms `a ⟶ b` into the
category of functors `(b ⟶ c) ⥤ (a ⟶ c)`. -/
@[simps]
/-
**CategoryTheory.Bicategory.precomposing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Bicategory`。
形式化陈述：precomposing (a b c : B) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) where obj f
参数：a b c : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition of a 1-morphism as a functor from the category of 1-morphisms `a 
⟶ b` into the
category of functors `(b ⟶ c) ⥤ (a ⟶ c)`.
-/
def precomposing (a b c : B) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) where
  obj f := precomp c f
  map η := { app := (η ▷ ·) }

/-- Postcomposition of a 1-morphism as a functor. -/
@[simps]
/-
**CategoryTheory.Bicategory.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
icategory`。
形式化陈述：postcomp (a : B) (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where obj
参数：a : B；f : b ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposition of a 1-morphism as a functor.
-/
def postcomp (a : B) (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj := (· ≫ f)
  map := (· ▷ f)

set_option backward.defeqAttrib.useBackward true in
/-- Postcomposition of a 1-morphism as a functor from the category of 1-morphisms `b ⟶ c` into the
category of functors `(a ⟶ b) ⥤ (a ⟶ c)`. -/
@[simps]
/-
**CategoryTheory.Bicategory.postcomposing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Bicategory`。
形式化陈述：postcomposing (a b c : B) : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) where obj f
参数：a b c : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposition of a 1-morphism as a functor from the category of 1-morphisms `b
 ⟶ c` into the
category of functors `(a ⟶ b) ⥤ (a ⟶ c)`.
-/
def postcomposing (a b c : B) : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := postcomp a f
  map η := { app := (· ◁ η) }

set_option backward.defeqAttrib.useBackward true in
/-- Left component of the associator as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.Bicategory.associatorNatIsoLeft** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：associatorNatIsoLeft (a : B) (g : b ⟶ c) (h : c ⟶ d) : (postcomposing a ..
).obj g ⋙ (postcomposing ..).obj h ≅ (postcomposing ..).obj (g ≫ h)
参数：a : B；g : b ⟶ c；h : c ⟶ d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left component of the associator as a natural isomorphism.
-/
def associatorNatIsoLeft (a : B) (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposing a ..).obj g ⋙ (postcomposing ..).obj h ≅ (postcomposing ..).obj (g ≫ h) :=
  NatIso.ofComponents (α_ · g h)

set_option backward.defeqAttrib.useBackward true in
/-- Middle component of the associator as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.Bicategory.associatorNatIsoMiddle** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Bicategory`。
形式化陈述：associatorNatIsoMiddle (f : a ⟶ b) (h : c ⟶ d) : (precomposing ..).obj f ⋙
 (postcomposing ..).obj h ≅ (postcomposing ..).obj h ⋙ (precomposing ..).obj f
参数：f : a ⟶ b；h : c ⟶ d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Middle component of the associator as a natural isomorphism.
-/
def associatorNatIsoMiddle (f : a ⟶ b) (h : c ⟶ d) :
    (precomposing ..).obj f ⋙ (postcomposing ..).obj h ≅
      (postcomposing ..).obj h ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f · h)

set_option backward.defeqAttrib.useBackward true in
/-- Right component of the associator as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.Bicategory.associatorNatIsoRight** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：associatorNatIsoRight (f : a ⟶ b) (g : b ⟶ c) (d : B) : (precomposing _ _ 
d).obj (f ≫ g) ≅ (precomposing ..).obj g ⋙ (precomposing ..).obj f
参数：f : a ⟶ b；g : b ⟶ c；d : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right component of the associator as a natural isomorphism.
-/
def associatorNatIsoRight (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposing _ _ d).obj (f ≫ g) ≅ (precomposing ..).obj g ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f g ·)

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.Bicategory.leftUnitorNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：leftUnitorNatIso (a b : B) : (precomposing _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b)
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left unitor as a natural isomorphism.
-/
def leftUnitorNatIso (a b : B) : (precomposing _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (λ_ ·)

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.Bicategory.rightUnitorNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：rightUnitorNatIso (a b : B) : (postcomposing a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b)
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right unitor as a natural isomorphism.
-/
def rightUnitorNatIso (a b : B) : (postcomposing a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (ρ_ ·)

end

end Bicategory

end CategoryTheory

