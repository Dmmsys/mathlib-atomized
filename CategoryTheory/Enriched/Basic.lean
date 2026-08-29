/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.Tactic.ApplyFun

/-!
# Enriched categories

We set up the basic theory of `V`-enriched categories,
for `V` an arbitrary monoidal category.

We do not assume here that `V` is a concrete category,
so there does not need to be an "honest" underlying category!

Use `X ⟶[V] Y` to obtain the `V` object of morphisms from `X` to `Y`.

This file contains the definitions of `V`-enriched categories and
`V`-functors.

We don't yet define the `V`-object of natural transformations
between a pair of `V`-functors (this requires limits in `V`),
but we do provide a presheaf isomorphic to the Yoneda embedding of this object.

We verify that when `V = Type v`, all these notions reduce to the usual ones.

## References

* [Kim Morrison, David Penneys, _Monoidal Categories Enriched in Braided Monoidal Categories_]
  [morrison-penney-enriched]
-/

@[expose] public section


universe w w' v v' u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/--
Definition of `EnrichedCategory` / `EnrichedCategory` 的定义

English:
class EnrichedCategory
  parameters: (C : Type u₁)
  axioms and operations (6):
    - Hom : C -> C -> V
    - id((X : C)) : 𝟙_ V ⟶ Hom X X
    - comp((X Y Z : C)) : Hom X Y otimes Hom Y Z ⟶ Hom X Z
    - id_comp((X Y : C)) : (fun_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _  [default: by cat_disch]
    - comp_id((X Y : C)) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _  [default: by cat_disch]
    - assoc((W X Y Z : C)) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z = _ ◁ comp X Y Z ≫ comp W X Z  [default: by cat_disch]

中文:
类 EnrichedCategory
  参数: (C : 类型u₁)
  公理与运算 (6 个):
    - Hom : C -> C -> V
    - id((X : C)) : 𝟙_ V ⟶ Hom X X
    - comp((X Y Z : C)) : Hom X Y otimes Hom Y Z ⟶ Hom X Z
    - id_comp((X Y : C)) : (fun_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _  [默认: by cat_disch]
    - comp_id((X Y : C)) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _  [默认: by cat_disch]
    - assoc((W X Y Z : C)) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z = _ ◁ comp X Y Z ≫ comp W X Z  [默认: by cat_disch]

Depends on / 依赖: cat_disch, comp_id
-/
class EnrichedCategory (C : Type u₁) where
  /-- `X ⟶[V] Y` is the `V` object of morphisms from `X` to `Y`. -/
  Hom : C -> C -> V
  /-- The identity morphism of this category -/
  id (X : C) : 𝟙_ V ⟶ Hom X X
  /-- Composition of two morphisms in this category -/
  comp (X Y Z : C) : Hom X Y otimes Hom Y Z ⟶ Hom X Z
  id_comp (X Y : C) : (fun_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _ := by cat_disch
  comp_id (X Y : C) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _ := by cat_disch
  assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z =
    _ ◁ comp X Y Z ≫ comp W X Z := by cat_disch

@[inherit_doc EnrichedCategory.Hom] notation3 X " ⟶[" V "] " Y:10 => (EnrichedCategory.Hom X Y : V)

variable {C : Type u₁} [EnrichedCategory V C]

/--
Definition of `eId` / `eId` 的定义

English:
definition eId
  signature: (X : C)
  body: EnrichedCategory.id X

中文:
定义 eId
  签名: (X : C)
  定义体: EnrichedCategory.id X

Depends on / 依赖: EnrichedCategory, EnrichedCategory.id
-/
def eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  EnrichedCategory.id X

/--
Definition of `eComp` / `eComp` 的定义

English:
definition eComp
  signature: (X Y Z : C)
  body: EnrichedCategory.comp X Y Z

@[reassoc (attr := simp)]

中文:
定义 eComp
  签名: (X Y Z : C)
  定义体: EnrichedCategory.comp X Y Z

@[reassoc (attr := simp)]

Depends on / 依赖: EnrichedCategory, EnrichedCategory.comp
-/
def eComp (X Y Z : C) : ((X ⟶[V] Y) otimes Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  EnrichedCategory.comp X Y Z

@[reassoc (attr := simp)]
/--
theorem `e_id_comp` / 定理 `e_id_comp`

English:
theorem e_id_comp
  given: (X Y : C)
  proof: EnrichedCategory.id_comp X Y

@[reassoc (attr := simp)]

中文:
定理 e_id_comp
  条件: (X Y : C)
  证明: EnrichedCategory.id_comp X Y

@[reassoc (attr := simp)]

Depends on / 依赖: EnrichedCategory, EnrichedCategory.id_comp, id_comp
-/
theorem e_id_comp (X Y : C) :
    (fun_ (X ⟶[V] Y)).inv ≫ eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.id_comp X Y

@[reassoc (attr := simp)]
/--
theorem `e_comp_id` / 定理 `e_comp_id`

English:
theorem e_comp_id
  given: (X Y : C)
  proof: EnrichedCategory.comp_id X Y

@[reassoc (attr := simp)]

中文:
定理 e_comp_id
  条件: (X Y : C)
  证明: EnrichedCategory.comp_id X Y

@[reassoc (attr := simp)]

Depends on / 依赖: EnrichedCategory, EnrichedCategory.comp_id, comp_id
-/
theorem e_comp_id (X Y : C) :
    (ρ_ (X ⟶[V] Y)).inv ≫ _ ◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.comp_id X Y

@[reassoc (attr := simp)]
/--
theorem `e_assoc` / 定理 `e_assoc`

English:
theorem e_assoc
  given: (W X Y Z : C)
  proof: EnrichedCategory.assoc W X Y Z

@[reassoc]

中文:
定理 e_assoc
  条件: (W X Y Z : C)
  证明: EnrichedCategory.assoc W X Y Z

@[reassoc]

Depends on / 依赖: EnrichedCategory, EnrichedCategory.assoc
-/
theorem e_assoc (W X Y Z : C) :
    (α_ _ _ _).inv ≫ eComp V W X Y ▷ _ ≫ eComp V W Y Z =
      _ ◁ eComp V X Y Z ≫ eComp V W X Z :=
  EnrichedCategory.assoc W X Y Z

@[reassoc]
/--
theorem `e_assoc'` / 定理 `e_assoc'`

English:
theorem e_assoc'
  given: (W X Y Z : C)
  proof: by
  rw [← e_assoc V W X Y Z]; rw [Iso.hom_inv_id_assoc]

中文:
定理 e_assoc'
  条件: (W X Y Z : C)
  证明: by
  rw [← e_assoc V W X Y Z]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, e_assoc, hom_inv_id_assoc
-/
theorem e_assoc' (W X Y Z : C) :
    (α_ _ _ _).hom ≫ _ ◁ eComp V X Y Z ≫ eComp V W X Z =
      eComp V W X Y ▷ _ ≫ eComp V W Y Z := by
  rw [← e_assoc V W X Y Z]; rw [Iso.hom_inv_id_assoc]

section

variable {V} {W : Type v'} [Category.{w'} W] [MonoidalCategory W]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : LaxMonoidalFunctor V W` to each hom object.
-/
@[nolint unusedArguments]
/--
Definition of `TransportEnrichment` / `TransportEnrichment` 的定义

English:
definition TransportEnrichment
  signature: (F : V ⥤ W) [F.LaxMonoidal] (C : Type u₁)
  body: C

中文:
定义 TransportEnrichment
  签名: (F : V ⥤ W) [F.LaxMonoidal] (C : 类型u₁)
  定义体: C
-/
def TransportEnrichment (F : V ⥤ W) [F.LaxMonoidal] (C : Type u₁) :=
  C

variable (F : V ⥤ W) [F.LaxMonoidal]

open Functor.LaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedCategory W (TransportEnrichment F C)
  body: fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => ε F ≫ F.map (eId V X)
  comp := fun X Y Z : C => μ F _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    simp only [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.LaxMonoidal.left_unitality_inv_assoc]
  

中文:
实例 :
  签名: EnrichedCategory W (TransportEnrichment F C)
  定义体: fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => ε F ≫ F.map (eId V X)
  comp := fun X Y Z : C => μ F _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    simp only [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.LaxMonoidal.left_unitality_inv_assoc]
  

Depends on / 依赖: F.obj
-/
instance : EnrichedCategory W (TransportEnrichment F C) where
  Hom := fun X Y : C => F.obj (X ⟶[V] Y)
  id := fun X : C => ε F ≫ F.map (eId V X)
  comp := fun X Y Z : C => μ F _ _ ≫ F.map (eComp V X Y Z)
  id_comp X Y := by
    simp only [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.LaxMonoidal.left_unitality_inv_assoc]
    simp_rw [← F.map_comp]
    convert! F.map_id _
    simp
  comp_id X Y := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc,
      Functor.LaxMonoidal.right_unitality_inv_assoc]
    simp_rw [← F.map_comp]
    convert! F.map_id _
    simp
  assoc P Q R S := by
    rw [comp_whiskerRight]; rw [Category.assoc]; rw [μ_natural_left_assoc]; rw [← associativity_inv_assoc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [e_assoc]; rw [F.map_comp]; rw [MonoidalCategory.whiskerLeft_comp]; rw [Category.assoc]; rw [Functor.LaxMonoidal.μ_natural_right_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `TransportEnrichment.eId_eq` / 引理 `TransportEnrichment.eId_eq`

English:
lemma TransportEnrichment.eId_eq
  given: (X : TransportEnrichment F C)
  proof: rfl

中文:
引理 TransportEnrichment.eId_eq
  条件: (X : TransportEnrichment F C)
  证明: rfl
-/
lemma TransportEnrichment.eId_eq (X : TransportEnrichment F C) :
    eId W X = ε F ≫ F.map (eId (C := C) V X) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `TransportEnrichment.eComp_eq` / 引理 `TransportEnrichment.eComp_eq`

English:
lemma TransportEnrichment.eComp_eq
  given: (X Y Z : TransportEnrichment F C)
  proof: rfl

中文:
引理 TransportEnrichment.eComp_eq
  条件: (X Y Z : TransportEnrichment F C)
  证明: rfl
-/
lemma TransportEnrichment.eComp_eq (X Y Z : TransportEnrichment F C) :
    eComp W X Y Z = μ F _ _ ≫ F.map (eComp V _ _ _) :=
  rfl

end

/-- Construct an honest category from a `Type v`-enriched category.
-/
@[instance_reducible]
/--
Definition of `categoryOfEnrichedCategoryType` / `categoryOfEnrichedCategoryType` 的定义

English:
definition categoryOfEnrichedCategoryType
  signature: (C : Type u₁) [𝒞 : EnrichedCategory (Type v) C]
  body: 𝒞.Hom X Y
  id X := eId (Type v) X PUnit.unit
  comp f g := eComp (Type v) _ _ _ ⟨f, g⟩
  id_comp f := ConcreteCategory.congr_hom (e_id_comp (Type v) _ _) f
  comp_id f := ConcreteCategory.congr_hom (e_comp_id (Type v) _ _) f
  assoc f g h := ConcreteCategory.congr_hom (e_assoc (Type v) _ _ _ _) ⟨f,

中文:
定义 categoryOfEnrichedCategoryType
  签名: (C : 类型u₁) [𝒞 : EnrichedCategory (类型v) C]
  定义体: 𝒞.Hom X Y
  id X := eId (Type v) X PUnit.unit
  comp f g := eComp (Type v) _ _ _ ⟨f, g⟩
  id_comp f := ConcreteCategory.congr_hom (e_id_comp (Type v) _ _) f
  comp_id f := ConcreteCategory.congr_hom (e_comp_id (Type v) _ _) f
  assoc f g h := ConcreteCategory.congr_hom (e_assoc (Type v) _ _ _ _) ⟨f,
-/
def categoryOfEnrichedCategoryType (C : Type u₁) [𝒞 : EnrichedCategory (Type v) C] :
    Category.{v} C where
  Hom X Y := 𝒞.Hom X Y
  id X := eId (Type v) X PUnit.unit
  comp f g := eComp (Type v) _ _ _ ⟨f, g⟩
  id_comp f := ConcreteCategory.congr_hom (e_id_comp (Type v) _ _) f
  comp_id f := ConcreteCategory.congr_hom (e_comp_id (Type v) _ _) f
  assoc f g h := ConcreteCategory.congr_hom (e_assoc (Type v) _ _ _ _) ⟨f, g, h⟩

attribute [local simp] types_tensorObj_def in
/-- Construct a `Type v`-enriched category from an honest category.
-/
@[instance_reducible]
/--
Definition of `enrichedCategoryTypeOfCategory` / `enrichedCategoryTypeOfCategory` 的定义

English:
definition enrichedCategoryTypeOfCategory
  signature: (C : Type u₁) [𝒞 : Category.{v} C]
  body: 𝒞.Hom X Y
  id X := ↾fun _ => 𝟙 _
  comp _ _ _ := ↾fun p => p.1 ≫ p.2

中文:
定义 enrichedCategoryTypeOfCategory
  签名: (C : 类型u₁) [𝒞 : Category.{v} C]
  定义体: 𝒞.Hom X Y
  id X := ↾fun _ => 𝟙 _
  comp _ _ _ := ↾fun p => p.1 ≫ p.2
-/
def enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] :
    EnrichedCategory (Type v) C where
  Hom X Y := 𝒞.Hom X Y
  id X := ↾fun _ => 𝟙 _
  comp _ _ _ := ↾fun p => p.1 ≫ p.2

/-- We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
@[implicit_reducible]
/--
Definition of `enrichedCategoryTypeEquivCategory` / `enrichedCategoryTypeEquivCategory` 的定义

English:
definition enrichedCategoryTypeEquivCategory
  signature: (C : Type u₁)
  body: categoryOfEnrichedCategoryType C
  invFun _ := enrichedCategoryTypeOfCategory C

中文:
定义 enrichedCategoryTypeEquivCategory
  签名: (C : 类型u₁)
  定义体: categoryOfEnrichedCategoryType C
  invFun _ := enrichedCategoryTypeOfCategory C

Depends on / 依赖: categoryOfEnrichedCategoryType
-/
def enrichedCategoryTypeEquivCategory (C : Type u₁) :
    EnrichedCategory (Type v) C ≃ Category.{v} C where
  toFun _ := categoryOfEnrichedCategoryType C
  invFun _ := enrichedCategoryTypeOfCategory C

section

variable {W : Type v} [Category.{w} W] [MonoidalCategory W] [EnrichedCategory W C]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the (honest) category structure
so that `X ⟶ Y` is `(𝟙_ W) ⟶ (X ⟶[W] Y)`.

We obtain this category by
transporting the enrichment in `V` along the lax monoidal functor `coyonedaTensorUnit`,
then using the equivalence of `Type`-enriched categories with honest categories.

This is sometimes called the "underlying" category of an enriched category,
although some care is needed as the functor `coyonedaTensorUnit`,
which always exists, does not necessarily coincide with
"the forgetful functor" from `V` to `Type`, if such exists.
When `V` is any of `Type`, `Top`, `AddCommGroup`, or `Module R`,
`coyonedaTensorUnit` is just the usual forgetful functor, however.
For `V = Algebra R`, the usual forgetful functor is coyoneda of `R[X]`, not of `R`.
(Perhaps we should have a typeclass for this situation: `ConcreteMonoidal`?)
-/
@[nolint unusedArguments]
/--
Definition of `ForgetEnrichment` / `ForgetEnrichment` 的定义

English:
definition ForgetEnrichment
  signature: (W : Type v) [Category.{w} W] [MonoidalCategory W] (C : Type u₁)
  body: C

中文:
定义 ForgetEnrichment
  签名: (W : 类型v) [Category.{w} W] [MonoidalCategory W] (C : 类型u₁)
  定义体: C
-/
def ForgetEnrichment (W : Type v) [Category.{w} W] [MonoidalCategory W] (C : Type u₁)
    [EnrichedCategory W C] :=
  C

variable (W)

/-- Typecheck an object of `C` as an object of `ForgetEnrichment W C`. -/
@[implicit_reducible]
/--
Definition of `ForgetEnrichment.of` / `ForgetEnrichment.of` 的定义

English:
definition ForgetEnrichment.of
  signature: (X : C)
  body: X

中文:
定义 ForgetEnrichment.of
  签名: (X : C)
  定义体: X
-/
def ForgetEnrichment.of (X : C) : ForgetEnrichment W C :=
  X

/-- Typecheck an object of `ForgetEnrichment W C` as an object of `C`. -/
@[implicit_reducible]
/--
Definition of `ForgetEnrichment.to` / `ForgetEnrichment.to` 的定义

English:
definition ForgetEnrichment.to
  signature: (X : ForgetEnrichment W C)
  body: X

@[simp]

中文:
定义 ForgetEnrichment.to
  签名: (X : ForgetEnrichment W C)
  定义体: X

@[simp]

Depends on / 依赖: HasSplitCoequalizer, preservesSplitCoequalizers
-/
def ForgetEnrichment.to (X : ForgetEnrichment W C) : C :=
  X

@[simp]
/--
theorem `ForgetEnrichment.to_of` / 定理 `ForgetEnrichment.to_of`

English:
theorem ForgetEnrichment.to_of
  given: (X : C)
  statement: ForgetEnrichment.to W (ForgetEnrichment.of W X) = X
  proof: rfl

@[simp]

中文:
定理 ForgetEnrichment.to_of
  条件: (X : C)
  结论: ForgetEnrichment.to W (ForgetEnrichment.of W X) = X
  证明: rfl

@[simp]

Depends on / 依赖: HasSplitEqualizer, preservesSplitEqualizers
-/
theorem ForgetEnrichment.to_of (X : C) : ForgetEnrichment.to W (ForgetEnrichment.of W X) = X :=
  rfl

@[simp]
/--
theorem `ForgetEnrichment.of_to` / 定理 `ForgetEnrichment.of_to`

English:
theorem ForgetEnrichment.of_to
  given: (X : ForgetEnrichment W C)
  proof: rfl

中文:
定理 ForgetEnrichment.of_to
  条件: (X : ForgetEnrichment W C)
  证明: rfl
-/
theorem ForgetEnrichment.of_to (X : ForgetEnrichment W C) :
    ForgetEnrichment.of W (ForgetEnrichment.to W X) = X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `categoryForgetEnrichment` / 实例 `categoryForgetEnrichment`

English:
instance categoryForgetEnrichment
  signature: : Category (ForgetEnrichment W C)
  body: enrichedCategoryTypeEquivCategory C (inferInstanceAs (EnrichedCategory (Type w)
      (TransportEnrichment (coyoneda.obj (op (𝟙_ W))) C)))

中文:
实例 categoryForgetEnrichment
  签名: : Category (ForgetEnrichment W C)
  定义体: enrichedCategoryTypeEquivCategory C (inferInstanceAs (EnrichedCategory (Type w)
      (TransportEnrichment (coyoneda.obj (op (𝟙_ W))) C)))

Depends on / 依赖: EnrichedCategory, TransportEnrichment, coyoneda, coyoneda.obj, enrichedCategoryTypeEquivCategory
-/
instance categoryForgetEnrichment : Category (ForgetEnrichment W C) :=
  enrichedCategoryTypeEquivCategory C (inferInstanceAs (EnrichedCategory (Type w)
      (TransportEnrichment (coyoneda.obj (op (𝟙_ W))) C)))

/-- We verify that the morphism types in `ForgetEnrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
example (X Y : ForgetEnrichment W C) :
    (X ⟶ Y) = (𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y) :=
  rfl

/--
Definition of `ForgetEnrichment.homOf` / `ForgetEnrichment.homOf` 的定义

English:
definition ForgetEnrichment.homOf
  signature: {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y)
  body: f

中文:
定义 ForgetEnrichment.homOf
  签名: {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y)
  定义体: f
-/
def ForgetEnrichment.homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.of W X ⟶ ForgetEnrichment.of W Y :=
  f

/--
Definition of `ForgetEnrichment.homTo` / `ForgetEnrichment.homTo` 的定义

English:
definition ForgetEnrichment.homTo
  signature: {X Y : ForgetEnrichment W C} (f : X ⟶ Y)
  body: f

@[simp]

中文:
定义 ForgetEnrichment.homTo
  签名: {X Y : ForgetEnrichment W C} (f : X ⟶ Y)
  定义体: f

@[simp]
-/
def ForgetEnrichment.homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y :=
  f

@[simp]
/--
theorem `ForgetEnrichment.homTo_homOf` / 定理 `ForgetEnrichment.homTo_homOf`

English:
theorem ForgetEnrichment.homTo_homOf
  given: {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y)
  proof: rfl

@[simp]

中文:
定理 ForgetEnrichment.homTo_homOf
  条件: {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y)
  证明: rfl

@[simp]
-/
theorem ForgetEnrichment.homTo_homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.homTo W (ForgetEnrichment.homOf W f) = f :=
  rfl

@[simp]
/--
theorem `ForgetEnrichment.homOf_homTo` / 定理 `ForgetEnrichment.homOf_homTo`

English:
theorem ForgetEnrichment.homOf_homTo
  given: {X Y : ForgetEnrichment W C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 ForgetEnrichment.homOf_homTo
  条件: {X Y : ForgetEnrichment W C} (f : X ⟶ Y)
  证明: rfl
-/
theorem ForgetEnrichment.homOf_homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    ForgetEnrichment.homOf W (ForgetEnrichment.homTo W f) = f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The identity in the "underlying" category of an enriched category. -/
@[simp]
/--
theorem `ForgetEnrichment.homTo_id` / 定理 `ForgetEnrichment.homTo_id`

English:
theorem ForgetEnrichment.homTo_id
  given: (X : ForgetEnrichment W C)
  proof: Category.id_comp _

中文:
定理 ForgetEnrichment.homTo_id
  条件: (X : ForgetEnrichment W C)
  证明: Category.id_comp _

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
theorem ForgetEnrichment.homTo_id (X : ForgetEnrichment W C) :
    ForgetEnrichment.homTo W (𝟙 X) = eId W (ForgetEnrichment.to W X : C) :=
  Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `ForgetEnrichment.homOf_eId` / 定理 `ForgetEnrichment.homOf_eId`

English:
theorem ForgetEnrichment.homOf_eId
  given: (X : C)
  proof: (homTo_id W (ForgetEnrichment.of W X)).symm

中文:
定理 ForgetEnrichment.homOf_eId
  条件: (X : C)
  证明: (homTo_id W (ForgetEnrichment.of W X)).symm

Depends on / 依赖: ForgetEnrichment, ForgetEnrichment.of, homTo_id
-/
theorem ForgetEnrichment.homOf_eId (X : C) :
    ForgetEnrichment.homOf W (eId W X) = 𝟙 (of W X : C) :=
  (homTo_id W (ForgetEnrichment.of W X)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Composition in the "underlying" category of an enriched category. -/
@[simp]
/--
theorem `ForgetEnrichment.homTo_comp` / 定理 `ForgetEnrichment.homTo_comp`

English:
theorem ForgetEnrichment.homTo_comp
  given: {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 ForgetEnrichment.homTo_comp
  条件: {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem ForgetEnrichment.homTo_comp {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homTo W (f ≫ g) = ((fun_ (𝟙_ W)).inv ≫ (homTo W f otimesₘ homTo W g)) ≫ eComp W _ _ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `ForgetEnrichment.homOf_comp` / 定理 `ForgetEnrichment.homOf_comp`

English:
theorem ForgetEnrichment.homOf_comp
  given: {X Y Z : C} (f : 𝟙_ W ⟶ (X ⟶[W] Y)) (g : 𝟙_ W ⟶ (Y ⟶[W] Z))
  proof: by
  rw [← Category.assoc]
  rfl

中文:
定理 ForgetEnrichment.homOf_comp
  条件: {X Y Z : C} (f : 𝟙_ W ⟶ (X ⟶[W] Y)) (g : 𝟙_ W ⟶ (Y ⟶[W] Z))
  证明: by
  rw [← Category.assoc]
  rfl

Depends on / 依赖: Category, Category.assoc
-/
theorem ForgetEnrichment.homOf_comp {X Y Z : C} (f : 𝟙_ W ⟶ (X ⟶[W] Y)) (g : 𝟙_ W ⟶ (Y ⟶[W] Z)) :
    homOf W ((fun_ _).inv ≫ (f otimesₘ g) ≫ eComp W ..) = homOf W f ≫ homOf W g := by
  rw [← Category.assoc]
  rfl

end

/--
Definition of `EnrichedFunctor` / `EnrichedFunctor` 的定义

English:
structure EnrichedFunctor
  parameters: (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
  axioms and operations (4):
    - obj : C -> D
    - map : forall X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
    - map_id : forall X : C, eId V X ≫ map X X = eId V (obj X)  [default: by cat_disch]
    - map_comp : forall X Y Z : C, eComp V X Y Z ≫ map X Z = (map X Y otimesₘ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z)  [default: by cat_disch]

中文:
结构 EnrichedFunctor
  参数: (C : 类型u₁) [EnrichedCategory V C] (D : 类型u₂)
  公理与运算 (4 个):
    - obj : C -> D
    - map : 对任意 X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
    - map_id : 对任意 X : C, eId V X ≫ map X X = eId V (obj X)  [默认: by cat_disch]
    - map_comp : 对任意 X Y Z : C, eComp V X Y Z ≫ map X Z = (map X Y otimesₘ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, map_comp
-/
structure EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
    [EnrichedCategory V D] where
  /-- The application of this functor to an object -/
  obj : C -> D
  /-- The `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`, for all `X Y : C` -/
  map : forall X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
  map_id : forall X : C, eId V X ≫ map X X = eId V (obj X) := by cat_disch
  map_comp :
    forall X Y Z : C,
      eComp V X Y Z ≫ map X Z = (map X Y otimesₘ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z) := by
    cat_disch

attribute [reassoc (attr := simp)] EnrichedFunctor.map_id

attribute [reassoc (attr := simp)] EnrichedFunctor.map_comp

namespace EnrichedFunctor

/-- The identity enriched functor. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (C : Type u₁) [EnrichedCategory V C]
  body: X
  map _ _ := 𝟙 _

中文:
定义 id
  签名: (C : 类型u₁) [EnrichedCategory V C]
  定义体: X
  map _ _ := 𝟙 _
-/
def id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C where
  obj X := X
  map _ _ := 𝟙 _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (EnrichedFunctor V C C)
  body: ⟨EnrichedFunctor.id V C⟩

中文:
实例 :
  签名: Inhabited (EnrichedFunctor V C C)
  定义体: ⟨EnrichedFunctor.id V C⟩

Depends on / 依赖: EnrichedFunctor, EnrichedFunctor.id
-/
instance : Inhabited (EnrichedFunctor V C C) :=
  ⟨EnrichedFunctor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
  body: G.obj (F.obj X)
  map _ _ := F.map _ _ ≫ G.map _ _

中文:
定义 comp
  签名: {C : 类型u₁} {D : 类型u₂} {E : 类型u₃} [EnrichedCategory V C]
  定义体: G.obj (F.obj X)
  map _ _ := F.map _ _ ≫ G.map _ _

Depends on / 依赖: F.obj, G.obj
-/
def comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
    [EnrichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D)
    (G : EnrichedFunctor V D E) : EnrichedFunctor V C E where
  obj X := G.obj (F.obj X)
  map _ _ := F.map _ _ ≫ G.map _ _

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {C : Type u₁} {D : Type u₂} [EnrichedCategory V C]
  proof: by
  match F, G with
  | mk F_obj F_map _ _, mk G_obj G_map _ _ =>
    obtain rfl : F_obj = G_obj := funext fun X => h_obj X
    congr
    ext X Y
    simpa using h_map X Y

中文:
引理 ext
  结论: {C : 类型u₁} {D : 类型u₂} [EnrichedCategory V C]
  证明: by
  match F, G with
  | mk F_obj F_map _ _, mk G_obj G_map _ _ =>
    obtain rfl : F_obj = G_obj := funext fun X => h_obj X
    congr
    ext X Y
    simpa using h_map X Y

Depends on / 依赖: F_map, F_obj, G_map, G_obj, h_map, h_obj
-/
lemma ext {C : Type u₁} {D : Type u₂} [EnrichedCategory V C]
    [EnrichedCategory V D] {F G : EnrichedFunctor V C D} (h_obj : forall X, F.obj X = G.obj X)
    (h_map : forall (X Y : C), F.map X Y ≫ eqToHom (by rw [h_obj, h_obj]) = G.map X Y) : F = G := by
  match F, G with
  | mk F_obj F_map _ _, mk G_obj G_map _ _ =>
    obtain rfl : F_obj = G_obj := funext fun X => h_obj X
    congr
    ext X Y
    simpa using h_map X Y

section

variable {W : Type v'} [Category.{w'} W] [MonoidalCategory W]
  {C : Type u₁} [EnrichedCategory W C]
  {D : Type u₂} [EnrichedCategory W D]
  {E : Type u₃} [EnrichedCategory W E]

set_option backward.isDefEq.respectTransparency false in
/-- An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
-/
@[simps, implicit_reducible]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: (F : EnrichedFunctor W C D)
  body: ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W _) (ForgetEnrichment.to W _))
  map_comp f g := by
    apply_fun ForgetEnrichment.homTo W
    · simp only [Iso.cancel_iso_inv_left, Categor

中文:
定义 forget
  签名: (F : EnrichedFunctor W C D)
  定义体: ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W _) (ForgetEnrichment.to W _))
  map_comp f g := by
    apply_fun ForgetEnrichment.homTo W
    · simp only [Iso.cancel_iso_inv_left, Categor

Depends on / 依赖: F.obj, ForgetEnrichment, ForgetEnrichment.of, ForgetEnrichment.to
-/
def forget (F : EnrichedFunctor W C D) :
    ForgetEnrichment W C ⥤ ForgetEnrichment W D where
  obj X := ForgetEnrichment.of W (F.obj (ForgetEnrichment.to W X))
  map f :=
    ForgetEnrichment.homOf W
      (ForgetEnrichment.homTo W f ≫ F.map (ForgetEnrichment.to W _) (ForgetEnrichment.to W _))
  map_comp f g := by
    apply_fun ForgetEnrichment.homTo W
    · simp only [Iso.cancel_iso_inv_left, Category.assoc, ← tensorHom_comp_tensorHom,
        ForgetEnrichment.homTo_homOf, EnrichedFunctor.map_comp, ForgetEnrichment.homTo_comp]
      rfl
    · intro f g w; apply_fun ForgetEnrichment.homOf W at w; simpa using w

set_option backward.defeqAttrib.useBackward true in
/-- `EnrichedFunctor.forget` distributes over composition of enriched functors up to isomorphism. -/
@[simps!]
/--
Definition of `forgetComp` / `forgetComp` 的定义

English:
definition forgetComp
  signature: (F : EnrichedFunctor W C D) (G : EnrichedFunctor W D E)
  body: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [comp, forget])

中文:
定义 forgetComp
  签名: (F : EnrichedFunctor W C D) (G : EnrichedFunctor W D E)
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [comp, forget])

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, forget, ofComponents
-/
def forgetComp (F : EnrichedFunctor W C D) (G : EnrichedFunctor W D E) :
    (F.comp W G).forget ≅ F.forget ⋙ G.forget :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [comp, forget])

set_option backward.defeqAttrib.useBackward true in
variable (W) (C) in
/-- `EnrichedFunctor.forget` maps the identity enriched functor to a functor isomorphic to
`Functor.id`. -/
@[simps!]
/--
Definition of `forgetId` / `forgetId` 的定义

English:
definition forgetId
  signature: : (EnrichedFunctor.id W C).forget ≅ Functor.id _
  body: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [forget])

中文:
定义 forgetId
  签名: : (EnrichedFunctor.id W C).forget ≅ Functor.id _
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [forget])

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, forget, ofComponents
-/
def forgetId : (EnrichedFunctor.id W C).forget ≅ Functor.id _ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [forget])

end

end EnrichedFunctor

section

variable {V}
variable {D : Type u₂} [EnrichedCategory V D]

/-!
We now turn to natural transformations between `V`-functors.

The most commonly encountered definition of an enriched natural transformation
is a collection of morphisms
```
(𝟙_ W) ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying an appropriate analogue of the naturality square.
(c.f. https://ncatlab.org/nlab/show/enriched+natural+transformation)

This is the same thing as a natural transformation `F.forget ⟶ G.forget`.

We formalize this as `EnrichedNatTrans F G`, which is a `Type`.

However, there's also something much nicer: with appropriate additional hypotheses,
there is a `V`-object `EnrichedNatTransObj F G` which contains more information,
and from which one can recover `EnrichedNatTrans F G ≃ (𝟙_ V) ⟶ EnrichedNatTransObj F G`.

Using these as the hom-objects, we can build a `V`-enriched category
with objects the `V`-functors.

For `EnrichedNatTransObj` to exist, it suffices to have `V` braided and complete.

Before assuming `V` is complete, we assume it is braided and
define a presheaf `enrichedNatTransYoneda F G`
which is isomorphic to the Yoneda embedding of `EnrichedNatTransObj F G`
whether or not that object actually exists.

This presheaf has components `(enrichedNatTransYoneda F G).obj A`
what we call the `A`-graded enriched natural transformations,
which are collections of morphisms
```
A ⟶ (F.obj X ⟶[V] G.obj X)
```
satisfying a similar analogue of the naturality square,
this time incorporating a half-braiding on `A`.

(We actually define `EnrichedNatTrans F G`
as the special case `A := 𝟙_ V` with the trivial half-braiding,
and when defining `enrichedNatTransYoneda F G` we use the half-braidings
coming from the ambient braiding on `V`.)
-/


/-- The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural transformations.
-/
@[ext]
/--
Definition of `GradedNatTrans` / `GradedNatTrans` 的定义

English:
structure GradedNatTrans
  parameters: (A : Center V) (F G : EnrichedFunctor V C D)
  axioms and operations (2):
    - app : forall X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
    - naturality : forall X Y : C, (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y otimesₘ app Y) ≫ eComp V _ _ _ = (app X otimesₘ G.map X Y) ≫ eComp V _ _ _

中文:
结构 GradedNatTrans
  参数: (A : Center V) (F G : EnrichedFunctor V C D)
  公理与运算 (2 个):
    - app : 对任意 X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
    - naturality : 对任意 X Y : C, (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y otimesₘ app Y) ≫ eComp V _ _ _ = (app X otimesₘ G.map X Y) ≫ eComp V _ _ _
-/
structure GradedNatTrans (A : Center V) (F G : EnrichedFunctor V C D) where
  /-- The `A`-graded transformation from `F` to `G` -/
  app : forall X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
  /-- `app` is a natural transformation. -/
  naturality :
    forall X Y : C,
      (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y otimesₘ app Y) ≫ eComp V _ _ _ =
        (app X otimesₘ G.map X Y) ≫ eComp V _ _ _

attribute [reassoc] GradedNatTrans.naturality

/--
Definition of `EnrichedNatTrans` / `EnrichedNatTrans` 的定义

English:
structure EnrichedNatTrans
  parameters: (F G : EnrichedFunctor V C D)
  axioms and operations (1):
    - out : F.forget ⟶ G.forget

中文:
结构 EnrichedNatTrans
  参数: (F G : EnrichedFunctor V C D)
  公理与运算 (1 个):
    - out : F.forget ⟶ G.forget
-/
structure EnrichedNatTrans (F G : EnrichedFunctor V C D) where
  /-- The underlying natural transformation of an enriched transformation. -/
  out : F.forget ⟶ G.forget

namespace EnrichedFunctor

/-- Enriched functors form a category with the morphisms between functors `F` and `G` being
enriched natural transformations, i.e. natural transformations `F.forget ⟶ G.forget`. -/
@[simps]
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (EnrichedFunctor V C D) where
  body: EnrichedNatTrans F G
  id F := ⟨𝟙 _⟩
  comp F G := ⟨F.out ≫ G.out⟩

@[ext]

中文:
实例 category
  签名: : Category (EnrichedFunctor V C D) where
  定义体: EnrichedNatTrans F G
  id F := ⟨𝟙 _⟩
  comp F G := ⟨F.out ≫ G.out⟩

@[ext]

Depends on / 依赖: EnrichedNatTrans
-/
instance category : Category (EnrichedFunctor V C D) where
  Hom F G := EnrichedNatTrans F G
  id F := ⟨𝟙 _⟩
  comp F G := ⟨F.out ≫ G.out⟩

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {F G : EnrichedFunctor V C D} {α β : F ⟶ G}
  proof: by
  rcases α with ⟨α⟩
  rcases β with ⟨β⟩
  congr
  ext
  apply h

中文:
引理 hom_ext
  结论: {F G : EnrichedFunctor V C D} {α β : F ⟶ G}
  证明: by
  rcases α with ⟨α⟩
  rcases β with ⟨β⟩
  congr
  ext
  apply h
-/
lemma hom_ext {F G : EnrichedFunctor V C D} {α β : F ⟶ G}
    (h : forall X : C, α.out.app X = β.out.app X) : α = β := by
  rcases α with ⟨α⟩
  rcases β with ⟨β⟩
  congr
  ext
  apply h

/-- To construct an isomorphism between enriched functors `F` and `G`, it suffices to construct
a natural isomorphism between `F.forget` and `G.forget`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {F G : EnrichedFunctor V C D} (h : F.forget ≅ G.forget)
  body: ⟨h.hom⟩
  inv := ⟨h.inv⟩

中文:
定义 isoMk
  签名: {F G : EnrichedFunctor V C D} (h : F.forget ≅ G.forget)
  定义体: ⟨h.hom⟩
  inv := ⟨h.inv⟩

Depends on / 依赖: h.hom
-/
def isoMk {F G : EnrichedFunctor V C D} (h : F.forget ≅ G.forget) : F ≅ G where
  hom := ⟨h.hom⟩
  inv := ⟨h.inv⟩

end EnrichedFunctor

variable [BraidedCategory V]

open BraidedCategory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/
@[simps]
/--
Definition of `enrichedNatTransYoneda` / `enrichedNatTransYoneda` 的定义

English:
definition enrichedNatTransYoneda
  signature: (F G : EnrichedFunctor V C D)
  body: GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map f := ↾fun σ =>
    { app X := f.unop ≫ σ.app X
      naturality X Y := by
        have p := σ.naturality X Y
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _]; rw [id_tensor_comp]; rw [Category.assoc]; rw [C

中文:
定义 enrichedNatTransYoneda
  签名: (F G : EnrichedFunctor V C D)
  定义体: GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map f := ↾fun σ =>
    { app X := f.unop ≫ σ.app X
      naturality X Y := by
        have p := σ.naturality X Y
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _]; rw [id_tensor_comp]; rw [Category.assoc]; rw [C

Depends on / 依赖: Center, Center.ofBraided, GradedNatTrans, ofBraided
-/
def enrichedNatTransYoneda (F G : EnrichedFunctor V C D) : Vᵒᵖ ⥤ Type (max u₁ w) where
  obj A := GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map f := ↾fun σ =>
    { app X := f.unop ≫ σ.app X
      naturality X Y := by
        have p := σ.naturality X Y
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _]; rw [id_tensor_comp]; rw [Category.assoc]; rw [Category.assoc]; rw [← braiding_naturality_assoc]; rw [id_tensor_comp_tensor_id_assoc]; rw [p]; rw [tensorHom_comp_tensorHom_assoc]; rw [Category.id_comp] }

-- TODO assuming `[HasLimits C]` construct the actual object of natural transformations
-- and show that the functor category is `V`-enriched.
end

section

attribute [local instance] categoryOfEnrichedCategoryType

/-- We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
-/
@[simps]
/--
Definition of `enrichedFunctorTypeEquivFunctor` / `enrichedFunctorTypeEquivFunctor` 的定义

English:
definition enrichedFunctorTypeEquivFunctor
  signature: {C : Type u₁} [𝒞 : EnrichedCategory (Type v) C]
  body: { obj := fun X => F.obj X
      map := fun f => F.map _ _ f
      map_id := fun X => ConcreteCategory.congr_hom (F.map_id X) PUnit.unit
      map_comp := fun f g => ConcreteCategory.congr_hom (F.map_comp _ _ _) ⟨f, g⟩ }
  invFun F :=
    { obj := fun X => F.obj X
      map := fun _ _ => ↾fun f => F.

中文:
定义 enrichedFunctorTypeEquivFunctor
  签名: {C : 类型u₁} [𝒞 : EnrichedCategory (类型v) C]
  定义体: { obj := fun X => F.obj X
      map := fun f => F.map _ _ f
      map_id := fun X => ConcreteCategory.congr_hom (F.map_id X) PUnit.unit
      map_comp := fun f g => ConcreteCategory.congr_hom (F.map_comp _ _ _) ⟨f, g⟩ }
  invFun F :=
    { obj := fun X => F.obj X
      map := fun _ _ => ↾fun f => F.

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.map, F.map_comp, F.map_id, F.obj, PUnit.unit, congr_hom, invFun, map_comp, map_id
-/
def enrichedFunctorTypeEquivFunctor {C : Type u₁} [𝒞 : EnrichedCategory (Type v) C]
    {D : Type u₂} [𝒟 : EnrichedCategory (Type v) D] :
    EnrichedFunctor (Type v) C D ≃ C ⥤ D where
  toFun F :=
    { obj := fun X => F.obj X
      map := fun f => F.map _ _ f
      map_id := fun X => ConcreteCategory.congr_hom (F.map_id X) PUnit.unit
      map_comp := fun f g => ConcreteCategory.congr_hom (F.map_comp _ _ _) ⟨f, g⟩ }
  invFun F :=
    { obj := fun X => F.obj X
      map := fun _ _ => ↾fun f => F.map f
      map_id := fun X => by ext ⟨⟩; exact F.map_id X
      map_comp := fun X Y Z => by ext ⟨f, g⟩; exact F.map_comp f g }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `enrichedNatTransYonedaTypeIsoYonedaNatTrans` / `enrichedNatTransYonedaTypeIsoYonedaNatTrans` 的定义

English:
definition enrichedNatTransYonedaTypeIsoYonedaNatTrans
  signature: {C : Type v} [EnrichedCategory (Type v) C]
  body: NatIso.ofComponents
    (fun α =>
      { hom := ↾fun σ => ↾fun x =>
          { app X := σ.app X x
            naturality X Y f := ConcreteCategory.congr_hom (σ.naturality X Y) ⟨x, f⟩ }
        inv := ↾fun σ =>
          { app X := ↾fun x => (σ.hom x).app X
            naturality X Y := by ext ⟨x, 

中文:
定义 enrichedNatTransYonedaTypeIsoYonedaNatTrans
  签名: {C : 类型v} [EnrichedCategory (类型v) C]
  定义体: NatIso.ofComponents
    (fun α =>
      { hom := ↾fun σ => ↾fun x =>
          { app X := σ.app X x
            naturality X Y f := ConcreteCategory.congr_hom (σ.naturality X Y) ⟨x, f⟩ }
        inv := ↾fun σ =>
          { app X := ↾fun x => (σ.hom x).app X
            naturality X Y := by ext ⟨x, 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, NatIso, NatIso.ofComponents, cat_disch, congr_hom, naturality, ofComponents
-/
def enrichedNatTransYonedaTypeIsoYonedaNatTrans {C : Type v} [EnrichedCategory (Type v) C]
    {D : Type v} [EnrichedCategory (Type v) D] (F G : EnrichedFunctor (Type v) C D) :
    enrichedNatTransYoneda F G ≅
      yoneda.obj (enrichedFunctorTypeEquivFunctor F ⟶
        enrichedFunctorTypeEquivFunctor G) :=
  NatIso.ofComponents
    (fun α =>
      { hom := ↾fun σ => ↾fun x =>
          { app X := σ.app X x
            naturality X Y f := ConcreteCategory.congr_hom (σ.naturality X Y) ⟨x, f⟩ }
        inv := ↾fun σ =>
          { app X := ↾fun x => (σ.hom x).app X
            naturality X Y := by ext ⟨x, f⟩; exact (σ.hom x).naturality f } })
    (by cat_disch)

end

end CategoryTheory
