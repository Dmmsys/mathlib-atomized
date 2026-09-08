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

/-- A `V`-category is a category enriched in a monoidal category `V`.

Note that we do not assume that `V` is a concrete category,
so there may not be an "honest" underlying category at all!
-/
/-
**CategoryTheory.EnrichedCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：EnrichedCategory (C : Type u₁) where /-- `X ⟶[V] Y` is the `V` object of m
orphisms from `X` to `Y`. -/ Hom : C -> C -> V /-- The identity morphism of this
 category -/ id (X : C) : 𝟙_ V ⟶ Hom X X /-- Composition of two morphisms in thi
s category -/ comp (X Y Z : C) : Hom X Y otimes Hom Y Z ⟶ Hom X Z id_comp (X Y :
 C) : (fun_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _
参数：C : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `V`-category is a category enriched in a monoidal category `V`.

Note that we do not assume that `V` is a concrete category,
so there may not be an "honest" underlying category at all!
-/
class EnrichedCategory (C : Type u₁) where
  /-- `X ⟶[V] Y` is the `V` object of morphisms from `X` to `Y`. -/
  Hom : C → C → V
  /-- The identity morphism of this category -/
  id (X : C) : 𝟙_ V ⟶ Hom X X
  /-- Composition of two morphisms in this category -/
  comp (X Y Z : C) : Hom X Y ⊗ Hom Y Z ⟶ Hom X Z
  id_comp (X Y : C) : (λ_ (Hom X Y)).inv ≫ id X ▷ _ ≫ comp X X Y = 𝟙 _ := by cat_disch
  comp_id (X Y : C) : (ρ_ (Hom X Y)).inv ≫ _ ◁ id Y ≫ comp X Y Y = 𝟙 _ := by cat_disch
  assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ comp W X Y ▷ _ ≫ comp W Y Z =
    _ ◁ comp X Y Z ≫ comp W X Z := by cat_disch

@[inherit_doc EnrichedCategory.Hom] notation3 X " ⟶[" V "] " Y:10 => (EnrichedCategory.Hom X Y : V)

variable {C : Type u₁} [EnrichedCategory V C]

/-- The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched category.
-/
/-
**CategoryTheory.eId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `𝟙_ V`-shaped generalized element giving the identity in a `V`-enriched cate
gory.
-/
def eId (X : C) : 𝟙_ V ⟶ X ⟶[V] X :=
  EnrichedCategory.id X

/-- The composition `V`-morphism for a `V`-enriched category.
-/
/-
**CategoryTheory.eComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eComp (X Y Z : C) : ((X ⟶[V] Y) otimes Y ⟶[V] Z) ⟶ X ⟶[V] Z
参数：X Y Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition `V`-morphism for a `V`-enriched category.
-/
def eComp (X Y Z : C) : ((X ⟶[V] Y) ⊗ Y ⟶[V] Z) ⟶ X ⟶[V] Z :=
  EnrichedCategory.comp X Y Z

@[reassoc (attr := simp)]
/-
**CategoryTheory.e_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：e_id_comp (X Y : C) : (fun_ (X ⟶[V] Y)).inv ≫ eId V X ▷ _ ≫ eComp V X X Y 
= 𝟙 (X ⟶[V] Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnrichedCategory.id_comp`：∀ {V : Type v} {inst : Category
Theory.Category.{w, v} V} {inst_1 : CategoryTheory.MonoidalCategory V} {C : Type
 u₁}   [self : CategoryTheory…
-/
theorem e_id_comp (X Y : C) :
    (λ_ (X ⟶[V] Y)).inv ≫ eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.id_comp X Y

@[reassoc (attr := simp)]
/-
**CategoryTheory.e_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：e_comp_id (X Y : C) : (ρ_ (X ⟶[V] Y)).inv ≫ _ ◁ eId V Y ≫ eComp V X Y Y = 
𝟙 (X ⟶[V] Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnrichedCategory.comp_id`：∀ {V : Type v} {inst : Category
Theory.Category.{w, v} V} {inst_1 : CategoryTheory.MonoidalCategory V} {C : Type
 u₁}   [self : CategoryTheory…
-/
theorem e_comp_id (X Y : C) :
    (ρ_ (X ⟶[V] Y)).inv ≫ _ ◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y) :=
  EnrichedCategory.comp_id X Y

@[reassoc (attr := simp)]
/-
**CategoryTheory.e_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V W X Y ▷ _ ≫ eComp V W Y Z
 = _ ◁ eComp V X Y Z ≫ eComp V W X Z
参数：W X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnrichedCategory.assoc`：∀ {V : Type v} {inst : CategoryTh
eory.Category.{w, v} V} {inst_1 : CategoryTheory.MonoidalCategory V} {C : Type u
₁}   [self : CategoryTheory…
-/
theorem e_assoc (W X Y Z : C) :
    (α_ _ _ _).inv ≫ eComp V W X Y ▷ _ ≫ eComp V W Y Z =
      _ ◁ eComp V X Y Z ≫ eComp V W X Z :=
  EnrichedCategory.assoc W X Y Z

@[reassoc]
/-
**CategoryTheory.e_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：e_assoc' (W X Y Z : C) : (α_ _ _ _).hom ≫ _ ◁ eComp V X Y Z ≫ eComp V W X 
Z = eComp V W X Y ▷ _ ≫ eComp V W Y Z
参数：W X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.e_assoc`：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V
 W X Y ▷ _ ≫ eComp V W Y Z = _ ◁ eComp V X Y Z ≫ eComp V W X Z
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem e_assoc' (W X Y Z : C) :
    (α_ _ _ _).hom ≫ _ ◁ eComp V X Y Z ≫ eComp V W X Z =
      eComp V W X Y ▷ _ ≫ eComp V W Y Z := by
  rw [← e_assoc V W X Y Z, Iso.hom_inv_id_assoc]

section

variable {V} {W : Type v'} [Category.{w'} W] [MonoidalCategory W]

/-- A type synonym for `C`, which should come equipped with a `V`-enriched category structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : LaxMonoidalFunctor V W` to each hom object.
-/
@[nolint unusedArguments]
/-
**CategoryTheory.TransportEnrichment** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：TransportEnrichment (F : V ⥤ W) [F.LaxMonoidal] (C : Type u₁)
参数：F : V ⥤ W；C : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `C`, which should come equipped with a `V`-enriched category 
structure.
In a moment we will equip this with the `W`-enriched category structure
obtained by applying the functor `F : LaxMonoidalFunctor V W` to each hom object
.
-/
def TransportEnrichment (F : V ⥤ W) [F.LaxMonoidal] (C : Type u₁) :=
  C

variable (F : V ⥤ W) [F.LaxMonoidal]

open Functor.LaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      ← associativity_inv_assoc, ← F.map_comp, ← F.map_comp, e_assoc,
      F.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TransportEnrichment.eId_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.TransportEnrichment`。
形式化陈述：∀ {V : Type v} [inst : CategoryTheory.Category.{w, v} V] [inst_1 : Categor
yTheory.MonoidalCategory V] {C : Type u₁}   [inst_2 : CategoryTheory.EnrichedCat
egory V C] {W : Type v'} [inst_3 : CategoryTheory.Category.{w', v'} W]   [inst_4
 : CategoryTheory.MonoidalCategory W] (F : CategoryTheory.Functor V W) [inst_5 :
 F.LaxMonoidal]   (X : CategoryTheory.TransportEnrichment F C),   CategoryTheory
.eId W X =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Functor.LaxMon
oidal.ε F) (F.map (CategoryTheory.eId V X))
参数：F : CategoryTheory.Functor V W；X : CategoryTheory.TransportEnrichment F C；Cat
egoryTheory.Functor.LaxMonoidal.ε F；F.map (CategoryTheory.eId V X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma TransportEnrichment.eId_eq (X : TransportEnrichment F C) :
    eId W X = ε F ≫ F.map (eId (C := C) V X) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TransportEnrichment.eComp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.TransportEnrichment`。
形式化陈述：∀ {V : Type v} [inst : CategoryTheory.Category.{w, v} V] [inst_1 : Categor
yTheory.MonoidalCategory V] {C : Type u₁}   [inst_2 : CategoryTheory.EnrichedCat
egory V C] {W : Type v'} [inst_3 : CategoryTheory.Category.{w', v'} W]   [inst_4
 : CategoryTheory.MonoidalCategory W] (F : CategoryTheory.Functor V W) [inst_5 :
 F.LaxMonoidal]   (X Y Z : CategoryTheory.TransportEnrichment F C),   CategoryTh
eory.eComp W X Y Z =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Func
tor.LaxMonoidal.μ F (X ⟶[V] Y) (Y ⟶[V] Z))       (F.map (CategoryTheory.eComp V 
X Y Z))
参数：F : CategoryTheory.Functor V W；X Y Z : CategoryTheory.TransportEnrichment F C
；CategoryTheory.Functor.LaxMonoidal.μ F (X ⟶[V] Y) (Y ⟶[V] Z)；F.map (CategoryThe
ory.eComp V X Y Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma TransportEnrichment.eComp_eq (X Y Z : TransportEnrichment F C) :
    eComp W X Y Z = μ F _ _ ≫ F.map (eComp V _ _ _) :=
  rfl

end

/-- Construct an honest category from a `Type v`-enriched category.
-/
@[instance_reducible]
/-
**CategoryTheory.categoryOfEnrichedCategoryType** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：categoryOfEnrichedCategoryType (C : Type u₁) [𝒞 : EnrichedCategory (Type v
) C] : Category.{v} C where Hom X Y
参数：C : Type u₁；Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an honest category from a `Type v`-enriched category.
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
/-
**CategoryTheory.enrichedCategoryTypeOfCategory** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] : Enrich
edCategory (Type v) C where Hom X Y
参数：C : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `Type v`-enriched category from an honest category.
-/
def enrichedCategoryTypeOfCategory (C : Type u₁) [𝒞 : Category.{v} C] :
    EnrichedCategory (Type v) C where
  Hom X Y := 𝒞.Hom X Y
  id X := ↾fun _ ↦ 𝟙 _
  comp _ _ _ := ↾fun p ↦ p.1 ≫ p.2

/-- We verify that an enriched category in `Type u` is just the same thing as an honest category.
-/
@[implicit_reducible]
/-
**CategoryTheory.enrichedCategoryTypeEquivCategory** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：enrichedCategoryTypeEquivCategory (C : Type u₁) : EnrichedCategory (Type v
) C ≃ Category.{v} C where toFun _
参数：C : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We verify that an enriched category in `Type u` is just the same thing as an hon
est category.
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
/-
**CategoryTheory.ForgetEnrichment** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ForgetEnrichment (W : Type v) [Category.{w} W] [MonoidalCategory W] (C : T
ype u₁) [EnrichedCategory W C]
参数：W : Type v；C : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `C`, which should come equipped with a `V`-enriched category 
structure.
In a moment we will equip this with the (honest) category structure
so that `X ⟶ Y` is `(𝟙_ W) ⟶ (X ⟶[W] Y)`.

We obtain this category by
transporting the enrichment in `V` along the lax monoidal functor `coyonedaTenso
rUnit`,
then using the equivalence of `Type`-enriched categories with honest categories.

This is sometimes called the "underlying" category of an enriched category,
although some care is needed as the functor `coyonedaTensorUnit`,
which always exists, does not necessarily coincide with
"the forgetful functor" from `V` to `Type`, if such exists.
When `V` is any of `Type`, `Top`, `AddCommGroup`, or `Module R`,
`coyonedaTensorUnit` is just the usual forgetful functor, however.
For `V = Algebra R`, the usual forgetful functor is coyoneda of `R[X]`, not of `
R`.
(Perhaps we should have a typeclass for this situation: `ConcreteMonoidal`?)
-/
def ForgetEnrichment (W : Type v) [Category.{w} W] [MonoidalCategory W] (C : Type u₁)
    [EnrichedCategory W C] :=
  C

variable (W)

/-- Typecheck an object of `C` as an object of `ForgetEnrichment W C`. -/
@[implicit_reducible]
/-
**CategoryTheory.ForgetEnrichment.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
orgetEnrichment`。
形式化陈述：{C : Type u₁} →   (W : Type v) →     [inst : CategoryTheory.Category.{w, v
} W] →       [inst_1 : CategoryTheory.MonoidalCategory W] →         [inst_2 : Ca
tegoryTheory.EnrichedCategory W C] → C → CategoryTheory.ForgetEnrichment W C
参数：W : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck an object of `C` as an object of `ForgetEnrichment W C`.
-/
def ForgetEnrichment.of (X : C) : ForgetEnrichment W C :=
  X

/-- Typecheck an object of `ForgetEnrichment W C` as an object of `C`. -/
@[implicit_reducible]
/-
**CategoryTheory.ForgetEnrichment.to** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
orgetEnrichment`。
形式化陈述：{C : Type u₁} →   (W : Type v) →     [inst : CategoryTheory.Category.{w, v
} W] →       [inst_1 : CategoryTheory.MonoidalCategory W] →         [inst_2 : Ca
tegoryTheory.EnrichedCategory W C] → CategoryTheory.ForgetEnrichment W C → C
参数：W : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck an object of `ForgetEnrichment W C` as an object of `C`.
-/
def ForgetEnrichment.to (X : ForgetEnrichment W C) : C :=
  X

@[simp]
/-
**CategoryTheory.ForgetEnrichment.to_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] (X : C),   CategoryTheory.ForgetEnrichment.to W (CategoryTheory.Forge
tEnrichment.of W X) = X
参数：W : Type v；X : C；CategoryTheory.ForgetEnrichment.of W X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ForgetEnrichment.to_of (X : C) : ForgetEnrichment.to W (ForgetEnrichment.of W X) = X :=
  rfl

@[simp]
/-
**CategoryTheory.ForgetEnrichment.of_to** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] (X : CategoryTheory.ForgetEnrichment W C),   CategoryTheory.ForgetEnr
ichment.of W (CategoryTheory.ForgetEnrichment.to W X) = X
参数：W : Type v；X : CategoryTheory.ForgetEnrichment W C；CategoryTheory.ForgetEnric
hment.to W X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ForgetEnrichment.of_to (X : ForgetEnrichment W C) :
    ForgetEnrichment.of W (ForgetEnrichment.to W X) = X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.categoryForgetEnrichment** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory`。
形式化陈述：categoryForgetEnrichment : Category (ForgetEnrichment W C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryForgetEnrichment : Category (ForgetEnrichment W C) :=
  enrichedCategoryTypeEquivCategory C (inferInstanceAs (EnrichedCategory (Type w)
      (TransportEnrichment (coyoneda.obj (op (𝟙_ W))) C)))

/-- We verify that the morphism types in `ForgetEnrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W] Y)`.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We verify that the morphism types in `ForgetEnrichment W C` are `(𝟙_ W) ⟶ (X ⟶[W
] Y)`.
-/
example (X Y : ForgetEnrichment W C) :
    (X ⟶ Y) = (𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y) :=
  rfl

/-- Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `ForgetEnrichment W C`. -/
/-
**CategoryTheory.ForgetEnrichment.homOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ForgetEnrichment`。
形式化陈述：{C : Type u₁} →   (W : Type v) →     [inst : CategoryTheory.Category.{w, v
} W] →       [inst_1 : CategoryTheory.MonoidalCategory W] →         [inst_2 : Ca
tegoryTheory.EnrichedCategory W C] →           {X Y : C} →             (Category
Theory.MonoidalCategoryStruct.tensorUnit W ⟶ X ⟶[W] Y) →               (Category
Theory.ForgetEnrichment.of W X ⟶ CategoryTheory.ForgetEnrichment.of W Y)
参数：W : Type v；CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶ X ⟶[W] Y；Cate
goryTheory.ForgetEnrichment.of W X ⟶ CategoryTheory.ForgetEnrichment.of W Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `(𝟙_ W)`-shaped `W`-morphism as a morphism in `ForgetEnrichment W C`
.
-/
def ForgetEnrichment.homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.of W X ⟶ ForgetEnrichment.of W Y :=
  f

/-- Typecheck a morphism in `ForgetEnrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism. -/
/-
**CategoryTheory.ForgetEnrichment.homTo** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ForgetEnrichment`。
形式化陈述：{C : Type u₁} →   (W : Type v) →     [inst : CategoryTheory.Category.{w, v
} W] →       [inst_1 : CategoryTheory.MonoidalCategory W] →         [inst_2 : Ca
tegoryTheory.EnrichedCategory W C] →           {X Y : CategoryTheory.ForgetEnric
hment W C} →             (X ⟶ Y) →               (CategoryTheory.MonoidalCategor
yStruct.tensorUnit W ⟶                 CategoryTheory.ForgetEnrichment.to W X ⟶[
W] CategoryTheory.ForgetEnrichment.to W Y)
参数：W : Type v；X ⟶ Y；CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶        
         CategoryTheory.ForgetEnrichment.to W X ⟶[W] CategoryTheory.ForgetEnrich
ment.to W Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a morphism in `ForgetEnrichment W C` as a `(𝟙_ W)`-shaped `W`-morphism
.
-/
def ForgetEnrichment.homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    𝟙_ W ⟶ ForgetEnrichment.to W X ⟶[W] ForgetEnrichment.to W Y :=
  f

@[simp]
/-
**CategoryTheory.ForgetEnrichment.homTo_homOf** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] {X Y : C}   (f : CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶
 X ⟶[W] Y),   CategoryTheory.ForgetEnrichment.homTo W (CategoryTheory.ForgetEnri
chment.homOf W f) = f
参数：W : Type v；f : CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶ X ⟶[W] Y；
CategoryTheory.ForgetEnrichment.homOf W f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ForgetEnrichment.homTo_homOf {X Y : C} (f : 𝟙_ W ⟶ X ⟶[W] Y) :
    ForgetEnrichment.homTo W (ForgetEnrichment.homOf W f) = f :=
  rfl

@[simp]
/-
**CategoryTheory.ForgetEnrichment.homOf_homTo** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] {X Y : CategoryTheory.ForgetEnrichment W C} (f : X ⟶ Y),   CategoryTh
eory.ForgetEnrichment.homOf W (CategoryTheory.ForgetEnrichment.homTo W f) = f
参数：W : Type v；f : X ⟶ Y；CategoryTheory.ForgetEnrichment.homTo W f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ForgetEnrichment.homOf_homTo {X Y : ForgetEnrichment W C} (f : X ⟶ Y) :
    ForgetEnrichment.homOf W (ForgetEnrichment.homTo W f) = f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The identity in the "underlying" category of an enriched category. -/
@[simp]
/-
**CategoryTheory.ForgetEnrichment.homTo_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] (X : CategoryTheory.ForgetEnrichment W C),   CategoryTheory.ForgetEnr
ichment.homTo W (CategoryTheory.CategoryStruct.id X) =     CategoryTheory.eId W 
(CategoryTheory.ForgetEnrichment.to W X)
参数：W : Type v；X : CategoryTheory.ForgetEnrichment W C；CategoryTheory.CategoryStr
uct.id X；CategoryTheory.ForgetEnrichment.to W X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
The identity in the "underlying" category of an enriched category.
-/
theorem ForgetEnrichment.homTo_id (X : ForgetEnrichment W C) :
    ForgetEnrichment.homTo W (𝟙 X) = eId W (ForgetEnrichment.to W X : C) :=
  Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.ForgetEnrichment.homOf_eId** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] (X : C),   CategoryTheory.ForgetEnrichment.homOf W (CategoryTheory.eI
d W X) =     CategoryTheory.CategoryStruct.id (CategoryTheory.ForgetEnrichment.o
f W X)
参数：W : Type v；X : C；CategoryTheory.eId W X；CategoryTheory.ForgetEnrichment.of W 
X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ForgetEnrichment.homTo_id`：∀ {C : Type u₁} (W : Type v) [
inst : CategoryTheory.Category.{w, v} W] [inst_1 : CategoryTheory.MonoidalCatego
ry W]   [inst_2 : CategoryTheo…
-/
theorem ForgetEnrichment.homOf_eId (X : C) :
    ForgetEnrichment.homOf W (eId W X) = 𝟙 (of W X : C) :=
  (homTo_id W (ForgetEnrichment.of W X)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Composition in the "underlying" category of an enriched category. -/
@[simp]
/-
**CategoryTheory.ForgetEnrichment.homTo_comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] {X Y Z : CategoryTheory.ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z)
,   CategoryTheory.ForgetEnrichment.homTo W (CategoryTheory.CategoryStruct.comp 
f g) =     CategoryTheory.CategoryStruct.comp       (CategoryTheory.CategoryStru
ct.comp         (CategoryTheory.MonoidalCategoryStruct.leftUnitor (CategoryTheor
y.MonoidalCategoryStruct.tensorUnit W)).inv         (CategoryTheory.MonoidalCate
goryStruct.tensorHom (CategoryTheory.ForgetEnrichment.homTo W f)           (Cate
goryTheory.ForgetEnrichment.homTo W g)))       (CategoryTheory.eComp W (Category
Theory.ForgetEnrichment.to W X) (CategoryTheory.ForgetEnrichment.to W Y)        
 (CategoryTheory.ForgetEnrichment.to W Z))
参数：W : Type v；f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；Categor
yTheory.CategoryStruct.comp         (CategoryTheory.MonoidalCategoryStruct.leftU
nitor (CategoryTheory.MonoidalCategoryStruct.tensorUnit W)).inv         (Categor
yTheory.MonoidalCategoryStruct.tensorHom (CategoryTheory.ForgetEnrichment.homTo 
W f)           (CategoryTheory.ForgetEnrichment.homTo W g))；CategoryTheory.eComp
 W (CategoryTheory.ForgetEnrichment.to W X) (CategoryTheory.ForgetEnrichment.to 
W Y)         (CategoryTheory.ForgetEnrichment.to W Z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition in the "underlying" category of an enriched category.
-/
theorem ForgetEnrichment.homTo_comp {X Y Z : ForgetEnrichment W C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homTo W (f ≫ g) = ((λ_ (𝟙_ W)).inv ≫ (homTo W f ⊗ₘ homTo W g)) ≫ eComp W _ _ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.ForgetEnrichment.homOf_comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ForgetEnrichment`。
形式化陈述：∀ {C : Type u₁} (W : Type v) [inst : CategoryTheory.Category.{w, v} W] [in
st_1 : CategoryTheory.MonoidalCategory W]   [inst_2 : CategoryTheory.EnrichedCat
egory W C] {X Y Z : C}   (f : CategoryTheory.MonoidalCategoryStruct.tensorUnit W
 ⟶ X ⟶[W] Y)   (g : CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶ Y ⟶[W] 
Z),   CategoryTheory.ForgetEnrichment.homOf W       (CategoryTheory.CategoryStru
ct.comp         (CategoryTheory.MonoidalCategoryStruct.leftUnitor (CategoryTheor
y.MonoidalCategoryStruct.tensorUnit W)).inv         (CategoryTheory.CategoryStru
ct.comp (CategoryTheory.MonoidalCategoryStruct.tensorHom f g)           (Categor
yTheory.eComp W X Y Z))) =     CategoryTheory.CategoryStruct.comp (CategoryTheor
y.ForgetEnrichment.homOf W f)       (CategoryTheory.ForgetEnrichment.homOf W g)
参数：W : Type v；f : CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶ X ⟶[W] Y；
g : CategoryTheory.MonoidalCategoryStruct.tensorUnit W ⟶ Y ⟶[W] Z；CategoryTheory
.CategoryStruct.comp         (CategoryTheory.MonoidalCategoryStruct.leftUnitor (
CategoryTheory.MonoidalCategoryStruct.tensorUnit W)).inv         (CategoryTheory
.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.tensorHom f g)      
     (CategoryTheory.eComp W X Y Z))；CategoryTheory.ForgetEnrichment.homOf W f；C
ategoryTheory.ForgetEnrichment.homOf W g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem ForgetEnrichment.homOf_comp {X Y Z : C} (f : 𝟙_ W ⟶ (X ⟶[W] Y)) (g : 𝟙_ W ⟶ (Y ⟶[W] Z)) :
    homOf W ((λ_ _).inv ≫ (f ⊗ₘ g) ≫ eComp W ..) = homOf W f ≫ homOf W g := by
  rw [← Category.assoc]
  rfl

end

/-- A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
/-
**CategoryTheory.EnrichedFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂) [Enrich
edCategory V D] where /-- The application of this functor to an object -/ obj : 
C -> D /-- The `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`, for all `
X Y : C` -/ map : forall X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y map_id : forall 
X : C, eId V X ≫ map X X = eId V (obj X)
参数：C : Type u₁；D : Type u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `V`-functor `F` between `V`-enriched categories
has a `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`,
satisfying the usual axioms.
-/
structure EnrichedFunctor (C : Type u₁) [EnrichedCategory V C] (D : Type u₂)
    [EnrichedCategory V D] where
  /-- The application of this functor to an object -/
  obj : C → D
  /-- The `V`-morphism from `X ⟶[V] Y` to `F.obj X ⟶[V] F.obj Y`, for all `X Y : C` -/
  map : ∀ X Y : C, (X ⟶[V] Y) ⟶ obj X ⟶[V] obj Y
  map_id : ∀ X : C, eId V X ≫ map X X = eId V (obj X) := by cat_disch
  map_comp :
    ∀ X Y Z : C,
      eComp V X Y Z ≫ map X Z = (map X Y ⊗ₘ map Y Z) ≫ eComp V (obj X) (obj Y) (obj Z) := by
    cat_disch

attribute [reassoc (attr := simp)] EnrichedFunctor.map_id

attribute [reassoc (attr := simp)] EnrichedFunctor.map_comp

namespace EnrichedFunctor

/-- The identity enriched functor. -/
@[simps]
/-
**CategoryTheory.EnrichedFunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.En
richedFunctor`。
形式化陈述：id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C where obj 
X
参数：C : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity enriched functor.
-/
def id (C : Type u₁) [EnrichedCategory V C] : EnrichedFunctor V C C where
  obj X := X
  map _ _ := 𝟙 _
/-
**CategoryTheory.EnrichedFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Enri
chedFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (EnrichedFunctor V C C) :=
  ⟨EnrichedFunctor.id V C⟩

/-- Composition of enriched functors. -/
@[simps]
/-
**CategoryTheory.EnrichedFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
EnrichedFunctor`。
形式化陈述：comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C] [Enr
ichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D) (G : Enric
hedFunctor V D E) : EnrichedFunctor V C E where obj X
参数：F : EnrichedFunctor V C D；G : EnrichedFunctor V D E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of enriched functors.
-/
def comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
    [EnrichedCategory V D] [EnrichedCategory V E] (F : EnrichedFunctor V C D)
    (G : EnrichedFunctor V D E) : EnrichedFunctor V C E where
  obj X := G.obj (F.obj X)
  map _ _ := F.map _ _ ≫ G.map _ _
/-
**CategoryTheory.EnrichedFunctor.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.E
nrichedFunctor`。
形式化陈述：ext {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V
 D] {F G : EnrichedFunctor V C D} (h_obj : forall X, F.obj X = G.obj X) (h_map :
 forall (X Y : C), F.map X Y ≫ eqToHom (by rw [h_obj, h_obj]) = G.map X Y) : F =
 G
参数：h_obj : forall X, F.obj X = G.obj X；h_map : forall (X Y : C), F.map X Y ≫ eqT
oHom (by rw [h_obj, h_obj]) = G.map X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ext {C : Type u₁} {D : Type u₂} [EnrichedCategory V C]
    [EnrichedCategory V D] {F G : EnrichedFunctor V C D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : C), F.map X Y ≫ eqToHom (by rw [h_obj, h_obj]) = G.map X Y) : F = G := by
  match F, G with
  | mk F_obj F_map _ _, mk G_obj G_map _ _ =>
    obtain rfl : F_obj = G_obj := funext fun X ↦ h_obj X
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
/-
**CategoryTheory.EnrichedFunctor.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.EnrichedFunctor`。
形式化陈述：forget (F : EnrichedFunctor W C D) : ForgetEnrichment W C ⥤ ForgetEnrichme
nt W D where obj X
参数：F : EnrichedFunctor W C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An enriched functor induces an honest functor of the underlying categories,
by mapping the `(𝟙_ W)`-shaped morphisms.
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
/-
**CategoryTheory.EnrichedFunctor.forgetComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.EnrichedFunctor`。
形式化陈述：forgetComp (F : EnrichedFunctor W C D) (G : EnrichedFunctor W D E) : (F.co
mp W G).forget ≅ F.forget ⋙ G.forget
参数：F : EnrichedFunctor W C D；G : EnrichedFunctor W D E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EnrichedFunctor.forget` distributes over composition of enriched functors up to
 isomorphism.
-/
def forgetComp (F : EnrichedFunctor W C D) (G : EnrichedFunctor W D E) :
    (F.comp W G).forget ≅ F.forget ⋙ G.forget :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [comp, forget])

set_option backward.defeqAttrib.useBackward true in
variable (W) (C) in
/-- `EnrichedFunctor.forget` maps the identity enriched functor to a functor isomorphic to
`Functor.id`. -/
@[simps!]
/-
**CategoryTheory.EnrichedFunctor.forgetId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.EnrichedFunctor`。
形式化陈述：forgetId : (EnrichedFunctor.id W C).forget ≅ Functor.id _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EnrichedFunctor.forget` maps the identity enriched functor to a functor isomorp
hic to
`Functor.id`.
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
/-
**CategoryTheory.GradedNatTrans** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{V : Type v} →   [inst : CategoryTheory.Category.{w, v} V] →     [inst_1 :
 CategoryTheory.MonoidalCategory V] →       {C : Type u₁} →         [inst_2 : Ca
tegoryTheory.EnrichedCategory V C] →           {D : Type u₂} →             [inst
_3 : CategoryTheory.EnrichedCategory V D] →               CategoryTheory.Center 
V →                 CategoryTheory.EnrichedFunctor V C D → CategoryTheory.Enrich
edFunctor V C D → Type (max u₁ w)
参数：max u₁ w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `A`-graded natural transformations between `V`-functors `F` and `G`.
This is the type of morphisms in `V` from `A` to the `V`-object of natural trans
formations.
-/
structure GradedNatTrans (A : Center V) (F G : EnrichedFunctor V C D) where
  /-- The `A`-graded transformation from `F` to `G` -/
  app : ∀ X : C, A.1 ⟶ F.obj X ⟶[V] G.obj X
  /-- `app` is a natural transformation. -/
  naturality :
    ∀ X Y : C,
      (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ app Y) ≫ eComp V _ _ _ =
        (app X ⊗ₘ G.map X Y) ≫ eComp V _ _ _

attribute [reassoc] GradedNatTrans.naturality

/-- A natural transformation between two enriched functors is a `𝟙_ V`-graded natural
transformation. -/
/-
**CategoryTheory.EnrichedNatTrans** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{V : Type v} →   [inst : CategoryTheory.Category.{w, v} V] →     [inst_1 :
 CategoryTheory.MonoidalCategory V] →       {C : Type u₁} →         [inst_2 : Ca
tegoryTheory.EnrichedCategory V C] →           {D : Type u₂} →             [inst
_3 : CategoryTheory.EnrichedCategory V D] →               CategoryTheory.Enriche
dFunctor V C D → CategoryTheory.EnrichedFunctor V C D → Type (max u₁ w)
参数：max u₁ w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation between two enriched functors is a `𝟙_ V`-graded natura
l
transformation.
-/
structure EnrichedNatTrans (F G : EnrichedFunctor V C D) where
  /-- The underlying natural transformation of an enriched transformation. -/
  out : F.forget ⟶ G.forget

namespace EnrichedFunctor

/-- Enriched functors form a category with the morphisms between functors `F` and `G` being
enriched natural transformations, i.e. natural transformations `F.forget ⟶ G.forget`. -/
@[simps]
/-
**CategoryTheory.EnrichedFunctor.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.EnrichedFunctor`。
形式化陈述：category : Category (EnrichedFunctor V C D) where Hom F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enriched functors form a category with the morphisms between functors `F` and `G
` being
enriched natural transformations, i.e. natural transformations `F.forget ⟶ G.for
get`.
-/
instance category : Category (EnrichedFunctor V C D) where
  Hom F G := EnrichedNatTrans F G
  id F := ⟨𝟙 _⟩
  comp F G := ⟨F.out ≫ G.out⟩

@[ext]
/-
**CategoryTheory.EnrichedFunctor.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.EnrichedFunctor`。
形式化陈述：hom_ext {F G : EnrichedFunctor V C D} {α β : F ⟶ G} (h : forall X : C, α.o
ut.app X = β.out.app X) : α = β
参数：h : forall X : C, α.out.app X = β.out.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {F G : EnrichedFunctor V C D} {α β : F ⟶ G}
    (h : ∀ X : C, α.out.app X = β.out.app X) : α = β := by
  rcases α with ⟨α⟩
  rcases β with ⟨β⟩
  congr
  ext
  apply h

/-- To construct an isomorphism between enriched functors `F` and `G`, it suffices to construct
a natural isomorphism between `F.forget` and `G.forget`. -/
@[simps]
/-
**CategoryTheory.EnrichedFunctor.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.EnrichedFunctor`。
形式化陈述：isoMk {F G : EnrichedFunctor V C D} (h : F.forget ≅ G.forget) : F ≅ G wher
e hom
参数：h : F.forget ≅ G.forget。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism between enriched functors `F` and `G`, it suffices t
o construct
a natural isomorphism between `F.forget` and `G.forget`.
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
/-
**CategoryTheory.enrichedNatTransYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：enrichedNatTransYoneda (F G : EnrichedFunctor V C D) : Vᵒᵖ ⥤ Type (max u₁ 
w) where obj A
参数：F G : EnrichedFunctor V C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf isomorphic to the Yoneda embedding of
the `V`-object of natural transformations from `F` to `G`.
-/
def enrichedNatTransYoneda (F G : EnrichedFunctor V C D) : Vᵒᵖ ⥤ Type (max u₁ w) where
  obj A := GradedNatTrans ((Center.ofBraided V).obj (unop A)) F G
  map f := ↾fun σ ↦
    { app X := f.unop ≫ σ.app X
      naturality X Y := by
        have p := σ.naturality X Y
        dsimp at p ⊢
        rw [← id_tensor_comp_tensor_id (f.unop ≫ σ.app Y) _, id_tensor_comp, Category.assoc,
          Category.assoc, ← braiding_naturality_assoc, id_tensor_comp_tensor_id_assoc, p,
          tensorHom_comp_tensorHom_assoc, Category.id_comp] }

-- TODO assuming `[HasLimits C]` construct the actual object of natural transformations
-- and show that the functor category is `V`-enriched.
end

section

attribute [local instance] categoryOfEnrichedCategoryType

/-- We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
-/
@[simps]
/-
**CategoryTheory.enrichedFunctorTypeEquivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：enrichedFunctorTypeEquivFunctor {C : Type u₁} [𝒞 : EnrichedCategory (Type 
v) C] {D : Type u₂} [𝒟 : EnrichedCategory (Type v) D] : EnrichedFunctor (Type v)
 C D ≃ C ⥤ D where toFun F
参数：Type v；Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We verify that an enriched functor between `Type v` enriched categories
is just the same thing as an honest functor.
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
/-- We verify that the presheaf representing natural transformations
between `Type v`-enriched functors is actually represented by
the usual type of natural transformations!
-/
/-
**CategoryTheory.enrichedNatTransYonedaTypeIsoYonedaNatTrans** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory`。
形式化陈述：enrichedNatTransYonedaTypeIsoYonedaNatTrans {C : Type v} [EnrichedCategory
 (Type v) C] {D : Type v} [EnrichedCategory (Type v) D] (F G : EnrichedFunctor (
Type v) C D) : enrichedNatTransYoneda F G ≅ yoneda.obj (enrichedFunctorTypeEquiv
Functor F ⟶ enrichedFunctorTypeEquivFunctor G)
参数：Type v；Type v；F G : EnrichedFunctor (Type v) C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We verify that the presheaf representing natural transformations
between `Type v`-enriched functors is actually represented by
the usual type of natural transformations!
-/
def enrichedNatTransYonedaTypeIsoYonedaNatTrans {C : Type v} [EnrichedCategory (Type v) C]
    {D : Type v} [EnrichedCategory (Type v) D] (F G : EnrichedFunctor (Type v) C D) :
    enrichedNatTransYoneda F G ≅
      yoneda.obj (enrichedFunctorTypeEquivFunctor F ⟶
        enrichedFunctorTypeEquivFunctor G) :=
  NatIso.ofComponents
    (fun α =>
      { hom := ↾fun σ ↦ ↾fun x =>
          { app X := σ.app X x
            naturality X Y f := ConcreteCategory.congr_hom (σ.naturality X Y) ⟨x, f⟩ }
        inv := ↾fun σ ↦
          { app X := ↾fun x => (σ.hom x).app X
            naturality X Y := by ext ⟨x, f⟩; exact (σ.hom x).naturality f } })
    (by cat_disch)

end

end CategoryTheory

