/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The pointwise monoidal structure on the product of families of monoidal categories

Given a family of monoidal categories `C i`, we define a monoidal structure on
`Π i, C i` where the tensor product is defined pointwise.

-/

@[expose] public section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Pi

open Category MonoidalCategory

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  [∀ i, MonoidalCategory (C i)]

@[simps tensorObj tensorHom whiskerLeft whiskerRight tensorUnit]
/-
**CategoryTheory.Pi.monoidalCategoryStruct** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pi`。
形式化陈述：monoidalCategoryStruct : MonoidalCategoryStruct (forall i, C i) where tens
orObj X Y i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalCategoryStruct : MonoidalCategoryStruct (∀ i, C i) where
  tensorObj X Y i := X i ⊗ Y i
  tensorHom f g i := f i ⊗ₘ g i
  whiskerLeft X _ _ f i := X i ◁ f i
  whiskerRight f Y i := f i ▷ Y i
  tensorUnit i := 𝟙_ (C i)
  leftUnitor X := isoMk (fun i ↦ λ_ (X i))
  rightUnitor X := isoMk (fun i ↦ ρ_ (X i))
  associator X Y Z := isoMk (fun i ↦ α_ (X i) (Y i) (Z i))

@[simp]
/-
**CategoryTheory.Pi.associator_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Pi`。
形式化陈述：associator_hom_apply {X Y Z : forall i, C i} {i : I} : (α_ X Y Z).hom i = 
(α_ (X i) (Y i) (Z i)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_apply {X Y Z : ∀ i, C i} {i : I} :
    (α_ X Y Z).hom i = (α_ (X i) (Y i) (Z i)).hom := rfl

@[simp]
/-
**CategoryTheory.Pi.associator_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Pi`。
形式化陈述：associator_inv_apply {X Y Z : forall i, C i} {i : I} : (α_ X Y Z).inv i = 
(α_ (X i) (Y i) (Z i)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv_apply {X Y Z : ∀ i, C i} {i : I} :
    (α_ X Y Z).inv i = (α_ (X i) (Y i) (Z i)).inv := rfl

@[simp]
/-
**CategoryTheory.Pi.isoApp_associator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Pi`。
形式化陈述：isoApp_associator {X Y Z : forall i, C i} {i : I} : isoApp (α_ X Y Z) i = 
α_ (X i) (Y i) (Z i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_associator {X Y Z : ∀ i, C i} {i : I} :
    isoApp (α_ X Y Z) i = α_ (X i) (Y i) (Z i) := rfl

@[simp]
/-
**CategoryTheory.Pi.left_unitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Pi`。
形式化陈述：left_unitor_hom_apply {X : forall i, C i} {i : I} : (fun_ X).hom i = (fun_
 (X i)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_unitor_hom_apply {X : ∀ i, C i} {i : I} :
    (λ_ X).hom i = (λ_ (X i)).hom := rfl

@[simp]
/-
**CategoryTheory.Pi.left_unitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Pi`。
形式化陈述：left_unitor_inv_apply {X : forall i, C i} {i : I} : (fun_ X).inv i = (fun_
 (X i)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_unitor_inv_apply {X : ∀ i, C i} {i : I} :
    (λ_ X).inv i = (λ_ (X i)).inv := rfl

@[simp]
/-
**CategoryTheory.Pi.isoApp_left_unitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Pi`。
形式化陈述：isoApp_left_unitor {X : forall i, C i} {i : I} : isoApp (fun_ X) i = fun_ 
(X i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_left_unitor {X : ∀ i, C i} {i : I} :
    isoApp (λ_ X) i = λ_ (X i) := rfl

@[simp]
/-
**CategoryTheory.Pi.right_unitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Pi`。
形式化陈述：right_unitor_hom_apply {X : forall i, C i} {i : I} : (ρ_ X).hom i = (ρ_ (X
 i)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_unitor_hom_apply {X : ∀ i, C i} {i : I} :
    (ρ_ X).hom i = (ρ_ (X i)).hom := rfl

@[simp]
/-
**CategoryTheory.Pi.right_unitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Pi`。
形式化陈述：right_unitor_inv_apply {X : forall i, C i} {i : I} : (ρ_ X).inv i = (ρ_ (X
 i)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_unitor_inv_apply {X : ∀ i, C i} {i : I} :
    (ρ_ X).inv i = (ρ_ (X i)).inv := rfl

@[simp]
/-
**CategoryTheory.Pi.isoApp_right_unitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Pi`。
形式化陈述：isoApp_right_unitor {X : forall i, C i} {i : I} : isoApp (ρ_ X) i = ρ_ (X 
i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_right_unitor {X : ∀ i, C i} {i : I} :
    isoApp (ρ_ X) i = ρ_ (X i) := rfl

/-- `Pi.monoidalCategory C` equips the product of an indexed family of categories with
the pointwise monoidal structure. -/
/-
**CategoryTheory.Pi.monoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.P
i`。
形式化陈述：monoidalCategory : MonoidalCategory.{max w₁ v₁} (forall i, C i) where tens
orHom_def {A B X Y} f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pi.monoidalCategory C` equips the product of an indexed family of categories wi
th
the pointwise monoidal structure.
-/
instance monoidalCategory : MonoidalCategory.{max w₁ v₁} (∀ i, C i) where
  tensorHom_def {A B X Y} f g := by ext i; simp [tensorHom_def, whiskerLeft]

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [∀ i, BraidedCategory (C i)]

/-- When each `C i` is a braided monoidal category,
the natural pointwise monoidal structure on `∀ i, C i`
is also braided.
-/
/-
**CategoryTheory.Pi.braidedCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi
`。
形式化陈述：braidedCategory : BraidedCategory (forall i, C i) where braiding X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When each `C i` is a braided monoidal category,
the natural pointwise monoidal structure on `∀ i, C i`
is also braided.
-/
instance braidedCategory : BraidedCategory (∀ i, C i) where
  braiding X Y := isoMk fun i => β_ (X i) (Y i)
  hexagon_forward X Y Z := by ext i; apply hexagon_forward
  hexagon_reverse X Y Z := by ext i; apply hexagon_reverse

@[simp]
/-
**CategoryTheory.Pi.braiding_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Pi`。
形式化陈述：braiding_hom_apply {X Y : forall i, C i} {i : I} : (β_ X Y).hom i = (β_ (X
 i) (Y i)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_hom_apply {X Y : ∀ i, C i} {i : I} :
    (β_ X Y).hom i = (β_ (X i) (Y i)).hom := rfl

@[simp]
/-
**CategoryTheory.Pi.braiding_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Pi`。
形式化陈述：braiding_inv_apply {X Y : forall i, C i} {i : I} : (β_ X Y).inv i = (β_ (X
 i) (Y i)).inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_inv_apply {X Y : ∀ i, C i} {i : I} :
    (β_ X Y).inv i = (β_ (X i) (Y i)).inv := rfl

@[simp]
/-
**CategoryTheory.Pi.isoApp_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pi
`。
形式化陈述：isoApp_braiding {X Y : forall i, C i} {i : I} : isoApp (β_ X Y) i = β_ (X 
i) (Y i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoApp_braiding {X Y : ∀ i, C i} {i : I} :
    isoApp (β_ X Y) i = β_ (X i) (Y i) := rfl

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [∀ i, SymmetricCategory (C i)]

/-- When each `C i` is a symmetric monoidal category,
the natural pointwise monoidal structure on `∀ i, C i`
is also symmetric.
-/
/-
**CategoryTheory.Pi.symmetricCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Pi`。
形式化陈述：symmetricCategory : SymmetricCategory (forall i, C i) where symmetry X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When each `C i` is a symmetric monoidal category,
the natural pointwise monoidal structure on `∀ i, C i`
is also symmetric.
-/
instance symmetricCategory : SymmetricCategory (∀ i, C i) where
  symmetry X Y := by ext i; apply symmetry

end SymmetricCategory

section Closed

open ihom

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  [∀ i, MonoidalCategory (C i)] [∀ i, MonoidalClosed (C i)]

/-- The internal hom functor `X ⟶[∀ i, C i] -` -/
@[simps!]
/-
**CategoryTheory.Pi.ihom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：ihom (X : forall i, C i) : (forall i, C i) ⥤ (forall i, C i) where obj Y
参数：X : forall i, C i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The internal hom functor `X ⟶[∀ i, C i] -`
-/
def ihom (X : ∀ i, C i) : (∀ i, C i) ⥤ (∀ i, C i) where
  obj Y := fun i ↦ (X i ⟶[C i] Y i)
  map {Y Z} f := fun i ↦ (CategoryTheory.ihom (X i)).map (f i)

set_option backward.isDefEq.respectTransparency false in
/-- The unit for the adjunction `tensorLeft X ⊣ ihom X`. -/
@[simps]
/-
**CategoryTheory.Pi.closedUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：closedUnit (X : forall i, C i) : 𝟭 (forall i, C i) ⟶ tensorLeft X ⋙ ihom X
 where app Y
参数：X : forall i, C i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the adjunction `tensorLeft X ⊣ ihom X`.
-/
def closedUnit (X : ∀ i, C i) : 𝟭 (∀ i, C i) ⟶ tensorLeft X ⋙ ihom X where
  app Y := fun i ↦ (ihom.coev (X i)).app (Y i)

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the adjunction `tensorLeft X ⊣ ihom X`. -/
@[simps]
/-
**CategoryTheory.Pi.closedCounit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：closedCounit (X : forall i, C i) : ihom X ⋙ tensorLeft X ⟶ 𝟭 (forall i, C 
i) where app Y
参数：X : forall i, C i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit for the adjunction `tensorLeft X ⊣ ihom X`.
-/
def closedCounit (X : ∀ i, C i) : ihom X ⋙ tensorLeft X ⟶ 𝟭 (∀ i, C i) where
  app Y := fun i ↦ (ihom.ev (X i)).app (Y i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equips the product of a family of closed monoidal categories with
a pointwise closed monoidal structure. -/
@[simps]
/-
**CategoryTheory.Pi.monoidalClosed** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`
。
形式化陈述：monoidalClosed : MonoidalClosed (forall i, C i) where closed X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equips the product of a family of closed monoidal categories with
a pointwise closed monoidal structure.
-/
instance monoidalClosed : MonoidalClosed (∀ i, C i) where
  closed X := {
    rightAdj := ihom X
    adj.unit := closedUnit X
    adj.counit := closedCounit X }

end Closed

set_option backward.defeqAttrib.useBackward true in
@[simps!]
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : I) : (Pi.eval C i).Monoidal where
  ε := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  δ X Y := 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, BraidedCategory (C i)] (i : I) : (Pi.eval C i).Braided where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Pi.laxMonoidalPi'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`
。
形式化陈述：laxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D] (F : forall 
i : I, D ⥤ C i) [forall i, (F i).LaxMonoidal] : (Functor.pi' F).LaxMonoidal wher
e ε
参数：F : forall i : I, D ⥤ C i；F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance laxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D] (F : ∀ i : I, D ⥤ C i)
    [∀ i, (F i).LaxMonoidal] :
    (Functor.pi' F).LaxMonoidal where
  ε := fun i ↦ Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i ↦ Functor.LaxMonoidal.μ (F i) X Y

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Pi.opLaxMonoidalPi'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.P
i`。
形式化陈述：opLaxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D] (F : foral
l i : I, D ⥤ C i) [forall i, (F i).OplaxMonoidal] : (Functor.pi' F).OplaxMonoida
l where η
参数：F : forall i : I, D ⥤ C i；F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance opLaxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D]
    (F : ∀ i : I, D ⥤ C i)
    [∀ i, (F i).OplaxMonoidal] :
    (Functor.pi' F).OplaxMonoidal where
  η := fun i ↦ Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i ↦ Functor.OplaxMonoidal.δ (F i) X Y
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
/-
**CategoryTheory.Pi.monoidalPi'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：{I : Type w₁} →   {C : I → Type u₁} →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] →       [inst_1 : (i : I) → CategoryTheory.MonoidalCat
egory (C i)] →         {D : Type u_1} →           [inst_2 : CategoryTheory.Categ
ory.{v_1, u_1} D] →             [inst_3 : CategoryTheory.MonoidalCategory D] →  
             (F : (i : I) → CategoryTheory.Functor D (C i)) →                 [(
i : I) → (F i).Monoidal] → (CategoryTheory.Functor.pi' F).Monoidal
参数：i : I；C i；i : I；C i；F : (i : I) → CategoryTheory.Functor D (C i)；i : I；F i；Ca
tegoryTheory.Functor.pi' F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalPi' {D : Type*} [Category* D] [MonoidalCategory D]
    (F : ∀ i : I, D ⥤ C i) [∀ i, (F i).Monoidal] :
    (Functor.pi' F).Monoidal where
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, BraidedCategory (C i)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : ∀ i : I, D ⥤ C i) [∀ i, (F i).LaxBraided] :
    (Functor.pi' F).LaxBraided where
  braided := by intros; ext i; exact Functor.LaxBraided.braided _ _
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, BraidedCategory (C i)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : ∀ i : I, D ⥤ C i) [∀ i, (F i).Braided] :
    (Functor.pi' F).Braided where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Pi.laxMonoidalPi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：laxMonoidalPi {D : I -> Type u₂} [forall i, Category.{v₂} (D i)] [forall i
, MonoidalCategory (D i)] (F : forall i : I, D i ⥤ C i) [forall i, (F i).LaxMono
idal] : (Functor.pi F).LaxMonoidal where ε
参数：D i；D i；F : forall i : I, D i ⥤ C i；F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance laxMonoidalPi {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i : I, D i ⥤ C i)
    [∀ i, (F i).LaxMonoidal] :
    (Functor.pi F).LaxMonoidal where
  ε := fun i ↦ Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i ↦ Functor.LaxMonoidal.μ (F i) (X i) (Y i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Pi.opLaxMonoidalPi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi
`。
形式化陈述：opLaxMonoidalPi {D : I -> Type u₂} [forall i, Category.{v₂} (D i)] [forall
 i, MonoidalCategory (D i)] (F : forall i : I, D i ⥤ C i) [forall i, (F i).Oplax
Monoidal] : (Functor.pi F).OplaxMonoidal where η
参数：D i；D i；F : forall i : I, D i ⥤ C i；F i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance opLaxMonoidalPi {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i : I, D i ⥤ C i)
    [∀ i, (F i).OplaxMonoidal] :
    (Functor.pi F).OplaxMonoidal where
  η := fun i ↦ Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i ↦ Functor.OplaxMonoidal.δ (F i) (X i) (Y i)
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
/-
**CategoryTheory.Pi.monoidalPi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pi`。
形式化陈述：{I : Type w₁} →   {C : I → Type u₁} →     [inst : (i : I) → CategoryTheory
.Category.{v₁, u₁} (C i)] →       [inst_1 : (i : I) → CategoryTheory.MonoidalCat
egory (C i)] →         {D : I → Type u₂} →           [inst_2 : (i : I) → Categor
yTheory.Category.{v₂, u₂} (D i)] →             [inst_3 : (i : I) → CategoryTheor
y.MonoidalCategory (D i)] →               (F : (i : I) → CategoryTheory.Functor 
(D i) (C i)) →                 [(i : I) → (F i).Monoidal] → (CategoryTheory.Func
tor.pi F).Monoidal
参数：i : I；C i；i : I；C i；i : I；D i；i : I；D i；F : (i : I) → CategoryTheory.Functor 
(D i) (C i)；i : I；F i；CategoryTheory.Functor.pi F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalPi {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] (F : ∀ i : I, D i ⥤ C i)
    [∀ i, (F i).Monoidal] :
    (Functor.pi F).Monoidal where
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, BraidedCategory (C i)]
    {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] [∀ i, BraidedCategory (D i)]
    (F : ∀ i : I, D i ⥤ C i) [∀ i, (F i).LaxBraided] :
    (Functor.pi F).LaxBraided where
  braided := by intros; ext i; exact Functor.LaxBraided.braided _ _
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, BraidedCategory (C i)]
    {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)] [∀ i, BraidedCategory (D i)]
    (F : ∀ i : I, D i ⥤ C i) [∀ i, (F i).Braided] :
    (Functor.pi F).Braided where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] [MonoidalCategory D]
    {F G : D ⥤ (∀ i, C i)} [F.LaxMonoidal] [G.LaxMonoidal]
    (τ : ∀ i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i)
    [∀ i, (τ i).IsMonoidal] :
    (NatTrans.pi' τ).IsMonoidal where
  unit := by ext i; simpa using NatTrans.IsMonoidal.unit (τ := τ i)
  tensor X Y := by ext i; simpa using NatTrans.IsMonoidal.tensor _ _ (τ := τ i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    [∀ i, MonoidalCategory (D i)]
    {F G : ∀ i : I, (D i ⥤ C i)} [∀ i, (F i).LaxMonoidal]
    [∀ i, (G i).LaxMonoidal] (τ : ∀ i : I, (F i) ⟶ (G i))
    [∀ i, (τ i).IsMonoidal] :
    (NatTrans.pi τ).IsMonoidal where

end Pi

end CategoryTheory

