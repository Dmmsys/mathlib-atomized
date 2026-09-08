/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# A closed monoidal category is enriched in itself

From the data of a closed monoidal category `C`, we define a `C`-category structure for `C`.
where the hom-object is given by the internal hom (coming from the closed structure).

We use `scoped instance` to avoid potential issues where `C` may also have
a `C`-category structure coming from another source (e.g. the type of simplicial sets
`SSet.{v}` has an instance of `EnrichedCategory SSet.{v}` as a category of simplicial objects;
see `Mathlib/AlgebraicTopology/SimplicialCategory/SimplicialObject.lean`).

All structure field values are defined in `Mathlib/CategoryTheory/Closed/Monoidal.lean`.

-/

public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalClosed

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- For `C` closed monoidal, build an instance of `C` as a `C`-category -/
/-
**CategoryTheory.MonoidalClosed.enrichedCategorySelf** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MonoidalClosed`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       [CategoryTheory.MonoidalClosed C] → 
CategoryTheory.EnrichedCategory C C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `C` closed monoidal, build an instance of `C` as a `C`-category
-/
scoped instance enrichedCategorySelf : EnrichedCategory C C where
  Hom x := (ihom x).obj
  id _ := id _
  comp _ _ _ := comp _ _ _
  assoc _ _ _ _ := assoc _ _ _ _

section

variable {C}

/-
**CategoryTheory.MonoidalClosed.enrichedCategorySelf_hom** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedCategorySelf_hom (X Y : C) : EnrichedCategory.Hom X Y = (ihom X).o
bj Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma enrichedCategorySelf_hom (X Y : C) :
    EnrichedCategory.Hom X Y = (ihom X).obj Y := rfl
/-
**CategoryTheory.MonoidalClosed.enrichedCategorySelf_id** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedCategorySelf_id (X : C) : eId C X = id X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma enrichedCategorySelf_id (X : C) :
    eId C X = id X := rfl
/-
**CategoryTheory.MonoidalClosed.enrichedCategorySelf_comp** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedCategorySelf_comp (X Y Z : C) : eComp C X Y Z = comp X Y Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma enrichedCategorySelf_comp (X Y Z : C) :
    eComp C X Y Z = comp X Y Z := rfl

end

/-- A monoidal closed category is an enriched ordinary category over itself. -/
/-
**CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       [CategoryTheory.MonoidalClosed C] → 
CategoryTheory.EnrichedOrdinaryCategory C C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal closed category is an enriched ordinary category over itself.
-/
scoped instance enrichedOrdinaryCategorySelf : EnrichedOrdinaryCategory C C where
  homEquiv := curryHomEquiv'
  homEquiv_id X := curry'_id X
  homEquiv_comp := curry'_comp
/-
**CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedOrdinaryCategorySelf_eHomWhiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶
 Y₂) : eHomWhiskerLeft C X g = (ihom X).map g
参数：X : C；g : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.whiskerLeft_curry'_comp`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {X Y Z : C}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma enrichedOrdinaryCategorySelf_eHomWhiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    eHomWhiskerLeft C X g = (ihom X).map g := by
  change (ρ_ _).inv ≫ _ ◁ curry' g ≫ comp X Y₁ Y₂ = _
  rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]
/-
**CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedOrdinaryCategorySelf_eHomWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y
 : C) : eHomWhiskerRight C f Y = (pre f).app Y
参数：f : X₁ ⟶ X₂；Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.curry'_whiskerRight_comp`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {X Y Z : C}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma enrichedOrdinaryCategorySelf_eHomWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    eHomWhiskerRight C f Y = (pre f).app Y := by
  change (λ_ _).inv ≫ curry' f ▷ _ ≫ comp X₁ X₂ Y = _
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
/-
**CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedOrdinaryCategorySelf_homEquiv {X Y : C} (f : X ⟶ Y) : eHomEquiv C 
f = curry' f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma enrichedOrdinaryCategorySelf_homEquiv {X Y : C} (f : X ⟶ Y) :
    eHomEquiv C f = curry' f := rfl
/-
**CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalClosed`。
形式化陈述：enrichedOrdinaryCategorySelf_homEquiv_symm {X Y : C} (g : 𝟙_ C ⟶ (ihom X).
obj Y) : (eHomEquiv C).symm g = uncurry' g
参数：g : 𝟙_ C ⟶ (ihom X).obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma enrichedOrdinaryCategorySelf_homEquiv_symm {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y) :
    (eHomEquiv C).symm g = uncurry' g := rfl

end MonoidalClosed

end CategoryTheory

