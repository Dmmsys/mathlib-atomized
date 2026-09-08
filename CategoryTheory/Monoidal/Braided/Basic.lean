/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `BraidedCategory` another typeclass, but then have `SymmetricCategory` extend this.
The rationale is that we are not carrying any additional data, just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

## References

* [Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, Victor Ostrik, *Tensor categories*][egno15]

-/

@[expose] public section



universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/-- A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
/-
**CategoryTheory.BraidedCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：BraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] whe
re /-- The braiding natural isomorphism. -/ braiding : forall X Y : C, X otimes 
Y ≅ Y otimes X braiding_naturality_right : forall (X : C) {Y Z : C} (f : Y ⟶ Z),
 X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A braided monoidal category is a monoidal category equipped with a braiding isom
orphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
class BraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  /-- The braiding natural isomorphism. -/
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  braiding_naturality_right :
    ∀ (X : C) {Y Z : C} (f : Y ⟶ Z),
      X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
    cat_disch
  braiding_naturality_left :
    ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
      f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
    cat_disch
  /-- The first hexagon identity. -/
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    cat_disch
  /-- The second hexagon identity. -/
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
    cat_disch

attribute [reassoc (attr := simp)]
  BraidedCategory.braiding_naturality_left
  BraidedCategory.braiding_naturality_right
attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open BraidedCategory

@[inherit_doc]
notation "β_" => BraidedCategory.braiding

namespace BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

@[simp, reassoc]
/-
**CategoryTheory.BraidedCategory.braiding_tensor_left_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_tensor_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z
).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.BraidedCategory.hexagon_reverse`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   
[self : CategoryTheory.BraidedCatego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_tensor_left_hom (X Y Z : C) :
    (β_ (X ⊗ Y) Z).hom =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫
        (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom := by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[simp, reassoc]
/-
**CategoryTheory.BraidedCategory.braiding_tensor_right_hom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_tensor_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y 
Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.BraidedCategory.hexagon_forward`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   
[self : CategoryTheory.BraidedCatego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_tensor_right_hom (X Y Z : C) :
    (β_ X (Y ⊗ Z)).hom =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv := by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[simp, reassoc]
/-
**CategoryTheory.BraidedCategory.braiding_tensor_left_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_tensor_left_inv (X Y Z : C) : (β_ (X otimes Y) Z).inv = (α_ Z X Y
).inv ≫ (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv ≫ (α_ X Y Z).inv
参数：X Y Z : C。
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
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_tensor_left_inv (X Y Z : C) :
    (β_ (X ⊗ Y) Z).inv =
      (α_ Z X Y).inv ≫ (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫
        X ◁ (β_ Y Z).inv ≫ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
/-
**CategoryTheory.BraidedCategory.braiding_tensor_right_inv** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_tensor_right_inv (X Y Z : C) : (β_ X (Y otimes Z)).inv = (α_ Y Z 
X).hom ≫ Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z ≫ (α_ X Y Z).hom
参数：X Y Z : C。
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
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerRight`：inv_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) [IsIso f] : inv (f ▷ Z) = inv f ▷ Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.inv_whiskerLeft`：inv_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) [IsIso f] : inv (X ◁ f) = X ◁ inv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_tensor_right_inv (X Y Z : C) :
    (β_ X (Y ⊗ Z)).inv =
      (α_ Y Z X).hom ≫ Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫
        (β_ X Y).inv ▷ Z ≫ (α_ X Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.BraidedCategory.braiding_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.BraidedCategory`。
形式化陈述：braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (f otimesₘ
 g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g otimesₘ f)
参数：f : X ⟶ Y；g : X' ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right_assoc`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoid
alCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ₘ f) := by
  rw [tensorHom_def' f g, tensorHom_def g f]
  simp_rw [Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.BraidedCategory.braiding_inv_naturality_right** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_inv_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ (β_ 
Z X).inv = (β_ Y X).inv ≫ f ▷ X
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.CommSq.vert_inv`：vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : Co
mmSq f g.hom h.hom i) : CommSq i g.inv h.inv f
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C}   [self : CategoryTheory.BraidedCatego…
-/
theorem braiding_inv_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ f ≫ (β_ Z X).inv = (β_ Y X).inv ≫ f ▷ X :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality_left f X

@[reassoc (attr := simp)]
/-
**CategoryTheory.BraidedCategory.braiding_inv_naturality_left** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_inv_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ (β_ Z
 Y).inv = (β_ Z X).inv ≫ Z ◁ f
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.CommSq.vert_inv`：vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : Co
mmSq f g.hom h.hom i) : CommSq i g.inv h.inv f
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCate
gory C}   [self : CategoryTheory.BraidedCatego…
-/
theorem braiding_inv_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z ≫ (β_ Z Y).inv = (β_ Z X).inv ≫ Z ◁ f :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality_right Z f

@[reassoc (attr := simp)]
/-
**CategoryTheory.BraidedCategory.braiding_inv_naturality** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.BraidedCategory`。
形式化陈述：braiding_inv_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (f oti
mesₘ g) ≫ (β_ Y' Y).inv = (β_ X' X).inv ≫ (g otimesₘ f)
参数：f : X ⟶ Y；g : X' ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.CommSq.vert_inv`：vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : Co
mmSq f g.hom h.hom i) : CommSq i g.inv h.inv f
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality`：braiding_naturality 
{X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (f otimesₘ g) ≫ (braiding Y Y').hom 
= (braiding X X').hom ≫ (g otimesₘ f)
-/
theorem braiding_inv_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g) ≫ (β_ Y' Y).inv = (β_ X' X).inv ≫ (g ⊗ₘ f) :=
  CommSq.w <| .vert_inv <| .mk <| braiding_naturality g f

set_option backward.defeqAttrib.useBackward true in
/-- In a braided monoidal category, the functors `tensorLeft X` and
`tensorRight X` are isomorphic. -/
@[simps]
/-
**CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：tensorLeftIsoTensorRight (X : C) : tensorLeft X ≅ tensorRight X where hom
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a braided monoidal category, the functors `tensorLeft X` and
`tensorRight X` are isomorphic.
-/
def tensorLeftIsoTensorRight (X : C) :
    tensorLeft X ≅ tensorRight X where
  hom := { app Y := (β_ X Y).hom }
  inv := { app Y := (β_ X Y).inv }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The braiding isomorphism as a natural isomorphism of bifunctors `C ⥤ C ⥤ C`. -/
@[simps!]
/-
**CategoryTheory.BraidedCategory.curriedBraidingNatIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.BraidedCategory`。
形式化陈述：curriedBraidingNatIso : curriedTensor C ≅ (curriedTensor C).flip
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braiding isomorphism as a natural isomorphism of bifunctors `C ⥤ C ⥤ C`.
-/
def curriedBraidingNatIso : curriedTensor C ≅ (curriedTensor C).flip :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ β_ X Y))

@[reassoc]
/-
**CategoryTheory.BraidedCategory.yang_baxter** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.BraidedCategory`。
形式化陈述：yang_baxter (X Y Z : C) : (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).h
om ≫ Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom = X ◁
 (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom ≫ Z ◁ (β_ X Y
).hom
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoid
alCategory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCate
gory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
-/
theorem yang_baxter (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
    Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫
      (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom := by
  rw [← braiding_tensor_right_hom_assoc X Y Z, ← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id, comp_id, ← braiding_naturality_right, braiding_tensor_right_hom]
/-
**CategoryTheory.BraidedCategory.yang_baxter'** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.BraidedCategory`。
形式化陈述：yang_baxter' (X Y Z : C) : (β_ X Y).hom ▷ Z otimes≫ Y ◁ (β_ X Z).hom otime
s≫ (β_ Y Z).hom ▷ X = 𝟙 _ otimes≫ (X ◁ (β_ Y Z).hom otimes≫ (β_ X Z).hom ▷ Y oti
mes≫ Z ◁ (β_ X Y).hom) otimes≫ 𝟙 _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
（共 34 条，此处仅展示前 30 条）
-/
theorem yang_baxter' (X Y Z : C) :
    (β_ X Y).hom ▷ Z ⊗≫ Y ◁ (β_ X Z).hom ⊗≫ (β_ Y Z).hom ▷ X =
      𝟙 _ ⊗≫ (X ◁ (β_ Y Z).hom ⊗≫ (β_ X Z).hom ▷ Y ⊗≫ Z ◁ (β_ X Y).hom) ⊗≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv, ← cancel_mono (α_ Z Y X).hom]
  convert! yang_baxter X Y Z using 1
  all_goals monoidal
/-
**CategoryTheory.BraidedCategory.yang_baxter_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.BraidedCategory`。
形式化陈述：yang_baxter_iso (X Y Z : C) : (α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) 
Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) ≪≫ (α_ Y Z X).symm ≪≫ whiskerRightIso
 (β_ Y Z) X ≪≫ (α_ Z Y X) = whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫ whis
kerRightIso (β_ X Z) Y ≪≫ α_ Z X Y ≪≫ whiskerLeftIso Z (β_ X Y)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.BraidedCategory.yang_baxter`：yang_baxter (X Y Z : C) : (α
_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α_ Y Z X)
.inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z …
-/
theorem yang_baxter_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫
    whiskerLeftIso Y (β_ X Z) ≪≫ (α_ Y Z X).symm ≪≫
    whiskerRightIso (β_ Y Z) X ≪≫ (α_ Z Y X) =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫
      whiskerRightIso (β_ X Z) Y ≪≫ α_ Z X Y ≪≫
      whiskerLeftIso Z (β_ X Y) := Iso.ext (yang_baxter X Y Z)
/-
**CategoryTheory.BraidedCategory.hexagon_forward_iso** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.BraidedCategory`。
形式化陈述：hexagon_forward_iso (X Y Z : C) : α_ X Y Z ≪≫ β_ X (Y otimes Z) ≪≫ α_ Y Z 
X = whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.BraidedCategory.hexagon_forward`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   
[self : CategoryTheory.BraidedCatego…
-/
theorem hexagon_forward_iso (X Y Z : C) :
    α_ X Y Z ≪≫ β_ X (Y ⊗ Z) ≪≫ α_ Y Z X =
      whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) :=
  Iso.ext (hexagon_forward X Y Z)
/-
**CategoryTheory.BraidedCategory.hexagon_reverse_iso** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.BraidedCategory`。
形式化陈述：hexagon_reverse_iso (X Y Z : C) : (α_ X Y Z).symm ≪≫ β_ (X otimes Y) Z ≪≫ 
(α_ Z X Y).symm = whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫ whiskerRightIs
o (β_ X Z) Y
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.BraidedCategory.hexagon_reverse`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   
[self : CategoryTheory.BraidedCatego…
-/
theorem hexagon_reverse_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ β_ (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫ whiskerRightIso (β_ X Z) Y :=
  Iso.ext (hexagon_reverse X Y Z)

@[reassoc]
/-
**CategoryTheory.BraidedCategory.hexagon_forward_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.BraidedCategory`。
形式化陈述：hexagon_forward_inv (X Y Z : C) : (α_ Y Z X).inv ≫ (β_ X (Y otimes Z)).inv
 ≫ (α_ X Y Z).inv = Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_inv`：braiding_tenso
r_right_inv (X Y Z : C) : (β_ X (Y otimes Z)).inv = (α_ Y Z X).hom ≫ Y ◁ (β_ X Z
).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z ≫ (α…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hexagon_forward_inv (X Y Z : C) :
    (α_ Y Z X).inv ≫ (β_ X (Y ⊗ Z)).inv ≫ (α_ X Y Z).inv =
      Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z := by
  simp

@[reassoc]
/-
**CategoryTheory.BraidedCategory.hexagon_reverse_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.BraidedCategory`。
形式化陈述：hexagon_reverse_inv (X Y Z : C) : (α_ Z X Y).hom ≫ (β_ (X otimes Y) Z).inv
 ≫ (α_ X Y Z).hom = (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_inv`：braiding_tensor
_left_inv (X Y Z : C) : (β_ (X otimes Y) Z).inv = (α_ Z X Y).inv ≫ (β_ X Z).inv 
▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv ≫ (α_…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hexagon_reverse_inv (X Y Z : C) :
    (α_ Z X Y).hom ≫ (β_ (X ⊗ Y) Z).inv ≫ (α_ X Y Z).hom =
      (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv := by
  simp

end BraidedCategory

-- FIXME: `reassoc_of%` should unfold `autoParam`.
/--
Verifying the axioms for a braiding by checking that the candidate braiding is sent to a braiding
by a faithful monoidal functor.
-/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.ofFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.BraidedCategory`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.
MonoidalCategory D] →             (F : CategoryTheory.Functor C D) →            
   [inst_4 : F.Monoidal] →                 [F.Faithful] →                   [ins
t_6 : CategoryTheory.BraidedCategory D] →                     (β :              
           (X Y : C) →                           CategoryTheory.MonoidalCategory
Struct.tensorObj X Y ≅                             CategoryTheory.MonoidalCatego
ryStruct.tensorObj Y X) →                       autoParam                       
    (∀ (X Y : C),                             CategoryTheory.CategoryStruct.comp
 (CategoryTheory.Functor.LaxMonoidal.μ F X Y)                                 (F
.map (β X Y).hom) =                               CategoryTheory.CategoryStruct.
comp (β_ (F.obj X) (F.obj Y)).hom                                 (CategoryTheor
y.Functor.LaxMonoidal.μ F Y X))                           CategoryTheory.Braided
Category.ofFaithful._auto_1 →                         CategoryTheory.BraidedCate
gory C
参数：F : CategoryTheory.Functor C D；β :                         (X Y : C) →       
                    CategoryTheory.MonoidalCategoryStruct.tensorObj X Y ≅       
                      CategoryTheory.MonoidalCategoryStruct.tensorObj Y X；∀ (X Y
 : C),                             CategoryTheory.CategoryStruct.comp (CategoryT
heory.Functor.LaxMonoidal.μ F X Y)                                 (F.map (β X Y
).hom) =                               CategoryTheory.CategoryStruct.comp (β_ (F
.obj X) (F.obj Y)).hom                                 (CategoryTheory.Functor.L
axMonoidal.μ F Y X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verifying the axioms for a braiding by checking that the candidate braiding is s
ent to a braiding
by a faithful monoidal functor.
-/
def BraidedCategory.ofFaithful {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Faithful] [BraidedCategory D]
    (β : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X)
    (w : ∀ X Y, μ F _ _ ≫ F.map (β X Y).hom = (β_ _ _).hom ≫ μ F _ _ := by cat_disch) :
    BraidedCategory C where
  braiding := β
  braiding_naturality_left := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← μ_natural_left_assoc, w, Functor.map_comp,
      reassoc_of% w, braiding_naturality_left_assoc, μ_natural_right]
  braiding_naturality_right := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp, ← μ_natural_right_assoc, w, Functor.map_comp,
      reassoc_of% w, braiding_naturality_right_assoc, μ_natural_left]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (μ F _ _ ▷ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      μ_natural_left_assoc, ← comp_whiskerRight_assoc, w,
      comp_whiskerRight_assoc, Functor.LaxMonoidal.associativity_assoc,
      Functor.LaxMonoidal.associativity_assoc, ← μ_natural_right, ←
      whiskerLeft_comp_assoc, w, whiskerLeft_comp_assoc,
      reassoc_of% w, braiding_naturality_right_assoc,
      Functor.LaxMonoidal.associativity, hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (_ ◁ μ F _ _)).1 ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ←
      μ_natural_right_assoc, ← whiskerLeft_comp_assoc, w,
      whiskerLeft_comp_assoc, Functor.LaxMonoidal.associativity_inv_assoc,
      Functor.LaxMonoidal.associativity_inv_assoc, ← μ_natural_left,
      ← comp_whiskerRight_assoc, w, comp_whiskerRight_assoc, reassoc_of% w,
      braiding_naturality_left_assoc, Functor.LaxMonoidal.associativity_inv, hexagon_reverse_assoc]

/-- Pull back a braiding along a fully faithful monoidal functor. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.ofFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.BraidedCategory`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.
MonoidalCategory D] →             (F : CategoryTheory.Functor C D) →            
   [F.Monoidal] →                 [F.Full] → [F.Faithful] → [CategoryTheory.Brai
dedCategory D] → CategoryTheory.BraidedCategory C
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a braiding along a fully faithful monoidal functor.
-/
noncomputable def BraidedCategory.ofFullyFaithful {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [BraidedCategory D] : BraidedCategory C :=
  .ofFaithful F fun X Y ↦ F.preimageIso ((μIso F _ _).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ μIso F _ _)

section

/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories", Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

/-
**CategoryTheory.braiding_leftUnitor_aux** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_leftUnitor_aux₁ (X : C) :
    (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
        (𝟙_ C ◁ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((λ_ X).hom ▷ _) =
      ((λ_ _).hom ▷ X) ≫ (β_ X (𝟙_ C)).inv := by
  monoidal
/-
**CategoryTheory.braiding_leftUnitor_aux** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_leftUnitor_aux₂ (X : C) :
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) = (ρ_ X).hom ▷ 𝟙_ C :=
  calc
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) =
      ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by
      simp
    _ = ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).hom) ≫
          (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((λ_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((λ_ _).hom ▷ X) ≫ (β_ X _).inv := by
      rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (λ_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_right]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (λ_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by rw [triangle]

@[reassoc]
/-
**CategoryTheory.braiding_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：braiding_leftUnitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (fun_ X).hom = (ρ_ X).ho
m
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_iff`：whiskerRight_iff {X Y 
: C} (f g : X ⟶ Y) : f ▷ 𝟙_ C = g ▷ 𝟙_ C ↔ f = g
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.braiding_leftUnitor_aux₂`：braiding_leftUnitor_aux₂ (X : C
) : ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((fun_ X).hom ▷ 𝟙_ C) = (ρ_ X).hom ▷ 𝟙_ C
-/
theorem braiding_leftUnitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  rw [← whiskerRight_iff, comp_whiskerRight, braiding_leftUnitor_aux₂]
/-
**CategoryTheory.braiding_rightUnitor_aux** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_rightUnitor_aux₁ (X : C) :
    (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
        ((β_ (𝟙_ C) X).inv ▷ 𝟙_ C) ≫ (α_ _ X _).hom ≫ (_ ◁ (ρ_ X).hom) =
      (X ◁ (ρ_ _).hom) ≫ (β_ (𝟙_ C) X).inv := by
  simp
/-
**CategoryTheory.braiding_rightUnitor_aux** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_rightUnitor_aux₂ (X : C) :
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) = 𝟙_ C ◁ (λ_ X).hom :=
  calc
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ▷ _) ≫
          ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫
          (𝟙_ C ◁ (ρ_ X).hom) := by
      (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (X ◁ (ρ_ _).hom) ≫ (β_ _ X).inv := by simp
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_left]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙_ C ◁ (λ_ X).hom := by rw [triangle_assoc_comp_right]

@[reassoc]
/-
**CategoryTheory.braiding_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：braiding_rightUnitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (fun_ X).h
om
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_iff`：whiskerLeft_iff {X Y : 
C} (f g : X ⟶ Y) : 𝟙_ C ◁ f = 𝟙_ C ◁ g ↔ f = g
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.braiding_rightUnitor_aux₂`：braiding_rightUnitor_aux₂ (X :
 C) : (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) = 𝟙_ C ◁ (fun_ X).hom
-/
theorem braiding_rightUnitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (λ_ X).hom := by
  rw [← whiskerLeft_iff, whiskerLeft_comp, braiding_rightUnitor_aux₂]

@[reassoc, simp]
/-
**CategoryTheory.braiding_tensorUnit_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：braiding_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ 
X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
theorem braiding_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).hom = (λ_ X).hom ≫ (ρ_ X).inv := by
  simp [← braiding_rightUnitor]

@[reassoc, simp]
/-
**CategoryTheory.braiding_inv_tensorUnit_left** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：braiding_inv_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (f
un_ X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_ext`：inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id 
: f.hom ≫ g = 𝟙 X) : f.inv = g
· 使用定理 `CategoryTheory.braiding_tensorUnit_left`：braiding_tensorUnit_left (X : C
) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
-/
theorem braiding_inv_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_left]
  monoidal

@[reassoc]
/-
**CategoryTheory.leftUnitor_inv_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：leftUnitor_inv_braiding (X : C) : (fun_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X
).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.braiding_tensorUnit_left`：braiding_tensorUnit_left (X : C
) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftUnitor_inv_braiding (X : C) : (λ_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv := by
  simp

@[reassoc]
/-
**CategoryTheory.rightUnitor_inv_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：rightUnitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (fun_ 
X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.braiding_leftUnitor`：braiding_leftUnitor (X : C) : (β_ X 
(𝟙_ C)).hom ≫ (fun_ X).hom = (ρ_ X).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightUnitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (λ_ X).inv := by
  apply (cancel_mono (λ_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]

@[reassoc, simp]
/-
**CategoryTheory.braiding_tensorUnit_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：braiding_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_
 X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
  simp [← rightUnitor_inv_braiding]

@[reassoc, simp]
/-
**CategoryTheory.braiding_inv_tensorUnit_right** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：braiding_inv_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).inv = (fun_ X).hom ≫
 (ρ_ X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_ext`：inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id 
: f.hom ≫ g = 𝟙 X) : f.inv = g
· 使用定理 `CategoryTheory.braiding_tensorUnit_right`：braiding_tensorUnit_right (X :
 C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
-/
theorem braiding_inv_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).inv = (λ_ X).hom ≫ (ρ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_right]
  monoidal

end

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric. -/
@[stacks 0FFW]
/-
**CategoryTheory.SymmetricCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：SymmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] e
xtends BraidedCategory.{v} C where -- braiding symmetric: symmetry : forall X Y 
: C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X otimes Y)
参数：C : Type u。
继承自：BraidedCategory.{v} C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A symmetric monoidal category is a braided monoidal category for which the braid
ing is symmetric.
-/
class SymmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    BraidedCategory.{v} C where
  -- braiding symmetric:
  symmetry : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by cat_disch

attribute [reassoc (attr := simp)] SymmetricCategory.symmetry
/-
**CategoryTheory.SymmetricCategory.braiding_swap_eq_inv_braiding** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.SymmetricCategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.SymmetricCategory C] (
X Y : C), (β_ Y X).hom = (β_ X Y).inv
参数：X Y : C；β_ Y X；β_ X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_ext'`：inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_i
d : f.hom ≫ g = 𝟙 X) : g = f.inv
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   [self
 : CategoryTheory.SymmetricCate…
-/
lemma SymmetricCategory.braiding_swap_eq_inv_braiding {C : Type u₁}
    [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C] (X Y : C) :
    (β_ Y X).hom = (β_ X Y).inv := Iso.inv_ext' (symmetry X Y)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

/-- A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
/-
**CategoryTheory.Functor.LaxBraided** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [CategoryTheory.BraidedCategory C
] →         {D : Type u₂} →           [inst_3 : CategoryTheory.Category.{v₂, u₂}
 D] →             [inst_4 : CategoryTheory.MonoidalCategory D] →               [
CategoryTheory.BraidedCategory D] → CategoryTheory.Functor C D → Type (max u₁ v₂
)
参数：max u₁ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lax braided functor between braided monoidal categories is a lax monoidal func
tor
which preserves the braiding.
-/
class Functor.LaxBraided (F : C ⥤ D) extends F.LaxMonoidal where
  braided : ∀ X Y : C, μ X Y ≫ F.map (β_ X Y).hom =
    (β_ (F.obj X) (F.obj Y)).hom ≫ μ Y X := by cat_disch

namespace Functor.LaxBraided

attribute [reassoc] braided

/-
**CategoryTheory.Functor.LaxBraided.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor.LaxBraided`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.BraidedC
ategory C] → (CategoryTheory.Functor.id C).LaxBraided
参数：CategoryTheory.Functor.id C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance id : (𝟭 C).LaxBraided where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.LaxBraided.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.F
unctor.LaxBraided`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [F.LaxBraided] [G.LaxBraided] :
    (F ⋙ G).LaxBraided where
  braided X Y := by
    dsimp
    slice_lhs 2 3 =>
      rw [← CategoryTheory.Functor.map_comp, braided, CategoryTheory.Functor.map_comp]
    slice_lhs 1 2 => rw [braided]
    simp only [Category.assoc]

/--
Given two lax monoidal, monoidally isomorphic functors, if one is lax braided, so is the other.
-/
@[instance_reducible]
/-
**CategoryTheory.Functor.LaxBraided.ofNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.LaxBraided`。
形式化陈述：ofNatIso {F G : C ⥤ D} (i : F ≅ G) [F.LaxBraided] [G.LaxMonoidal] [NatTran
s.IsMonoidal i.hom] : G.LaxBraided where braided X Y
参数：i : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two lax monoidal, monoidally isomorphic functors, if one is lax braided, s
o is the other.
-/
def ofNatIso {F G : C ⥤ D} (i : F ≅ G) [F.LaxBraided] [G.LaxMonoidal]
    [NatTrans.IsMonoidal i.hom] : G.LaxBraided where
  braided X Y := by
    have (X Y : C) : μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app _ := by
      simp [NatTrans.IsMonoidal.tensor X Y, tensorHom_comp_tensorHom_assoc]
    rw [this X Y, this Y X, ← braiding_naturality_assoc, ← Functor.LaxBraided.braided_assoc]
    simp

/-- Copy of a lax braided structure on a functor `F` with new `ε` and `μ` fields equal to the old
ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/-
**CategoryTheory.Functor.LaxBraided.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.LaxBraided`。
形式化陈述：copy {F : C ⥤ D} (hF : F.LaxBraided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)) (μ' : fora
ll X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)) (hε : ε' = ε F
参数：hF : F.LaxBraided；ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)；μ' : forall X Y : C, F.obj X otime
s F.obj Y ⟶ F.obj (X otimes Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a lax braided structure on a functor `F` with new `ε` and `μ` fields equ
al to the old
ones.

This is useful to fix definitional equalities.
-/
def copy {F : C ⥤ D} (hF : F.LaxBraided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch) : F.LaxBraided where
  __ := hF.toLaxMonoidal.copy ε' μ' hε hμ
  braided X Y := hμ ▸ hF.braided X Y

end Functor.LaxBraided

section

variable (C D)

/-- Bundled version of lax braided functors. -/
/-
**CategoryTheory.LaxBraidedFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：LaxBraidedFunctor extends C ⥤ D where laxBraided : toFunctor.LaxBraided
继承自：C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled version of lax braided functors.
-/
structure LaxBraidedFunctor extends C ⥤ D where
  laxBraided : toFunctor.LaxBraided := by infer_instance

namespace LaxBraidedFunctor

variable {C D}

attribute [instance] laxBraided

/-- Constructor for `LaxBraidedFunctor C D`. -/
@[simps toFunctor]
/-
**CategoryTheory.LaxBraidedFunctor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
LaxBraidedFunctor`。
形式化陈述：of (F : C ⥤ D) [F.LaxBraided] : LaxBraidedFunctor C D where toFunctor
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `LaxBraidedFunctor C D`.
-/
def of (F : C ⥤ D) [F.LaxBraided] : LaxBraidedFunctor C D where
  toFunctor := F

/-- The lax monoidal functor induced by a lax braided functor. -/
@[simps toFunctor]
/-
**CategoryTheory.LaxBraidedFunctor.toLaxMonoidalFunctor** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.LaxBraidedFunctor`。
形式化陈述：toLaxMonoidalFunctor (F : LaxBraidedFunctor C D) : LaxMonoidalFunctor C D 
where toFunctor
参数：F : LaxBraidedFunctor C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lax monoidal functor induced by a lax braided functor.
-/
def toLaxMonoidalFunctor (F : LaxBraidedFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor
/-
**CategoryTheory.LaxBraidedFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.La
xBraidedFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (LaxBraidedFunctor C D) :=
  inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

@[simp]
/-
**CategoryTheory.LaxBraidedFunctor.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.LaxBraidedFunctor`。
形式化陈述：id_hom (F : LaxBraidedFunctor C D) : LaxMonoidalFunctor.Hom.hom (InducedCa
tegory.Hom.hom (𝟙 F)) = 𝟙 _
参数：F : LaxBraidedFunctor C D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (F : LaxBraidedFunctor C D) :
    LaxMonoidalFunctor.Hom.hom (InducedCategory.Hom.hom (𝟙 F)) = 𝟙 _ := rfl

@[reassoc, simp]
/-
**CategoryTheory.LaxBraidedFunctor.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.LaxBraidedFunctor`。
形式化陈述：comp_hom {F G H : LaxBraidedFunctor C D} (α : F ⟶ G) (β : G ⟶ H) : (α ≫ β)
.hom = α.hom ≫ β.hom
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {F G H : LaxBraidedFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

@[ext]
/-
**CategoryTheory.LaxBraidedFunctor.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.LaxBraidedFunctor`。
形式化陈述：hom_ext {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom
.hom) : α = β
参数：h : α.hom.hom = β.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用引理 `CategoryTheory.LaxMonoidalFunctor.hom_ext`：hom_ext {F G : LaxMonoidalFun
ctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β
-/
lemma hom_ext {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) :
    α = β :=
  InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for morphisms in the category `LaxBraidedFunctor C D`. -/
@[simps]
/-
**CategoryTheory.LaxBraidedFunctor.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.LaxBraidedFunctor`。
形式化陈述：homMk {F G : LaxBraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTr
ans.IsMonoidal f] : F ⟶ G
参数：f : F.toFunctor ⟶ G.toFunctor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in the category `LaxBraidedFunctor C D`.
-/
def homMk {F G : LaxBraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G := ⟨f, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for isomorphisms in the category `LaxBraidedFunctor C D`. -/
@[simps]
/-
**CategoryTheory.LaxBraidedFunctor.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.LaxBraidedFunctor`。
形式化陈述：isoMk {F G : LaxBraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor) [NatTr
ans.IsMonoidal e.hom] : F ≅ G where hom
参数：e : F.toFunctor ≅ G.toFunctor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in the category `LaxBraidedFunctor C D`.
-/
def isoMk {F G : LaxBraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] :
    F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

/-- The forgetful functor from lax braided functors to lax monoidal functors. -/
@[simps! obj map]
/-
**CategoryTheory.LaxBraidedFunctor.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.LaxBraidedFunctor`。
形式化陈述：forget : LaxBraidedFunctor C D ⥤ LaxMonoidalFunctor C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from lax braided functors to lax monoidal functors.
-/
def forget : LaxBraidedFunctor C D ⥤ LaxMonoidalFunctor C D :=
  inducedFunctor _

/-- The forgetful functor from lax braided functors to lax monoidal functors
is fully faithful. -/
/-
**CategoryTheory.LaxBraidedFunctor.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.LaxBraidedFunctor`。
形式化陈述：fullyFaithfulForget : (forget (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from lax braided functors to lax monoidal functors
is fully faithful.
-/
def fullyFaithfulForget : (forget (C := C) (D := D)).FullyFaithful :=
  fullyFaithfulInducedFunctor _

section

variable {F G : LaxBraidedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for isomorphisms between lax braided functors. -/
/-
**CategoryTheory.LaxBraidedFunctor.isoOfComponents** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.LaxBraidedFunctor`。
形式化陈述：isoOfComponents : F ≅ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms between lax braided functors.
-/
def isoOfComponents :
    F ≅ G :=
  fullyFaithfulForget.preimageIso
    (LaxMonoidalFunctor.isoOfComponents e naturality unit tensor)

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.LaxBraidedFunctor.isoOfComponents_hom_hom_hom_app** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.LaxBraidedFunctor`。
形式化陈述：isoOfComponents_hom_hom_hom_app (X : C) : (isoOfComponents e naturality un
it tensor).hom.hom.hom.app X = (e X).hom
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoOfComponents_hom_hom_hom_app (X : C) :
    (isoOfComponents e naturality unit tensor).hom.hom.hom.app X = (e X).hom := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.LaxBraidedFunctor.isoOfComponents_inv_hom_hom_app** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.LaxBraidedFunctor`。
形式化陈述：isoOfComponents_inv_hom_hom_app (X : C) : (isoOfComponents e naturality un
it tensor).inv.hom.hom.app X = (e X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoOfComponents_inv_hom_hom_app (X : C) :
    (isoOfComponents e naturality unit tensor).inv.hom.hom.app X = (e X).inv := rfl

end

end LaxBraidedFunctor

end

/-- A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
@[ext]
/-
**CategoryTheory.Functor.Braided** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [CategoryTheory.BraidedCategory C
] →         {D : Type u₂} →           [inst_3 : CategoryTheory.Category.{v₂, u₂}
 D] →             [inst_4 : CategoryTheory.MonoidalCategory D] →               [
CategoryTheory.BraidedCategory D] → CategoryTheory.Functor C D → Type (max u₁ v₂
)
参数：max u₁ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
class Functor.Braided (F : C ⥤ D) extends F.Monoidal, F.LaxBraided where

@[simp, reassoc]
/-
**CategoryTheory.Functor.map_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] {D 
: Type u₂} [inst_3 : CategoryTheory.Category.{v₂, u₂} D]   [inst_4 : CategoryThe
ory.MonoidalCategory D] [inst_5 : CategoryTheory.BraidedCategory D]   (F : Categ
oryTheory.Functor C D) (X Y : C) [inst_6 : F.Braided],   F.map (β_ X Y).hom =   
  CategoryTheory.CategoryStruct.comp (CategoryTheory.Functor.OplaxMonoidal.δ F X
 Y)       (CategoryTheory.CategoryStruct.comp (β_ (F.obj X) (F.obj Y)).hom (Cate
goryTheory.Functor.LaxMonoidal.μ F Y X))
参数：F : CategoryTheory.Functor C D；X Y : C；β_ X Y；CategoryTheory.Functor.OplaxMon
oidal.δ F X Y；CategoryTheory.CategoryStruct.comp (β_ (F.obj X) (F.obj Y)).hom (C
ategoryTheory.Functor.LaxMonoidal.μ F Y X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.Braided.braided`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst
_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
-/
lemma Functor.map_braiding (F : C ⥤ D) (X Y : C) [F.Braided] :
    F.map (β_ X Y).hom =
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← Functor.Braided.braided, δ_μ_assoc]

/--
A braided category with a faithful braided functor to a symmetric category is itself symmetric.
-/
@[instance_reducible]
/-
**CategoryTheory.SymmetricCategory.ofFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SymmetricCategory`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.
MonoidalCategory D] →             [inst_4 : CategoryTheory.BraidedCategory C] → 
              [inst_5 : CategoryTheory.SymmetricCategory D] →                 (F
 : CategoryTheory.Functor C D) → [F.Braided] → [F.Faithful] → CategoryTheory.Sym
metricCategory C
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A braided category with a faithful braided functor to a symmetric category is it
self symmetric.
-/
def SymmetricCategory.ofFaithful {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [SymmetricCategory D] (F : C ⥤ D) [F.Braided]
    [F.Faithful] : SymmetricCategory C where
  symmetry X Y := F.map_injective (by simp)

/-- Pull back a symmetric braiding along a fully faithful monoidal functor. -/
@[instance_reducible]
/-
**CategoryTheory.SymmetricCategory.ofFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.SymmetricCategory`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.
MonoidalCategory D] →             (F : CategoryTheory.Functor C D) →            
   [F.Monoidal] →                 [F.Full] → [F.Faithful] → [CategoryTheory.Symm
etricCategory D] → CategoryTheory.SymmetricCategory C
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a symmetric braiding along a fully faithful monoidal functor.
-/
noncomputable def SymmetricCategory.ofFullyFaithful {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [SymmetricCategory D] : SymmetricCategory C :=
  let h : BraidedCategory C := BraidedCategory.ofFullyFaithful F
  let _ : F.Braided := {
    braided X Y := by
      simp +instances [h, BraidedCategory.ofFullyFaithful, BraidedCategory.ofFaithful] }
  .ofFaithful F

namespace Functor.Braided

/-
**CategoryTheory.Functor.Braided.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Braided`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟭 C).Braided where
/-
**CategoryTheory.Functor.Braided.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Braided`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) (G : D ⥤ E) [F.Braided] [G.Braided] : (F ⋙ G).Braided where
/-
**CategoryTheory.Functor.Braided.toMonoidal_injective** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.Braided`。
形式化陈述：toMonoidal_injective (F : C ⥤ D) : Function.Injective (@Braided.toMonoidal
 _ _ _ _ _ _ _ _ _ : F.Braided -> F.Monoidal)
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toMonoidal_injective (F : C ⥤ D) : Function.Injective
    (@Braided.toMonoidal _ _ _ _ _ _ _ _ _ : F.Braided → F.Monoidal) := by rintro ⟨⟩ ⟨⟩ rfl; rfl

/-- Copy of a braided structure on a functor `F` with new `ε`, `μ`, `η` and `δ` fields equal to the
old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/-
**CategoryTheory.Functor.Braided.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor.Braided`。
形式化陈述：copy {F : C ⥤ D} (hF : F.Braided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)) (μ' : forall 
X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
 (δ' : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y) (hε : ε' = ε
 F
参数：hF : F.Braided；ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)；μ' : forall X Y : C, F.obj X otimes F
.obj Y ⟶ F.obj (X otimes Y)；η' : F.obj (𝟙_ C) ⟶ 𝟙_ D；δ' : forall X Y : C, F.obj 
(X otimes Y) ⟶ F.obj X otimes F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a braided structure on a functor `F` with new `ε`, `μ`, `η` and `δ` fiel
ds equal to the
old ones.

This is useful to fix definitional equalities.
-/
def copy {F : C ⥤ D} (hF : F.Braided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (δ' : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch)
    (hη : η' = η F := by cat_disch) (hδ : δ' = δ F := by cat_disch) : F.Braided where
  __ := hF.toMonoidal.copy ε' μ' η' δ' hε hμ hη hδ
  braided X Y := hμ ▸ hF.braided X Y

end Functor.Braided

section CommMonoid

variable (M : Type u) [CommMonoid M]

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (Discrete M) where
  braiding X Y := Discrete.eqToIso (mul_comm X.as Y.as)

variable {M} {N : Type u} [CommMonoid N]

/-- A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
/-
**CategoryTheory.Discrete.monoidalFunctorBraided** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Discrete`。
形式化陈述：{M : Type u} →   [inst : CommMonoid M] →     {N : Type u} → [inst_1 : Comm
Monoid N] → (F : M →* N) → (CategoryTheory.Discrete.monoidalFunctor F).Braided
参数：F : M →* N；CategoryTheory.Discrete.monoidalFunctor F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative morphism between commutative monoids gives a braided functor be
tween
the corresponding discrete braided monoidal categories.
-/
instance Discrete.monoidalFunctorBraided (F : M →* N) :
    (Discrete.monoidalFunctor F).Braided where

end CommMonoid

namespace MonoidalCategory

section Tensor

/-- Swap the second and third objects in `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂)`. This is used to strength the
tensor product functor from `C × C` to `C` as a monoidal functor. -/
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swap the second and third objects in `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂)`. This is used to st
rength the
tensor product functor from `C × C` to `C` as a monoidal functor.
-/
def tensorμ (X₁ X₂ Y₁ Y₂ : C) : (X₁ ⊗ X₂) ⊗ Y₁ ⊗ Y₂ ⟶ (X₁ ⊗ Y₁) ⊗ X₂ ⊗ Y₂ :=
  (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫
    (X₁ ◁ (α_ X₂ Y₁ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂) ≫
        (X₁ ◁ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv

/-- The inverse of `tensorμ`. -/
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of `tensorμ`.
-/
def tensorδ (X₁ X₂ Y₁ Y₂ : C) : (X₁ ⊗ Y₁) ⊗ X₂ ⊗ Y₂ ⟶ (X₁ ⊗ X₂) ⊗ Y₁ ⊗ Y₂ :=
  (α_ X₁ Y₁ (X₂ ⊗ Y₂)).hom ≫
    (X₁ ◁ (α_ Y₁ X₂ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).inv ▷ Y₂) ≫
        (X₁ ◁ (α_ X₂ Y₁ Y₂).hom) ≫
          (α_ X₁ X₂ (Y₁ ⊗ Y₂)).inv

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorμ_tensorδ (X₁ X₂ Y₁ Y₂ : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ≫ tensorδ X₁ X₂ Y₁ Y₂ = 𝟙 _ := by
  simp only [tensorμ, ← whiskerLeft_comp_assoc, tensorδ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorδ_tensorμ (X₁ X₂ Y₁ Y₂ : C) :
    tensorδ X₁ X₂ Y₁ Y₂ ≫ tensorμ X₁ X₂ Y₁ Y₂ = 𝟙 _ := by
  simp only [tensorδ, ← whiskerLeft_comp_assoc, tensorμ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_natural {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
    (g₂ : U₂ ⟶ V₂) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ g₁ ⊗ₘ g₂) ≫ tensorμ Y₁ Y₂ V₁ V₂ =
      tensorμ X₁ X₂ U₁ U₂ ≫ ((f₁ ⊗ₘ g₁) ⊗ₘ f₂ ⊗ₘ g₂) := by
  dsimp only [tensorμ]
  simp_rw [← id_tensorHom, ← tensorHom_id]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [tensorHom_comp_tensorHom, comp_id f₁, ← id_comp f₁, associator_inv_naturality,
      ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 =>
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, comp_id f₁, ← id_comp f₁, comp_id g₂,
      ← id_comp g₂, braiding_naturality, ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
  slice_lhs 4 5 =>
    rw [tensorHom_comp_tensorHom, comp_id f₁, ← id_comp f₁, associator_naturality,
      ← tensorHom_comp_tensorHom]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  simp only [assoc]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_natural_left {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C) :
    (f₁ ⊗ₘ f₂) ▷ (Z₁ ⊗ Z₂) ≫ tensorμ Y₁ Y₂ Z₁ Z₂ =
      tensorμ X₁ X₂ Z₁ Z₂ ≫ (f₁ ▷ Z₁ ⊗ₘ f₂ ▷ Z₂) := by
  convert! tensorμ_natural f₁ f₂ (𝟙 Z₁) (𝟙 Z₂) using 1 <;> simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorμ_natural_right (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (Z₁ ⊗ Z₂) ◁ (f₁ ⊗ₘ f₂) ≫ tensorμ Z₁ Z₂ Y₁ Y₂ =
      tensorμ Z₁ Z₂ X₁ X₂ ≫ (Z₁ ◁ f₁ ⊗ₘ Z₂ ◁ f₂) := by
  convert! tensorμ_natural (𝟙 Z₁) (𝟙 Z₂) f₁ f₂ using 1 <;> simp

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_left_unitality** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_left_unitality (X₁ X₂ : C) : (fun_ (X₁ otimes X₂)).hom = ((fun_ (𝟙_
 C)).inv ▷ (X₁ otimes X₂)) ≫ tensorμ (𝟙_ C) (𝟙_ C) X₁ X₂ ≫ ((fun_ X₁).hom otimes
ₘ (fun_ X₂).hom)
参数：X₁ X₂ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight`：leftUnitor_
inv_whiskerRight (X Y : C) : (fun_ X).inv ▷ Y = (fun_ (X otimes Y)).inv ≫ (α_ (𝟙
_ C) X Y).inv
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom_hom_inv`：pentagon_i
nv_inv_hom_hom_inv : (α_ W (X otimes Y) Z).inv ≫ (α_ W X Y).inv ▷ Z ≫ (α_ (W oti
mes X) Y Z).hom = W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y …
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.leftUnitor_inv_braiding`：leftUnitor_inv_braiding (X : C) 
: (fun_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_inv_assoc`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.M
onoidalCategory C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight`：leftUnitor_whis
kerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)
).hom
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_inv`：triangle_
assoc_comp_right_inv (X Y : C) : (ρ_ X).inv ▷ Y ≫ (α_ X (𝟙_ C) Y).hom = X ◁ (fun
_ Y).inv
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] (X Y : C) {Z : C}   (h : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_hom_inv`：whiskerLeft_hom_inv
 (X : C) {Y Z : C} (f : Y ≅ Z) : X ◁ f.hom ≫ X ◁ f.inv = 𝟙 (X otimes Y)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_inv_hom`：whiskerLeft_inv_hom
 (X : C) {Y Z : C} (f : Y ≅ Z) : X ◁ f.inv ≫ X ◁ f.hom = 𝟙 (X otimes Z)
-/
theorem tensor_left_unitality (X₁ X₂ : C) :
    (λ_ (X₁ ⊗ X₂)).hom =
      ((λ_ (𝟙_ C)).inv ▷ (X₁ ⊗ X₂)) ≫
        tensorμ (𝟙_ C) (𝟙_ C) X₁ X₂ ≫ ((λ_ X₁).hom ⊗ₘ (λ_ X₂).hom) := by
  dsimp only [tensorμ]
  have :
    ((λ_ (𝟙_ C)).inv ▷ (X₁ ⊗ X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫ (𝟙_ C ◁ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙_ C ◁ (λ_ X₁).inv ▷ X₂ := by
    simp
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    leftUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_right_unitality** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_right_unitality (X₁ X₂ : C) : (ρ_ (X₁ otimes X₂)).hom = ((X₁ otimes
 X₂) ◁ (fun_ (𝟙_ C)).inv) ≫ tensorμ X₁ X₂ (𝟙_ C) (𝟙_ C) ≫ ((ρ_ X₁).hom otimesₘ (
ρ_ X₂).hom)
参数：X₁ X₂ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.rightUnitor_inv_braiding`：rightUnitor_inv_braiding (X : C
) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (fun_ X).inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor`：whiskerLeft_rig
htUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).ho
m
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv`：whiskerLeft
_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙
_ C)).hom
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_hom_inv_inv_hom`：pentagon_h
om_hom_inv_inv_hom : (α_ W (X otimes Y) Z).hom ≫ W ◁ (α_ X Y Z).hom ≫ (α_ W X (Y
 otimes Z)).inv = (α_ W X Y).inv ▷ Z ≫ (α_ (W otim…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
（共 38 条，此处仅展示前 30 条）
-/
theorem tensor_right_unitality (X₁ X₂ : C) :
    (ρ_ (X₁ ⊗ X₂)).hom =
      ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).inv) ≫
        tensorμ X₁ X₂ (𝟙_ C) (𝟙_ C) ≫ ((ρ_ X₁).hom ⊗ₘ (ρ_ X₂).hom) := by
  dsimp only [tensorμ]
  have :
    ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).hom ≫ (X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (X₁ ◁ (ρ_ X₂).inv ▷ 𝟙_ C) := by
    monoidal
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    rightUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor_associativity** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) : (tensorμ X₁ X₂ Y₁ Y₂ ▷ (Z₁ 
otimes Z₂)) ≫ tensorμ (X₁ otimes Y₁) (X₂ otimes Y₂) Z₁ Z₂ ≫ ((α_ X₁ Y₁ Z₁).hom o
timesₘ (α_ X₂ Y₂ Z₂).hom) = (α_ (X₁ otimes X₂) (Y₁ otimes Y₂) (Z₁ otimes Z₂)).ho
m ≫ ((X₁ otimes X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) ≫ tensorμ X₁ X₂ (Y₁ otimes Z₁) (Y₂ ot
imes Z₂)
参数：X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_whisker`：evalWhiskerRight_
cons_whisker {f g h i j k : C} {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i
 ⟶ j} {η₁ : h otimes k ⟶ i otimes k} {η₂ : …
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
· 使用定理 `Mathlib.Tactic.Monoidal.eval_tensorHom`：eval_tensorHom {f g h i : C} {η 
η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f otimes h ⟶ g otimes i} (e_η : η = η') (e_θ : θ
 = θ') (e_ι : η' otimesₘ θ' …
· 使用定理 `Mathlib.Tactic.Monoidal.evalHorizontalComp_nil_nil`：evalHorizontalComp_n
il_nil {f g h i : C} (α : f ≅ g) (β : h ≅ i) : (α otimesᵢ β).hom = (α otimesᵢ β)
.hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
（共 36 条，此处仅展示前 30 条）
-/
theorem tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    (tensorμ X₁ X₂ Y₁ Y₂ ▷ (Z₁ ⊗ Z₂)) ≫
        tensorμ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) Z₁ Z₂ ≫ ((α_ X₁ Y₁ Z₁).hom ⊗ₘ (α_ X₂ Y₂ Z₂).hom) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
        ((X₁ ⊗ X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) ≫ tensorμ X₁ X₂ (Y₁ ⊗ Z₁) (Y₂ ⊗ Z₂) := by
  dsimp only [tensor_obj, prodMonoidal_tensorObj, tensorμ]
  simp only [braiding_tensor_left_hom, braiding_tensor_right_hom]
  calc
    _ = 𝟙 _ ⊗≫
      X₁ ◁ ((β_ X₂ Y₁).hom ▷ (Y₂ ⊗ Z₁) ≫ (Y₁ ⊗ X₂) ◁ (β_ Y₂ Z₁).hom) ▷ Z₂ ⊗≫
        X₁ ◁ Y₁ ◁ (β_ X₂ Z₁).hom ▷ Y₂ ▷ Z₂ ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalCategory.tensorMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：tensorMonoidal : (tensor C).Monoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tensorMonoidal : (tensor C).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := (λ_ (𝟙_ C)).symm
        μIso := fun X Y ↦
          { hom := tensorμ X.1 X.2 Y.1 Y.2
            inv := tensorδ X.1 X.2 Y.1 Y.2 }
        μIso_hom_natural_left := fun f Z ↦ tensorμ_natural_left f.1 f.2 Z.1 Z.2
        μIso_hom_natural_right := fun Z f ↦ tensorμ_natural_right Z.1 Z.2 f.1 f.2
        associativity := fun X Y Z ↦ tensor_associativity X.1 X.2 Y.1 Y.2 Z.1 Z.2
        left_unitality := fun ⟨X₁, X₂⟩ ↦ tensor_left_unitality X₁ X₂
        right_unitality := fun ⟨X₁, X₂⟩ ↦ tensor_right_unitality X₁ X₂ }
/-
**CategoryTheory.MonoidalCategory.tensor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensor_ε : ε (tensor C) = (λ_ (𝟙_ C)).inv := rfl
/-
**CategoryTheory.MonoidalCategory.tensor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensor_η : η (tensor C) = (λ_ (𝟙_ C)).hom := rfl
/-
**CategoryTheory.MonoidalCategory.tensor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensor_μ (X Y : C × C) : μ (tensor C) X Y = tensorμ X.1 X.2 Y.1 Y.2 := rfl
/-
**CategoryTheory.MonoidalCategory.tensor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tensor_δ (X Y : C × C) : δ (tensor C) X Y = tensorδ X.1 X.2 Y.1 Y.2 := rfl

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.leftUnitor_monoidal** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：leftUnitor_monoidal (X₁ X₂ : C) : (fun_ X₁).hom otimesₘ (fun_ X₂).hom = te
nsorμ (𝟙_ C) X₁ (𝟙_ C) X₂ ≫ ((fun_ (𝟙_ C)).hom ▷ (X₁ otimes X₂)) ≫ (fun_ (X₁ oti
mes X₂)).hom
参数：X₁ X₂ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_tensorHom`：eval_tensorHom {f g h i : C} {η 
η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f otimes h ⟶ g otimes i} (e_η : η = η') (e_θ : θ
 = θ') (e_ι : η' otimesₘ θ' …
· 使用定理 `Mathlib.Tactic.Monoidal.evalHorizontalComp_nil_nil`：evalHorizontalComp_n
il_nil {f g h i : C} (α : f ≅ g) (β : h ≅ i) : (α otimesᵢ β).hom = (α otimesᵢ β)
.hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_tensorHom`：naturality_tensorHom {p f₁
 g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂} (η_f₁ : p otimes f₁ ≅ pf₁) 
(η_g₁ : p otimes g₁ ≅ pf₁) (η_f₂ :…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_right`：triangle_asso
c_comp_right (X Y : C) : (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (fun_ Y).h
om
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.braiding_tensorUnit_right`：braiding_tensorUnit_right (X :
 C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
（共 40 条，此处仅展示前 30 条）
-/
theorem leftUnitor_monoidal (X₁ X₂ : C) :
    (λ_ X₁).hom ⊗ₘ (λ_ X₂).hom =
      tensorμ (𝟙_ C) X₁ (𝟙_ C) X₂ ≫ ((λ_ (𝟙_ C)).hom ▷ (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom := by
  dsimp only [tensorμ]
  have :
    (λ_ X₁).hom ⊗ₘ (λ_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).hom ≫
        (𝟙_ C ◁ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (λ_ ((X₁ ⊗ 𝟙_ C) ⊗ X₂)).hom ≫ ((ρ_ X₁).hom ▷ X₂) := by
    monoidal
  simp [this]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.rightUnitor_monoidal** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.MonoidalCategory`。
形式化陈述：rightUnitor_monoidal (X₁ X₂ : C) : (ρ_ X₁).hom otimesₘ (ρ_ X₂).hom = tenso
rμ X₁ (𝟙_ C) X₂ (𝟙_ C) ≫ ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).hom) ≫ (ρ_ (X₁ otimes X
₂)).hom
参数：X₁ X₂ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_tensorHom`：eval_tensorHom {f g h i : C} {η 
η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f otimes h ⟶ g otimes i} (e_η : η = η') (e_θ : θ
 = θ') (e_ι : η' otimesₘ θ' …
· 使用定理 `Mathlib.Tactic.Monoidal.evalHorizontalComp_nil_nil`：evalHorizontalComp_n
il_nil {f g h i : C} (α : f ≅ g) (β : h ≅ i) : (α otimesᵢ β).hom = (α otimesᵢ β)
.hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_tensorHom`：naturality_tensorHom {p f₁
 g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂} (η_f₁ : p otimes f₁ ≅ pf₁) 
(η_g₁ : p otimes g₁ ≅ pf₁) (η_f₂ :…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.braiding_rightUnitor`：braiding_rightUnitor (X : C) : (β_ 
(𝟙_ C) X).hom ≫ (ρ_ X).hom = (fun_ X).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_id`：evalWhiskerRight_id {f g : 
C} {η : f ⟶ g} {η₁ : f ⟶ g otimes 𝟙_ C} {η₂ : f otimes 𝟙_ C ⟶ g otimes 𝟙_ C} (e_
η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ :…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
-/
theorem rightUnitor_monoidal (X₁ X₂ : C) :
    (ρ_ X₁).hom ⊗ₘ (ρ_ X₂).hom =
      tensorμ X₁ (𝟙_ C) X₂ (𝟙_ C) ≫ ((X₁ ⊗ X₂) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (X₁ ⊗ X₂)).hom := by
  dsimp only [tensorμ]
  have :
    (ρ_ X₁).hom ⊗ₘ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ ⊗ 𝟙_ C)).hom ≫
        (X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (X₁ ◁ (ρ_ (𝟙_ C ⊗ X₂)).hom) ≫ (X₁ ◁ (λ_ X₂).hom) := by
    monoidal
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  monoidal

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.associator_monoidal** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalCategory`。
形式化陈述：associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) : tensorμ (X₁ otimes X₂) X₃ (Y
₁ otimes Y₂) Y₃ ≫ (tensorμ X₁ X₂ Y₁ Y₂ ▷ (X₃ otimes Y₃)) ≫ (α_ (X₁ otimes Y₁) (X
₂ otimes Y₂) (X₃ otimes Y₃)).hom = ((α_ X₁ X₂ X₃).hom otimesₘ (α_ Y₁ Y₂ Y₃).hom)
 ≫ tensorμ X₁ (X₂ otimes X₃) Y₁ (Y₂ otimes Y₃) ≫ ((X₁ otimes Y₁) ◁ tensorμ X₂ X₃
 Y₂ Y₃)
参数：X₁ X₂ X₃ Y₁ Y₂ Y₃ : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_whisker`：evalWhiskerRight_
cons_whisker {f g h i j k : C} {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i
 ⟶ j} {η₁ : h otimes k ⟶ i otimes k} {η₂ : …
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `Mathlib.Tactic.Monoidal.eval_tensorHom`：eval_tensorHom {f g h i : C} {η 
η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f otimes h ⟶ g otimes i} (e_η : η = η') (e_θ : θ
 = θ') (e_ι : η' otimesₘ θ' …
（共 32 条，此处仅展示前 30 条）
-/
theorem associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensorμ (X₁ ⊗ X₂) X₃ (Y₁ ⊗ Y₂) Y₃ ≫
        (tensorμ X₁ X₂ Y₁ Y₂ ▷ (X₃ ⊗ Y₃)) ≫ (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      ((α_ X₁ X₂ X₃).hom ⊗ₘ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensorμ X₁ (X₂ ⊗ X₃) Y₁ (Y₂ ⊗ Y₃) ≫ ((X₁ ⊗ Y₁) ◁ tensorμ X₂ X₃ Y₂ Y₃) := by
  dsimp only [tensorμ]
  calc
    _ = 𝟙 _ ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
      X₁ ◁ ((X₂ ⊗ Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ ⊗ X₃)) ▷ Y₃ ⊗≫ 𝟙 _ := by
          rw [braiding_tensor_right_hom]; monoidal
    _ = _ := by rw [whisker_exchange, braiding_tensor_left_hom]; monoidal

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.MonoidalCategory`。
形式化陈述：tensor : C × C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorμ_comp_μ_tensorHom_μ_comp_μ (F : C ⥤ D) [F.LaxBraided] (W X Y Z : C) :
    tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) ≫
      (μ F W Y ⊗ₘ μ F X Z) ≫ μ F (W ⊗ Y) (X ⊗ Z) =
      (μ F W X ⊗ₘ μ F Y Z) ≫ μ F (W ⊗ X) (Y ⊗ Z) ≫ F.map (tensorμ W X Y Z) := by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_comp_μ,
    associator_inv_naturality_left_assoc, ← pentagon_inv_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, μ_whiskerRight_comp_μ,
    whiskerLeft_hom_inv_assoc, Iso.inv_hom_id_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, μ_natural_left_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Functor.LaxBraided.braided,
    MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right, whiskerLeft_μ_comp_μ_assoc,
    comp_whiskerRight_assoc, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, pentagon_inv_assoc, μ_natural_left_assoc, μ_natural_left_assoc,
    Iso.hom_inv_id_assoc, ← associator_inv_naturality_left_assoc, μ_whiskerRight_comp_μ_assoc,
    Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
  simp only [← Functor.map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

end Tensor

end MonoidalCategory

@[reassoc]
/-
**CategoryTheory.SymmetricCategory.tensor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SymmetricCategory.tensorμ_braid_swap
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    (X Y : C) :
    tensorμ X X Y Y ≫ (β_ (X ⊗ Y) (X ⊗ Y)).hom =
      ((β_ X X).hom ⊗ₘ (β_ Y Y).hom) ≫ tensorμ X X Y Y := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X, tensorHom_def]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory Cᵒᵖ where
  braiding X Y := (β_ Y.unop X.unop).op
  braiding_naturality_right X {_ _} f := Quiver.Hom.unop_inj <| by simp
  braiding_naturality_left {_ _} f Z := Quiver.Hom.unop_inj <| by simp

section OppositeLemmas

open Opposite

/-
**CategoryTheory.op_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : C), (β_ X Y).op = β_ (Opposite.op Y) (Opposite.op X)
参数：X Y : C；β_ X Y；Opposite.op Y；Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_braiding (X Y : C) : (β_ X Y).op = β_ (op Y) (op X) := rfl
/-
**CategoryTheory.unop_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : Cᵒᵖ), (β_ X Y).unop = β_ (Opposite.unop Y) (Opposite.unop X)
参数：X Y : Cᵒᵖ；β_ X Y；Opposite.unop Y；Opposite.unop X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_braiding (X Y : Cᵒᵖ) : (β_ X Y).unop = β_ (unop Y) (unop X) := rfl
/-
**CategoryTheory.op_hom_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : C), (β_ X Y).hom.op = (β_ (Opposite.op Y) (Opposite.op X)).hom
参数：X Y : C；β_ X Y；β_ (Opposite.op Y) (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_hom_braiding (X Y : C) : (β_ X Y).hom.op = (β_ (op Y) (op X)).hom := rfl
/-
**CategoryTheory.unop_hom_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : Cᵒᵖ),   (β_ X Y).hom.unop = (β_ (Opposite.unop Y) (Opposite.unop X)).hom
参数：X Y : Cᵒᵖ；β_ X Y；β_ (Opposite.unop Y) (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_hom_braiding (X Y : Cᵒᵖ) : (β_ X Y).hom.unop = (β_ (unop Y) (unop X)).hom := rfl
/-
**CategoryTheory.op_inv_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : C), (β_ X Y).inv.op = (β_ (Opposite.op Y) (Opposite.op X)).inv
参数：X Y : C；β_ X Y；β_ (Opposite.op Y) (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_inv_braiding (X Y : C) : (β_ X Y).inv.op = (β_ (op Y) (op X)).inv := rfl
/-
**CategoryTheory.unop_inv_braiding** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : Cᵒᵖ),   (β_ X Y).inv.unop = (β_ (Opposite.unop Y) (Opposite.unop X)).inv
参数：X Y : Cᵒᵖ；β_ X Y；β_ (Opposite.unop Y) (Opposite.unop X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_inv_braiding (X Y : Cᵒᵖ) : (β_ X Y).inv.unop = (β_ (unop Y) (unop X)).inv := rfl

end OppositeLemmas

namespace MonoidalOpposite

/-
**CategoryTheory.MonoidalOpposite.instBraiding** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.MonoidalOpposite`。
形式化陈述：instBraiding : BraidedCategory Cᴹᵒᵖ where braiding X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBraiding : BraidedCategory Cᴹᵒᵖ where
  braiding X Y := (β_ Y.unmop X.unmop).mop
  braiding_naturality_right X {_ _} f := Quiver.Hom.unmop_inj <| by simp
  braiding_naturality_left {_ _} f Z := Quiver.Hom.unmop_inj <| by simp

section MonoidalOppositeLemmas

/-
**CategoryTheory.MonoidalOpposite.mop_braiding** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.MonoidalOpposite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : C), (β_ X Y).mop = β_ { unmop := Y } { unmop := X }
参数：X Y : C；β_ X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_braiding (X Y : C) : (β_ X Y).mop = β_ (mop Y) (mop X) := rfl
/-
**CategoryTheory.MonoidalOpposite.unmop_braiding** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalOpposite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : Cᴹᵒᵖ), (β_ X Y).unmop = β_ Y.unmop X.unmop
参数：X Y : Cᴹᵒᵖ；β_ X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmop_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).unmop = β_ (unmop Y) (unmop X) := rfl
/-
**CategoryTheory.MonoidalOpposite.mop_hom_braiding** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalOpposite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : C), (β_ X Y).hom.mop = (β_ { unmop := Y } { unmop := X }).hom
参数：X Y : C；β_ X Y；β_ { unmop := Y } { unmop := X }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_hom_braiding (X Y : C) : (β_ X Y).hom.mop = (β_ (mop Y) (mop X)).hom := rfl
@[simp]
/-
**CategoryTheory.MonoidalOpposite.unmop_hom_braiding** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MonoidalOpposite`。
形式化陈述：unmop_hom_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).hom.unmop = (β_ (unmop Y) (unmo
p X)).hom
参数：X Y : Cᴹᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unmop_hom_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).hom.unmop = (β_ (unmop Y) (unmop X)).hom := rfl
/-
**CategoryTheory.MonoidalOpposite.mop_inv_braiding** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.MonoidalOpposite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] (X 
Y : C), (β_ X Y).inv.mop = (β_ { unmop := Y } { unmop := X }).inv
参数：X Y : C；β_ X Y；β_ { unmop := Y } { unmop := X }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mop_inv_braiding (X Y : C) : (β_ X Y).inv.mop = (β_ (mop Y) (mop X)).inv := rfl
@[simp]
/-
**CategoryTheory.MonoidalOpposite.unmop_inv_braiding** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MonoidalOpposite`。
形式化陈述：unmop_inv_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).inv.unmop = (β_ (unmop Y) (unmo
p X)).inv
参数：X Y : Cᴹᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unmop_inv_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).inv.unmop = (β_ (unmop Y) (unmop X)).inv := rfl

end MonoidalOppositeLemmas

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (mopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y ↦ β_ (mop X) (mop Y)
      associativity := fun X Y Z ↦ by simp [← yang_baxter_assoc] }
/-
**CategoryTheory.MonoidalOpposite.mopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mopFunctor_ε : ε (mopFunctor C) = 𝟙 _ := rfl
/-
**CategoryTheory.MonoidalOpposite.mopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mopFunctor_η : η (mopFunctor C) = 𝟙 _ := rfl
/-
**CategoryTheory.MonoidalOpposite.mopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mopFunctor_μ (X Y : C) : μ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).hom := rfl
/-
**CategoryTheory.MonoidalOpposite.mopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mopFunctor_δ (X Y : C) : δ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (unmopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y ↦ β_ (unmop X) (unmop Y)
      associativity := fun X Y Z ↦ by simp [← yang_baxter_assoc] }
/-
**CategoryTheory.MonoidalOpposite.unmopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmopFunctor_ε : ε (unmopFunctor C) = 𝟙 _ := rfl
/-
**CategoryTheory.MonoidalOpposite.unmopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmopFunctor_η : η (unmopFunctor C) = 𝟙 _ := rfl
/-
**CategoryTheory.MonoidalOpposite.unmopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmopFunctor_μ (X Y : Cᴹᵒᵖ) :
    μ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).hom := rfl
/-
**CategoryTheory.MonoidalOpposite.unmopFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MonoidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unmopFunctor_δ (X Y : Cᴹᵒᵖ) :
    δ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).inv := rfl

/-- The identity functor on `C`, viewed as a functor from `C` to its
monoidal opposite, upgraded to a braided functor. -/
/-
**CategoryTheory.MonoidalOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor on `C`, viewed as a functor from `C` to its
monoidal opposite, upgraded to a braided functor.
-/
instance : (mopFunctor C).Braided where

/-- The identity functor on `C`, viewed as a functor from the
monoidal opposite of `C` to `C`, upgraded to a braided functor. -/
/-
**CategoryTheory.MonoidalOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
oidalOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor on `C`, viewed as a functor from the
monoidal opposite of `C` to `C`, upgraded to a braided functor.
-/
instance : (unmopFunctor C).Braided where

end MonoidalOpposite

variable (C)

/-- The braided monoidal category obtained from `C` by replacing its braiding
`β_ X Y : X ⊗ Y ≅ Y ⊗ X` with the inverse `(β_ Y X)⁻¹ : X ⊗ Y ≅ Y ⊗ X`.
This corresponds to the automorphism of the braid group swapping
over-crossings and under-crossings. -/
/-
**CategoryTheory.reverseBraiding** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：reverseBraiding : BraidedCategory C where braiding X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braided monoidal category obtained from `C` by replacing its braiding
`β_ X Y : X ⊗ Y ≅ Y ⊗ X` with the inverse `(β_ Y X)⁻¹ : X ⊗ Y ≅ Y ⊗ X`.
This corresponds to the automorphism of the braid group swapping
over-crossings and under-crossings.
-/
abbrev reverseBraiding : BraidedCategory C where
  braiding X Y := (β_ Y X).symm
  braiding_naturality_right X {_ _} f := by simp
  braiding_naturality_left {_ _} f Z := by simp
/-
**CategoryTheory.SymmetricCategory.reverseBraiding_eq** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.SymmetricCategory`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [i : CategoryTheory.SymmetricCategory C], Categ
oryTheory.reverseBraiding C = i.toBraidedCategory
参数：C : Type u₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.SymmetricCategory.braiding_swap_eq_inv_braiding`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Mon
oidalCategory C]   [inst_2 : CategoryTheory.Symmetri…
-/
lemma SymmetricCategory.reverseBraiding_eq (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [i : SymmetricCategory C] :
    reverseBraiding C = i.toBraidedCategory := by
  dsimp only [reverseBraiding]
  congr
  funext X Y
  exact Iso.ext (braiding_swap_eq_inv_braiding Y X).symm

/-- The identity functor from `C` to `C`, where the codomain is given the
reversed braiding, upgraded to a braided functor. -/
@[instance_reducible]
/-
**CategoryTheory.SymmetricCategory.equivReverseBraiding** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SymmetricCategory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.Symmetri
cCategory C] → (CategoryTheory.Functor.id C).Braided
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor from `C` to `C`, where the codomain is given the
reversed braiding, upgraded to a braided functor.
-/
def SymmetricCategory.equivReverseBraiding (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [SymmetricCategory C] :=
  @Functor.Braided.mk C _ _ _ C _ _ (reverseBraiding C) (𝟭 C) _ <| by
    simp +instances [reverseBraiding, braiding_swap_eq_inv_braiding]

end CategoryTheory

