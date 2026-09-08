/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda

/-!
# Enriched ordinary categories

If `V` is a monoidal category, a `V`-enriched category `C` does not need
to be a category. However, when we have both `Category C` and `EnrichedCategory V C`,
we may require that the type of morphisms `X ⟶ Y` in `C` identify to
`𝟙_ V ⟶ EnrichedCategory.Hom X Y`. This data shall be packaged in the
typeclass `EnrichedOrdinaryCategory V C`.

In particular, if `C` is a `V`-enriched category, it is shown that
the "underlying" category `ForgetEnrichment V C` is equipped with a
`EnrichedOrdinaryCategory V C` instance.

Simplicial categories are implemented in `AlgebraicTopology.SimplicialCategory.Basic`
using an abbreviation for `EnrichedOrdinaryCategory SSet C`.

-/

@[expose] public section

universe v' v v'' u u' u''

open CategoryTheory Category MonoidalCategory Opposite

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C]

/-- An enriched ordinary category is a category `C` that is also enriched
over a category `V` in such a way that morphisms `X ⟶ Y` in `C` identify
to morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V`. -/
/-
**CategoryTheory.EnrichedOrdinaryCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheo
ry`。
形式化陈述：EnrichedOrdinaryCategory extends EnrichedCategory V C where /-- morphisms 
`X ⟶ Y` in the category identify morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V` -/ homEqui
v {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y)) homEquiv_id (X : C) : homEquiv (𝟙 X)
 = eId V X
参数：X ⟶[V] Y。
继承自：EnrichedCategory V C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An enriched ordinary category is a category `C` that is also enriched
over a category `V` in such a way that morphisms `X ⟶ Y` in `C` identify
to morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V`.
-/
class EnrichedOrdinaryCategory extends EnrichedCategory V C where
  /-- morphisms `X ⟶ Y` in the category identify morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V` -/
  homEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
  homEquiv_id (X : C) : homEquiv (𝟙 X) = eId V X := by cat_disch
  homEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv (f ≫ g) = (λ_ _).inv ≫ (homEquiv f ⊗ₘ homEquiv g) ≫
      eComp V X Y Z := by cat_disch

variable [EnrichedOrdinaryCategory V C] {C}

/-- The bijection `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))` given by a
`EnrichedOrdinaryCategory` instance. -/
/-
**CategoryTheory.eHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eHomEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))` given by a
`EnrichedOrdinaryCategory` instance.
-/
def eHomEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y)) :=
  EnrichedOrdinaryCategory.homEquiv

@[simp]
/-
**CategoryTheory.eHomEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = eId V X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnrichedOrdinaryCategory.homEquiv_id`：∀ {V : Type u'} {in
st : CategoryTheory.Category.{v', u'} V} {inst_1 : CategoryTheory.MonoidalCatego
ry V} {C : Type u}   {inst_2 : CategoryTh…
-/
lemma eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = eId V X :=
  EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]
/-
**CategoryTheory.eHomEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : eHomEquiv V (f ≫ g) =
 (fun_ _).inv ≫ (eHomEquiv V f otimesₘ eHomEquiv V g) ≫ eComp V X Y Z
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnrichedOrdinaryCategory.homEquiv_comp`：∀ {V : Type u'} {
inst : CategoryTheory.Category.{v', u'} V} {inst_1 : CategoryTheory.MonoidalCate
gory V} {C : Type u}   {inst_2 : CategoryTh…
-/
lemma eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = (λ_ _).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V g) ≫ eComp V X Y Z :=
  EnrichedOrdinaryCategory.homEquiv_comp _ _

/-- The morphism `(X' ⟶[V] Y) ⟶ (X ⟶[V] Y)` induced by a morphism `X ⟶ X'`. -/
/-
**CategoryTheory.eHomWhiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y : C) : (X' ⟶[V] Y) ⟶ (X ⟶[V] Y
)
参数：f : X ⟶ X'；Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(X' ⟶[V] Y) ⟶ (X ⟶[V] Y)` induced by a morphism `X ⟶ X'`.
-/
def eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    (X' ⟶[V] Y) ⟶ (X ⟶[V] Y) :=
  (λ_ _).inv ≫ eHomEquiv V f ▷ _ ≫ eComp V X X' Y

@[simp]
/-
**CategoryTheory.eHomWhiskerRight_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eHomWhiskerRight_id (X Y : C) : eHomWhiskerRight V (𝟙 X) Y = 𝟙 _
参数：X Y : C。
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
· 使用引理 `CategoryTheory.eHomEquiv_id`：eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = 
eId V X
· 使用定理 `CategoryTheory.e_id_comp`：e_id_comp (X Y : C) : (fun_ (X ⟶[V] Y)).inv ≫ 
eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eHomWhiskerRight_id (X Y : C) : eHomWhiskerRight V (𝟙 X) Y = 𝟙 _ := by
  simp [eHomWhiskerRight]

@[simp, reassoc]
/-
**CategoryTheory.eHomWhiskerRight_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：eHomWhiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) 
: eHomWhiskerRight V (f ≫ f') Y = eHomWhiskerRight V f' Y ≫ eHomWhiskerRight V f
 Y
参数：f : X ⟶ X'；f' : X' ⟶ X''；Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.eHomEquiv_comp`：eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g
 : Y ⟶ Z) : eHomEquiv V (f ≫ g) = (fun_ _).inv ≫ (eHomEquiv V f otimesₘ eHomEqui
v V g) ≫ eComp V X …
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.e_assoc'`：e_assoc' (W X Y Z : C) : (α_ _ _ _).hom ≫ _ ◁ e
Comp V X Y Z ≫ eComp V W X Z = eComp V W X Y ▷ _ ≫ eComp V W Y Z
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight_assoc`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
(X Y : C) {Z : C}   (h : CategoryTheory.Mon…
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mon
oidalCategory C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_left_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
MonoidalCategory C] {X X' : C}   (f : X ⟶ X') (Y Z : C) {Z…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
-/
lemma eHomWhiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    eHomWhiskerRight V (f ≫ f') Y = eHomWhiskerRight V f' Y ≫ eHomWhiskerRight V f Y := by
  dsimp [eHomWhiskerRight]
  rw [assoc, assoc, eHomEquiv_comp, comp_whiskerRight_assoc, comp_whiskerRight_assoc, ← e_assoc',
    tensorHom_def', comp_whiskerRight_assoc, id_whiskerLeft, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight_assoc,
    comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
    ← associator_inv_naturality_left_assoc, Iso.inv_hom_id_assoc,
    ← whisker_exchange_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc]

/-- Whiskering commutes with the enriched composition. -/
@[reassoc]
/-
**CategoryTheory.eComp_eHomWhiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y`。
形式化陈述：eComp_eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y Z : C) : eComp V X' Y Z 
≫ eHomWhiskerRight V f Z = eHomWhiskerRight V f Y ▷ _ ≫ eComp V X Y Z
参数：f : X ⟶ X'；Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.e_assoc'`：e_assoc' (W X Y Z : C) : (α_ _ _ _).hom ≫ _ ◁ e
Comp V X Y Z ≫ eComp V W X Z = eComp V W X Y ▷ _ ≫ eComp V W Y Z
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight`：leftUnitor_
inv_whiskerRight (X Y : C) : (fun_ X).inv ▷ Y = (fun_ (X otimes Y)).inv ≫ (α_ (𝟙
_ C) X Y).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Whiskering commutes with the enriched composition.
-/
lemma eComp_eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y Z : C) :
    eComp V X' Y Z ≫ eHomWhiskerRight V f Z =
      eHomWhiskerRight V f Y ▷ _ ≫ eComp V X Y Z := by
  dsimp [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  simp [e_assoc']

/-- The morphism `(X ⟶[V] Y) ⟶ (X ⟶[V] Y')` induced by a morphism `Y ⟶ Y'`. -/
/-
**CategoryTheory.eHomWhiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eHomWhiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') : (X ⟶[V] Y) ⟶ (X ⟶[V] Y')
参数：X : C；g : Y ⟶ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(X ⟶[V] Y) ⟶ (X ⟶[V] Y')` induced by a morphism `Y ⟶ Y'`.
-/
def eHomWhiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (X ⟶[V] Y) ⟶ (X ⟶[V] Y') :=
  (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V X Y Y'

@[simp]
/-
**CategoryTheory.eHomWhiskerLeft_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eHomWhiskerLeft_id (X Y : C) : eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.eHomEquiv_id`：eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = 
eId V X
· 使用定理 `CategoryTheory.e_comp_id`：e_comp_id (X Y : C) : (ρ_ (X ⟶[V] Y)).inv ≫ _ 
◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eHomWhiskerLeft_id (X Y : C) : eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _ := by
  simp [eHomWhiskerLeft]

@[simp, reassoc]
/-
**CategoryTheory.eHomWhiskerLeft_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：eHomWhiskerLeft_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
 eHomWhiskerLeft V X (g ≫ g') = eHomWhiskerLeft V X g ≫ eHomWhiskerLeft V X g'
参数：X : C；g : Y ⟶ Y'；g' : Y' ⟶ Y''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.eHomEquiv_comp`：eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g
 : Y ⟶ Z) : eHomEquiv V (f ≫ g) = (fun_ _).inv ≫ (eHomEquiv V f otimesₘ eHomEqui
v V g) ≫ eComp V X …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.e_assoc`：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V
 W X Y ▷ _ ≫ eComp V W Y Z = _ ◁ eComp V X Y Z ≫ eComp V W X Z
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_assoc`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoida
lCategory C] (X Y : C) {Z : C}   (h : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mon
oidalCategory C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
-/
lemma eHomWhiskerLeft_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    eHomWhiskerLeft V X (g ≫ g') = eHomWhiskerLeft V X g ≫ eHomWhiskerLeft V X g' := by
  dsimp [eHomWhiskerLeft]
  rw [assoc, assoc, eHomEquiv_comp, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, ← e_assoc, tensorHom_def,
    MonoidalCategory.whiskerRight_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_rightUnitor_assoc, whiskerLeft_rightUnitor_inv_assoc,
    triangle_assoc_comp_left_inv_assoc, MonoidalCategory.whiskerRight_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc]

/-- Whiskering commutes with the enriched composition. -/
@[reassoc]
/-
**CategoryTheory.eComp_eHomWhiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：eComp_eHomWhiskerLeft (X Y : C) {Z Z' : C} (g : Z ⟶ Z') : eComp V X Y Z ≫ 
eHomWhiskerLeft V X g = _ ◁ eHomWhiskerLeft V Y g ≫ eComp V X Y Z'
参数：X Y : C；g : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mono
idalCategory C] {X X' : C}   (f : X ⟶ X') {Z : C}   (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.e_assoc`：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V
 W X Y ▷ _ ≫ eComp V W Y Z = _ ◁ eComp V X Y Z ≫ eComp V W X Z
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor_inv`：whiskerLeft
_rightUnitor_inv (X Y : C) : X ◁ (ρ_ Y).inv = (ρ_ (X otimes Y)).inv ≫ (α_ X Y (𝟙
_ C)).hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Whiskering commutes with the enriched composition.
-/
lemma eComp_eHomWhiskerLeft (X Y : C) {Z Z' : C} (g : Z ⟶ Z') :
    eComp V X Y Z ≫ eHomWhiskerLeft V X g =
      _ ◁ eHomWhiskerLeft V Y g ≫ eComp V X Y Z' := by
  dsimp [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
  simp

/-- Given an isomorphism `α : Y ≅ Y₁` in C, the enriched composition map
`eComp V X Y Z : (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z)` factors through the `V`
object `(X ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z)` via the map defined by whiskering in the
middle with `α.hom` and `α.inv`. -/
@[reassoc]
/-
**CategoryTheory.eHom_whisker_cancel** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：eHom_whisker_cancel {X Y Y₁ Z : C} (α : Y ≅ Y₁) : eHomWhiskerLeft V X α.ho
m ▷ _ ≫ _ ◁ eHomWhiskerRight V α.inv Z ≫ eComp V X Y₁ Z = eComp V X Y Z
参数：α : Y ≅ Y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc_symm`：whisker_assoc_symm (
X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) : X ◁ f ▷ Z = (α_ X Y Z).inv ≫ (X ◁ f) ▷ 
Z ≫ (α_ X Y' Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.e_assoc'`：e_assoc' (W X Y Z : C) : (α_ _ _ _).hom ≫ _ ◁ e
Comp V X Y Z ≫ eComp V W X Z = eComp V W X Y ▷ _ ≫ eComp V W Y Z
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc_comp_left_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `CategoryTheory.eHomWhiskerLeft_id`：eHomWhiskerLeft_id (X Y : C) : eHomWh
iskerLeft V X (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an isomorphism `α : Y ≅ Y₁` in C, the enriched composition map
`eComp V X Y Z : (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z)` factors through the `V`
object `(X ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z)` via the map defined by whiskering in the
middle with `α.hom` and `α.inv`.
-/
lemma eHom_whisker_cancel {X Y Y₁ Z : C} (α : Y ≅ Y₁) :
    eHomWhiskerLeft V X α.hom ▷ _ ≫ _ ◁ eHomWhiskerRight V α.inv Z ≫
      eComp V X Y₁ Z = eComp V X Y Z := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [MonoidalCategory.whiskerLeft_comp_assoc, whisker_assoc_symm,
    triangle_assoc_comp_left_inv_assoc, e_assoc', assoc]
  simp only [← comp_whiskerRight_assoc]
  change (eHomWhiskerLeft V X α.hom ≫ eHomWhiskerLeft V X α.inv) ▷ _ ≫ _ = _
  simp [← eHomWhiskerLeft_comp]

@[reassoc]
/-
**CategoryTheory.eHom_whisker_cancel_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：eHom_whisker_cancel_inv {X Y Y₁ Z : C} (α : Y ≅ Y₁) : eHomWhiskerLeft V X 
α.inv ▷ _ ≫ _ ◁ eHomWhiskerRight V α.hom Z ≫ eComp V X Y Z = eComp V X Y₁ Z
参数：α : Y ≅ Y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.eHom_whisker_cancel`：eHom_whisker_cancel {X Y Y₁ Z : C} (
α : Y ≅ Y₁) : eHomWhiskerLeft V X α.hom ▷ _ ≫ _ ◁ eHomWhiskerRight V α.inv Z ≫ e
Comp V X Y₁ Z = eComp V …
-/
lemma eHom_whisker_cancel_inv {X Y Y₁ Z : C} (α : Y ≅ Y₁) :
    eHomWhiskerLeft V X α.inv ▷ _ ≫ _ ◁ eHomWhiskerRight V α.hom Z ≫
      eComp V X Y Z = eComp V X Y₁ Z := eHom_whisker_cancel V α.symm

@[reassoc]
/-
**CategoryTheory.eHom_whisker_exchange** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：eHom_whisker_exchange {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') : eHomWhis
kerLeft V X' g ≫ eHomWhiskerRight V f Y' = eHomWhiskerRight V f Y ≫ eHomWhiskerL
eft V X g
参数：f : X ⟶ X'；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.e_assoc`：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V
 W X Y ▷ _ ≫ eComp V W Y Z = _ ◁ eComp V X Y Z ≫ eComp V W X Z
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_tensor_inv_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalC
ategory C] (X Y : C) {Z : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_left_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
MonoidalCategory C] {X X' : C}   (f : X ⟶ X') (Y Z : C) {Z…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma eHom_whisker_exchange {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    eHomWhiskerLeft V X' g ≫ eHomWhiskerRight V f Y' =
      eHomWhiskerRight V f Y ≫ eHomWhiskerLeft V X g := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  rw [assoc, assoc, assoc, assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, ← e_assoc, leftUnitor_tensor_inv_assoc,
    associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, whisker_exchange_assoc,
    MonoidalCategory.whiskerRight_id_assoc, assoc, Iso.inv_hom_id_assoc,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc]

attribute [local simp] eHom_whisker_exchange

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ V` which sends `X : Cᵒᵖ` and `Y : C` to `X ⟶[V] Y`. -/
@[simps]
/-
**CategoryTheory.eHomFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：eHomFunctor : Cᵒᵖ ⥤ C ⥤ V where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bifunctor `Cᵒᵖ ⥤ C ⥤ V` which sends `X : Cᵒᵖ` and `Y : C` to `X ⟶[V] Y`.
-/
def eHomFunctor : Cᵒᵖ ⥤ C ⥤ V where
  obj X :=
    { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => eHomWhiskerLeft V X.unop φ }
  map φ :=
    { app := fun Y => eHomWhiskerRight V φ.unop Y }
/-
**CategoryTheory.ForgetEnrichment.enrichedOrdinaryCategory** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ForgetEnrichment`。
形式化陈述：(V : Type u') →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       {D : Type u_1} →         [inst_2 
: CategoryTheory.EnrichedCategory V D] →           CategoryTheory.EnrichedOrdina
ryCategory V (CategoryTheory.ForgetEnrichment V D)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
instance ForgetEnrichment.enrichedOrdinaryCategory {D : Type*} [EnrichedCategory V D] :
    EnrichedOrdinaryCategory V (ForgetEnrichment V D) where
  toEnrichedCategory := inferInstanceAs (EnrichedCategory V D)
  homEquiv := Equiv.refl _
  homEquiv_id _ := Category.id_comp _
  homEquiv_comp _ _ := Category.assoc _ _ _

/-- If `D` is already an enriched ordinary category, there is a canonical functor from `D` to
`ForgetEnrichment V D`. -/
@[simps]
/-
**CategoryTheory.ForgetEnrichment.equivInverse** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ForgetEnrichment`。
形式化陈述：(V : Type u') →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       (D : Type u'') →         [inst_2 
: CategoryTheory.Category.{v'', u''} D] →           [inst_3 : CategoryTheory.Enr
ichedOrdinaryCategory V D] →             CategoryTheory.Functor D (CategoryTheor
y.ForgetEnrichment V D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is already an enriched ordinary category, there is a canonical functor fr
om `D` to
`ForgetEnrichment V D`.
-/
def ForgetEnrichment.equivInverse (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    D ⥤ ForgetEnrichment V D where
  obj X := .of V X
  map f := ForgetEnrichment.homOf V (eHomEquiv V f)
  map_comp f g := by simp [eHomEquiv_comp]

/-- If `D` is already an enriched ordinary category, there is a canonical functor from
`ForgetEnrichment V D` to `D`. -/
@[simps]
/-
**CategoryTheory.ForgetEnrichment.equivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ForgetEnrichment`。
形式化陈述：(V : Type u') →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       (D : Type u'') →         [inst_2 
: CategoryTheory.Category.{v'', u''} D] →           [inst_3 : CategoryTheory.Enr
ichedOrdinaryCategory V D] →             CategoryTheory.Functor (CategoryTheory.
ForgetEnrichment V D) D
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `D` is already an enriched ordinary category, there is a canonical functor fr
om
`ForgetEnrichment V D` to `D`.
-/
def ForgetEnrichment.equivFunctor (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ⥤ D where
  obj X := ForgetEnrichment.to V X
  map f := (eHomEquiv V).symm (ForgetEnrichment.homTo V f)
  map_id X := by rw [ForgetEnrichment.homTo_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {X} {Y} {Z} f g := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V Z))
    (by simp [eHomEquiv_comp])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `D` is already an enriched ordinary category, it is equivalent to `ForgetEnrichment V D`. -/
@[simps]
/-
**CategoryTheory.ForgetEnrichment.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ForgetEnrichment`。
形式化陈述：(V : Type u') →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       {D : Type u''} →         [inst_2 
: CategoryTheory.Category.{v'', u''} D] →           [inst_3 : CategoryTheory.Enr
ichedOrdinaryCategory V D] → CategoryTheory.ForgetEnrichment V D ≌ D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is already an enriched ordinary category, it is equivalent to `ForgetEnri
chment V D`.
-/
def ForgetEnrichment.equiv {D : Type u''} [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ≌ D where
  functor := equivFunctor V D
  inverse := equivInverse V D
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
  functor_unitIso_comp X := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V X)) (by simp)

/-- enriched coyoneda functor `(X ⟶[V] _) : C ⥤ V`. -/
/-
**CategoryTheory.eCoyoneda** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：eCoyoneda (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
enriched coyoneda functor `(X ⟶[V] _) : C ⥤ V`.
-/
abbrev eCoyoneda (X : C) := (eHomFunctor V C).obj (op X)

section TransportEnrichment

variable {V} {W : Type u''} [Category.{v''} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  (C)

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (TransportEnrichment F C) := inferInstanceAs (Category C)

/-- If `C` is an ordinary enriched category, the category structure on `TransportEnrichment F C`
is trivially equivalent to the one on `C` itself. -/
/-
**CategoryTheory.TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.TransportEnrichment`。
形式化陈述：{V : Type u'} →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       (C : Type u) →         [inst_2 : 
CategoryTheory.Category.{v, u} C] →           {W : Type u''} →             [inst
_3 : CategoryTheory.Category.{v'', u''} W] →               [inst_4 : CategoryThe
ory.MonoidalCategory W] →                 (F : CategoryTheory.Functor V W) → [in
st_5 : F.LaxMonoidal] → CategoryTheory.TransportEnrichment F C ≌ C
参数：C : Type u；F : CategoryTheory.Functor V W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is an ordinary enriched category, the category structure on `TransportEnr
ichment F C`
is trivially equivalent to the one on `C` itself.
-/
def TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv : TransportEnrichment F C ≌ C :=
  Equivalence.refl

open EnrichedCategory

set_option backward.isDefEq.respectTransparency false in
/-- If for a lax monoidal functor `F : V ⥤ W` the canonical function
`(𝟙_ V ⟶ v) → (𝟙_ W ⟶ F.obj v)` is bijective, and `C` is an enriched ordinary category on `V`,
then `F` induces the structure of a `W`-enriched ordinary category on `TransportEnrichment F C`,
i.e. on the same underlying category `C`. -/
@[instance_reducible]
/-
**CategoryTheory.TransportEnrichment.enrichedOrdinaryCategory** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.TransportEnrichment`。
形式化陈述：{V : Type u'} →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       (C : Type u) →         [inst_2 : 
CategoryTheory.Category.{v, u} C] →           [CategoryTheory.EnrichedOrdinaryCa
tegory V C] →             {W : Type u''} →               [inst_4 : CategoryTheor
y.Category.{v'', u''} W] →                 [inst_5 : CategoryTheory.MonoidalCate
gory W] →                   (F : CategoryTheory.Functor V W) →                  
   [inst_6 : F.LaxMonoidal] →                       (e :                        
   (v : V) →                             (CategoryTheory.MonoidalCategoryStruct.
tensorUnit V ⟶ v) ≃                               (CategoryTheory.MonoidalCatego
ryStruct.tensorUnit W ⟶ F.obj v)) →                         (∀ (v : V) (f : Cate
goryTheory.MonoidalCategoryStruct.tensorUnit V ⟶ v),                            
 (e v) f =                               CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.Functor.LaxMonoidal.ε F) (F.map f)) →                           Cate
goryTheory.EnrichedOrdinaryCategory W (CategoryTheory.TransportEnrichment F C)
参数：C : Type u；F : CategoryTheory.Functor V W；e :                           (v : 
V) →                             (CategoryTheory.MonoidalCategoryStruct.tensorUn
it V ⟶ v) ≃                               (CategoryTheory.MonoidalCategoryStruct
.tensorUnit W ⟶ F.obj v)；∀ (v : V) (f : CategoryTheory.MonoidalCategoryStruct.te
nsorUnit V ⟶ v),                             (e v) f =                          
     CategoryTheory.CategoryStruct.comp (CategoryTheory.Functor.LaxMonoidal.ε F)
 (F.map f)；CategoryTheory.TransportEnrichment F C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If for a lax monoidal functor `F : V ⥤ W` the canonical function
`(𝟙_ V ⟶ v) → (𝟙_ W ⟶ F.obj v)` is bijective, and `C` is an enriched ordinary ca
tegory on `V`,
then `F` induces the structure of a `W`-enriched ordinary category on `Transport
Enrichment F C`,
i.e. on the same underlying category `C`.
-/
def TransportEnrichment.enrichedOrdinaryCategory
    (e : ∀ v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
    (h : ∀ v : V, ∀ f : 𝟙_ V ⟶ v, e v f = Functor.LaxMonoidal.ε F ≫ F.map f) :
    EnrichedOrdinaryCategory W (TransportEnrichment F C) where
  homEquiv {X Y} := (eHomEquiv V (C := C)).trans (e (Hom (C := C) X Y))
  homEquiv_id {X} := by simpa using! h _ (eId V _)
  homEquiv_comp f g := by
    dsimp +instances [instEnrichedCategoryTransportEnrichment]
    rw [h, h, h, ← tensorHom_comp_tensorHom_assoc, eComp_eq, tensorHom_def_assoc,
      whiskerRight_id_assoc, unitors_inv_equal, Iso.inv_hom_id_assoc,
      Functor.LaxMonoidal.μ_natural_assoc, Functor.LaxMonoidal.right_unitality_inv_assoc,
      eHomEquiv_comp, ← F.map_comp, ← F.map_comp, unitors_inv_equal]

section Equiv

variable {W : Type u''} [Category.{v''} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  (D : Type u) [EnrichedCategory V D]
  (e : ∀ v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
  (h : ∀ (v : V) (f : 𝟙_ V ⟶ v), (e v) f = Functor.LaxMonoidal.ε F ≫ F.map f)

set_option backward.isDefEq.respectTransparency false in
/-- The functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`. -/
@[simps]
/-
**CategoryTheory.TransportEnrichment.forgetEnrichmentEquivFunctor** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.TransportEnrichment`。
形式化陈述：{V : Type u'} →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       {W : Type u''} →         [inst_2 
: CategoryTheory.Category.{v'', u''} W] →           [inst_3 : CategoryTheory.Mon
oidalCategory W] →             (F : CategoryTheory.Functor V W) →               
[inst_4 : F.LaxMonoidal] →                 (D : Type u) →                   [ins
t_5 : CategoryTheory.EnrichedCategory V D] →                     (e :           
              (v : V) →                           (CategoryTheory.MonoidalCatego
ryStruct.tensorUnit V ⟶ v) ≃                             (CategoryTheory.Monoida
lCategoryStruct.tensorUnit W ⟶ F.obj v)) →                       (∀ (v : V) (f :
 CategoryTheory.MonoidalCategoryStruct.tensorUnit V ⟶ v),                       
    (e v) f =                             CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Functor.LaxMonoidal.ε F) (F.map f)) →                         Categ
oryTheory.Functor                           (CategoryTheory.TransportEnrichment 
F (CategoryTheory.ForgetEnrichment V D))                           (CategoryTheo
ry.ForgetEnrichment W (CategoryTheory.TransportEnrichment F D))
参数：F : CategoryTheory.Functor V W；D : Type u；e :                         (v : V)
 →                           (CategoryTheory.MonoidalCategoryStruct.tensorUnit V
 ⟶ v) ≃                             (CategoryTheory.MonoidalCategoryStruct.tenso
rUnit W ⟶ F.obj v)；∀ (v : V) (f : CategoryTheory.MonoidalCategoryStruct.tensorUn
it V ⟶ v),                           (e v) f =                             Categ
oryTheory.CategoryStruct.comp (CategoryTheory.Functor.LaxMonoidal.ε F) (F.map f)
；CategoryTheory.TransportEnrichment F (CategoryTheory.ForgetEnrichment V D)；Cate
goryTheory.ForgetEnrichment W (CategoryTheory.TransportEnrichment F D)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`.
-/
def TransportEnrichment.forgetEnrichmentEquivFunctor :
    TransportEnrichment F (ForgetEnrichment V D) ⥤
      ForgetEnrichment W (TransportEnrichment F D) where
  obj X := ForgetEnrichment.of W X
  map {X} {Y} f := ForgetEnrichment.homOf W <| (e (Hom (C := ForgetEnrichment V D) X Y)) <|
    ForgetEnrichment.homTo V f
  map_id X := by
    rw [h, ForgetEnrichment.homTo_id, ← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [h, h, h, ForgetEnrichment.homTo_comp, F.map_comp, F.map_comp, ← Category.assoc,
      ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, ← Functor.LaxMonoidal.μ_natural_assoc, ← TransportEnrichment.eComp_eq,
      ← ForgetEnrichment.homOf_comp, leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc,
      tensorHom_comp_tensorHom_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`. -/
@[simps]
/-
**CategoryTheory.TransportEnrichment.forgetEnrichmentEquivInverse** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.TransportEnrichment`。
形式化陈述：{V : Type u'} →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       {W : Type u''} →         [inst_2 
: CategoryTheory.Category.{v'', u''} W] →           [inst_3 : CategoryTheory.Mon
oidalCategory W] →             (F : CategoryTheory.Functor V W) →               
[inst_4 : F.LaxMonoidal] →                 (D : Type u) →                   [ins
t_5 : CategoryTheory.EnrichedCategory V D] →                     (e :           
              (v : V) →                           (CategoryTheory.MonoidalCatego
ryStruct.tensorUnit V ⟶ v) ≃                             (CategoryTheory.Monoida
lCategoryStruct.tensorUnit W ⟶ F.obj v)) →                       (∀ (v : V) (f :
 CategoryTheory.MonoidalCategoryStruct.tensorUnit V ⟶ v),                       
    (e v) f =                             CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Functor.LaxMonoidal.ε F) (F.map f)) →                         Categ
oryTheory.Functor                           (CategoryTheory.ForgetEnrichment W (
CategoryTheory.TransportEnrichment F D))                           (CategoryTheo
ry.TransportEnrichment F (CategoryTheory.ForgetEnrichment V D))
参数：F : CategoryTheory.Functor V W；D : Type u；e :                         (v : V)
 →                           (CategoryTheory.MonoidalCategoryStruct.tensorUnit V
 ⟶ v) ≃                             (CategoryTheory.MonoidalCategoryStruct.tenso
rUnit W ⟶ F.obj v)；∀ (v : V) (f : CategoryTheory.MonoidalCategoryStruct.tensorUn
it V ⟶ v),                           (e v) f =                             Categ
oryTheory.CategoryStruct.comp (CategoryTheory.Functor.LaxMonoidal.ε F) (F.map f)
；CategoryTheory.ForgetEnrichment W (CategoryTheory.TransportEnrichment F D)；Cate
goryTheory.TransportEnrichment F (CategoryTheory.ForgetEnrichment V D)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The inverse functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`.
-/
def TransportEnrichment.forgetEnrichmentEquivInverse :
    ForgetEnrichment W (TransportEnrichment F D) ⥤ TransportEnrichment F (ForgetEnrichment V D)
      where
  obj X := ForgetEnrichment.of V (ForgetEnrichment.to (C := TransportEnrichment F D) W X)
  map f := ForgetEnrichment.homOf V ((e _).symm (ForgetEnrichment.homTo W f))
  map_id X := by
    rw [← ForgetEnrichment.homOf_eId]
    congr 1
    apply Equiv.injective (e _)
    rw [ForgetEnrichment.homTo_id, Equiv.apply_symm_apply, h, TransportEnrichment.eId_eq]
  map_comp f g := by
    rw [← ForgetEnrichment.homOf_comp]
    congr
    apply Equiv.injective (e _)
    rw [Equiv.apply_symm_apply, h]
    simp only [ForgetEnrichment.homTo_comp, eComp_eq, Category.assoc, Functor.map_comp]
    slice_rhs 1 3 =>
      rw [← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
        ← Functor.LaxMonoidal.μ_natural, ← leftUnitor_inv_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
    simp [← h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `D` is a `V`-enriched category, then forgetting the enrichment and transporting the resulting
enriched ordinary category along a functor `F : V ⥤ W`, for which
`f ↦ Functor.LaxMonoidal.ε F ≫ F.map f` has an inverse, results in a category equivalent to
transporting along `F` and then forgetting about the resulting `W`-enrichment. -/
@[simps]
/-
**CategoryTheory.TransportEnrichment.forgetEnrichmentEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.TransportEnrichment`。
形式化陈述：{V : Type u'} →   [inst : CategoryTheory.Category.{v', u'} V] →     [inst_
1 : CategoryTheory.MonoidalCategory V] →       {W : Type u''} →         [inst_2 
: CategoryTheory.Category.{v'', u''} W] →           [inst_3 : CategoryTheory.Mon
oidalCategory W] →             (F : CategoryTheory.Functor V W) →               
[inst_4 : F.LaxMonoidal] →                 (D : Type u) →                   [ins
t_5 : CategoryTheory.EnrichedCategory V D] →                     (e :           
              (v : V) →                           (CategoryTheory.MonoidalCatego
ryStruct.tensorUnit V ⟶ v) ≃                             (CategoryTheory.Monoida
lCategoryStruct.tensorUnit W ⟶ F.obj v)) →                       (∀ (v : V) (f :
 CategoryTheory.MonoidalCategoryStruct.tensorUnit V ⟶ v),                       
    (e v) f =                             CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Functor.LaxMonoidal.ε F) (F.map f)) →                         (Cate
goryTheory.TransportEnrichment F (CategoryTheory.ForgetEnrichment V D) ≌        
                   CategoryTheory.ForgetEnrichment W (CategoryTheory.TransportEn
richment F D))
参数：F : CategoryTheory.Functor V W；D : Type u；e :                         (v : V)
 →                           (CategoryTheory.MonoidalCategoryStruct.tensorUnit V
 ⟶ v) ≃                             (CategoryTheory.MonoidalCategoryStruct.tenso
rUnit W ⟶ F.obj v)；∀ (v : V) (f : CategoryTheory.MonoidalCategoryStruct.tensorUn
it V ⟶ v),                           (e v) f =                             Categ
oryTheory.CategoryStruct.comp (CategoryTheory.Functor.LaxMonoidal.ε F) (F.map f)
；CategoryTheory.TransportEnrichment F (CategoryTheory.ForgetEnrichment V D) ≌   
                        CategoryTheory.ForgetEnrichment W (CategoryTheory.Transp
ortEnrichment F D)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is a `V`-enriched category, then forgetting the enrichment and transporti
ng the resulting
enriched ordinary category along a functor `F : V ⥤ W`, for which
`f ↦ Functor.LaxMonoidal.ε F ≫ F.map f` has an inverse, results in a category eq
uivalent to
transporting along `F` and then forgetting about the resulting `W`-enrichment.
-/
def TransportEnrichment.forgetEnrichmentEquiv : TransportEnrichment F (ForgetEnrichment V D) ≌
    ForgetEnrichment W (TransportEnrichment F D) where
  functor := forgetEnrichmentEquivFunctor _ _ e h
  inverse := forgetEnrichmentEquivInverse _ _ e h
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    simp [ForgetEnrichment.to, ForgetEnrichment.of]
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, forgetEnrichmentEquivFunctor_obj, Functor.comp_obj,
      forgetEnrichmentEquivInverse_obj, ForgetEnrichment.to_of, NatIso.ofComponents_hom_app,
      Iso.refl_hom, forgetEnrichmentEquivFunctor_map, h, Category.comp_id]
    rw [← ForgetEnrichment.homOf_eId, TransportEnrichment.eId_eq, ForgetEnrichment.homTo_id]
    rfl

end Equiv

end TransportEnrichment

section full_subcategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- A full subcategory of an enriched ordinary category is an enriched ordinary category. -/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A full subcategory of an enriched ordinary category is an enriched ordinary cate
gory.
-/
instance (P : ObjectProperty C) :
    EnrichedOrdinaryCategory V (ObjectProperty.FullSubcategory P) where
  Hom X Y := X.obj ⟶[V] Y.obj
  id X := eId V X.obj
  comp X Y Z := eComp V X.obj Y.obj Z.obj
  homEquiv {X} {Y} := P.fullyFaithfulι.homEquiv.trans (eHomEquiv V)
  homEquiv_id {X} := by
    change _ = eId V X.obj
    rw [← eHomEquiv_id]
    rfl
  homEquiv_comp f g := by
    simp only [ObjectProperty.ι_obj]
    change (eHomEquiv V) (P.ι.map (f ≫ g)) = _
    rw [Functor.map_comp, eHomEquiv_comp]
    rfl

end full_subcategory

end CategoryTheory

