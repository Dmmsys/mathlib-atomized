/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Day convolution monoidal structure

Given functors `F G : C ⥤ V` between two monoidal categories,
this file defines a typeclass `DayConvolution` on functors `F` `G` that contains
a functor `F ⊛ G`, as well as the required data to exhibit `F ⊛ G` as a pointwise
left Kan extension of `F ⊠ G` (see `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean`
for the definition) along the tensor product of `C`.
Such a functor is called a Day convolution of `F` and `G`, and
although we do not show it yet, this operation defines a monoidal structure on `C ⥤ V`.

We also define a typeclass `DayConvolutionUnit` on a functor `U : C ⥤ V` that bundles the data
required to make it a unit for the Day convolution monoidal structure: said data is that of
a map `𝟙_ V ⟶ U.obj (𝟙_ C)` that exhibits `U` as a pointwise left Kan extension of
`fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`.

The main way to assert that a given monoidal category structure on a category `D`
arises as a "Day convolution monoidal structure" is given by the typeclass
`LawfulDayConvolutionMonoidalCategoryStruct C V D`, which bundles the data and
equations needed to exhibit `D` as a monoidal full subcategory of `C ⥤ V` if
the latter were to have the Day convolution monoidal structure. The definition
`monoidalOfLawfulDayConvolutionMonoidalCategoryStruct` promotes (under suitable
assumptions on `V`) a `LawfulDayConvolutionMonoidalCategoryStruct C V D` to
a monoidal structure.


## References
- [nLab page: Day convolution](https://ncatlab.org/nlab/show/Day+convolution)

## TODOs (@robin-carlier)
- Type alias for `C ⥤ V` with a `LawfulDayConvolutionMonoidalCategoryStruct`.
- Characterization of lax monoidal functors out of a Day convolution monoidal category.
- Case `V = Type u` and its universal property.
- Fix the abuse of functor associativity that causes `erw [id_apply]` in a few places in this file.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]

/-- A `DayConvolution` structure on functors `F G : C ⥤ V` is the data of
a functor `F ⊛ G : C ⥤ V`, along with a unit `F ⊠ G ⟶ tensor C ⋙ F ⊛ G`
that exhibits this functor as a pointwise left Kan extension of `F ⊠ G` along
`tensor C`. This is a `class` used to prove various properties of such extensions,
but registering global instances of this class is probably a bad idea. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolution** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.MonoidalCategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {V : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} V] →         [Categor
yTheory.MonoidalCategory C] →           [CategoryTheory.MonoidalCategory V] →   
          CategoryTheory.Functor C V → CategoryTheory.Functor C V → Type (max (m
ax (max u₁ u₂) v₁) v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DayConvolution` structure on functors `F G : C ⥤ V` is the data of
a functor `F ⊛ G : C ⥤ V`, along with a unit `F ⊠ G ⟶ tensor C ⋙ F ⊛ G`
that exhibits this functor as a pointwise left Kan extension of `F ⊠ G` along
`tensor C`. This is a `class` used to prove various properties of such extension
s,
but registering global instances of this class is probably a bad idea.
-/
class DayConvolution (F G : C ⥤ V) where
  /-- The chosen convolution between the functors. Denoted `F ⊛ G`. -/
  convolution : C ⥤ V
  /-- The chosen convolution between the functors. -/
  unit (F) (G) : F ⊠ G ⟶ tensor C ⋙ convolution
  /-- The transformation `unit` exhibits `F ⊛ G` as a pointwise left Kan extension
  of `F ⊠ G` along `tensor C`. -/
  isPointwiseLeftKanExtensionUnit (F G) :
    (Functor.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension

namespace DayConvolution

open scoped CategoryTheory.Prod

section

/-- A notation for the Day convolution of two functors. -/
scoped infixr:80 " ⊛ " => convolution

variable (F G : C ⥤ V)

/-
**CategoryTheory.MonoidalCategory.DayConvolution.leftKanExtension** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：leftKanExtension [DayConvolution F G] : (F ⊛ G).IsLeftKanExtension (unit F
 G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
instance leftKanExtension [DayConvolution F G] :
    (F ⊛ G).IsLeftKanExtension (unit F G) :=
  isPointwiseLeftKanExtensionUnit F G |>.isLeftKanExtension

variable {F G}

/-- Two Day convolution structures on the same functors gives an isomorphic functor. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolution.uniqueUpToIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：uniqueUpToIso (h : DayConvolution F G) (h' : DayConvolution F G) : h.convo
lution ≅ h'.convolution
参数：h : DayConvolution F G；h' : DayConvolution F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two Day convolution structures on the same functors gives an isomorphic functor.
-/
def uniqueUpToIso (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.convolution ≅ h'.convolution :=
  Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.unit_uniqueUpToIso_hom** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：unit_uniqueUpToIso_hom (h : DayConvolution F G) (h' : DayConvolution F G) 
: h.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').hom = h'.unit
参数：h : DayConvolution F G；h' : DayConvolution F G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_hom`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unit_uniqueUpToIso_hom (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').hom = h'.unit := by
  simp [uniqueUpToIso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.unit_uniqueUpToIso_inv** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：unit_uniqueUpToIso_inv (h : DayConvolution F G) (h' : DayConvolution F G) 
: h'.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').inv = h.unit
参数：h : DayConvolution F G；h' : DayConvolution F G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_inv`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unit_uniqueUpToIso_inv (h : DayConvolution F G) (h' : DayConvolution F G) :
    h'.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').inv = h.unit := by
  simp [uniqueUpToIso]

variable (F G) [DayConvolution F G]

section unit

variable {x x' y y' : C}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.unit_naturality** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：unit_naturality (f : x ⟶ x') (g : y ⟶ y') : (F.map f otimesₘ G.map g) ≫ (u
nit F G).app (x', y') = (unit F G).app (x, y) ≫ (F ⊛ G).map (f otimesₘ g)
参数：f : x ⟶ x'；g : y ⟶ y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma unit_naturality (f : x ⟶ x') (g : y ⟶ y') :
    (F.map f ⊗ₘ G.map g) ≫ (unit F G).app (x', y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ⊗ₘ g) := by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ g)

set_option backward.defeqAttrib.useBackward true in
variable (y) in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.whiskerRight_comp_unit_app** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：whiskerRight_comp_unit_app (f : x ⟶ x') : F.map f ▷ G.obj y ≫ (unit F G).a
pp (x', y) = (unit F G).app (x, y) ≫ (F ⊛ G).map (f ▷ y)
参数：f : x ⟶ x'。
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
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma whiskerRight_comp_unit_app (f : x ⟶ x') :
    F.map f ▷ G.obj y ≫ (unit F G).app (x', y) =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ▷ y) := by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ 𝟙 _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (x) in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.whiskerLeft_comp_unit_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：whiskerLeft_comp_unit_app (g : y ⟶ y') : F.obj x ◁ G.map g ≫ (unit F G).ap
p (x, y') = (unit F G).app (x, y) ≫ (F ⊛ G).map (x ◁ g)
参数：g : y ⟶ y'。
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
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma whiskerLeft_comp_unit_app (g : y ⟶ y') :
    F.obj x ◁ G.map g ≫ (unit F G).app (x, y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (x ◁ g) := by
  simpa [tensorHom_def] using (unit F G).naturality (𝟙 _ ×ₘ g)

end unit

variable {F G}

section map

variable {F' G' : C ⥤ V} [DayConvolution F' G']

/-- The morphism between Day convolutions (provided they exist) induced by a pair of morphisms. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolution.map** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：map (f : F ⟶ F') (g : G ⟶ G') : F ⊛ G ⟶ F' ⊛ G'
参数：f : F ⟶ F'；g : G ⟶ G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism between Day convolutions (provided they exist) induced by a pair of
 morphisms.
-/
def map (f : F ⟶ F') (g : G ⟶ G') : F ⊛ G ⟶ F' ⊛ G' :=
  Functor.descOfIsLeftKanExtension (F ⊛ G) (unit F G) (F' ⊛ G') <|
    (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G'

variable (f : F ⟶ F') (g : G ⟶ G') (x y : C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed in DayConvolution.lean
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：unit_app_map_app : (unit F G).app (x, y) ≫ (map f g).app (x otimes y : C) 
= (f.app x otimesₘ g.app y) ≫ (unit F' G').app (x, y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
-/
lemma unit_app_map_app :
    (unit F G).app (x, y) ≫ (map f g).app (x ⊗ y : C) =
    (f.app x ⊗ₘ g.app y) ≫ (unit F' G').app (x, y) := by
  simpa [tensorHom_def] using!
    (Functor.descOfIsLeftKanExtension_fac_app (F ⊛ G) (unit F G) (F' ⊛ G') <|
      (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G') (x, y)

end map

variable (F G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The universal property of left Kan extensions characterizes the functor
corepresented by `F ⊛ G`. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.corepresentableBy** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：corepresentableBy : .CorepresentableBy (Functor.whiskeringLeft _ _ _).obj 
(tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G) (F ⊛ G) where homEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of left Kan extensions characterizes the functor
corepresented by `F ⊛ G`.
-/
def corepresentableBy :
    (Functor.whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G) |>.CorepresentableBy
      (F ⊛ G) where
  homEquiv := Functor.homEquivOfIsLeftKanExtension _ (unit F G) _
  homEquiv_comp := by aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Use the fact that `(F ⊛ G).obj c` is a colimit to characterize morphisms out of it at a
point. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolution.convolution_hom_ext_at** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：convolution_hom_ext_at (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v} (h : fora
ll {x y : C} (u : x otimes y ⟶ c), (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ f = (
unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ g) : f = g
参数：c : C；F ⊛ G；h : forall {x y : C} (u : x otimes y ⟶ c), (unit F G).app (x, y) 
≫ (F ⊛ G).map u ≫ f = (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
Use the fact that `(F ⊛ G).obj c` is a colimit to characterize morphisms out of 
it at a
point.
-/
theorem convolution_hom_ext_at (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v}
    (h : ∀ {x y : C} (u : x ⊗ y ⟶ c),
      (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ f = (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ g) :
    f = g :=
  ((isPointwiseLeftKanExtensionUnit F G) c).hom_ext (fun j ↦ by simpa using h j.hom)

section associator

open CategoryTheory.Functor

variable (H : C ⥤ V) [DayConvolution G H] [DayConvolution F (G ⊛ H)] [DayConvolution (F ⊛ G) H]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]

open MonoidalCategory.ExternalProduct

/-
**CategoryTheory.MonoidalCategory.DayConvolution.** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.MonoidalCategory.DayConvolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (F ⊠ G ⊛ H).IsLeftKanExtension <|
    extensionUnitRight (G ⊛ H) (unit G H) F :=
  (isPointwiseLeftKanExtensionExtensionUnitRight _ _ _ <|
    isPointwiseLeftKanExtensionUnit G H).isLeftKanExtension
/-
**CategoryTheory.MonoidalCategory.DayConvolution.** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.MonoidalCategory.DayConvolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ((F ⊛ G) ⊠ H).IsLeftKanExtension <|
    extensionUnitLeft (F ⊛ G) (unit F G) H :=
  (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _ <|
    isPointwiseLeftKanExtensionUnit F G).isLeftKanExtension

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ (F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ Y)` is corepresented by
`F ⊛ G ⊛ H`. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.corepresentableBy** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：corepresentableBy : .CorepresentableBy (Functor.whiskeringLeft _ _ _).obj 
(tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G) (F ⊛ G) where homEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ (F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ Y)` is corepresented by
`F ⊛ G ⊛ H`.
-/
def corepresentableBy₂ :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H) |>.CorepresentableBy (F ⊛ G ⊛ H) where
  homEquiv :=
    (corepresentableBy F (G ⊛ H)).homEquiv.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight (G ⊛ H) (unit G H) F) _
  homEquiv_comp := by aesop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ ((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ Y)` is corepresented by
`(F ⊛ G) ⊛ H`. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.corepresentableBy** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：corepresentableBy : .CorepresentableBy (Functor.whiskeringLeft _ _ _).obj 
(tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G) (F ⊛ G) where homEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ ((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ Y)` is corepresented by
`(F ⊛ G) ⊛ H`.
-/
def corepresentableBy₂' :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H) |>.CorepresentableBy ((F ⊛ G) ⊛ H) where
  homEquiv :=
    (corepresentableBy (F ⊛ G) H).homEquiv.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft (F ⊛ G) (unit F G) H) _
  homEquiv_comp := by aesop

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism of functors between
`((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ -)` and
`(F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ -)` that corresponds to the associator
isomorphism for Day convolution through `corepresentableBy₂` and `corepresentableBy₂`. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.associatorCorepresentingIso** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：associatorCorepresentingIso : (whiskeringLeft _ _ _).obj (tensor C) ⋙ (whi
skeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙ coyoneda.obj (.op <| (F ⊠ G) ⊠ 
H) ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙ (whiskeringLeft _ _ _).obj ((𝟭 C).p
rod (tensor C)) ⋙ coyoneda.obj (.op <| F ⊠ G ⊠ H)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of functors between
`((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ -)` and
`(F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ -)` that corresponds to the ass
ociator
isomorphism for Day convolution through `corepresentableBy₂` and `corepresentabl
eBy₂`.
-/
def associatorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.associativity C C C).inverse ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ ↦ Equiv.toIso <|
          (prod.associativity C C C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.associativity C C C).inverse ⋙ (tensor C).prod (𝟭 C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents (fun _ ↦ α_ _ _ _)) _
    _ ≅ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
      isoWhiskerLeft _ <|
        coyoneda.mapIso <| Iso.op <| NatIso.ofComponents (fun _ ↦ α_ _ _ _ |>.symm)

/-- The associator isomorphism for Day convolution -/
/-
**CategoryTheory.MonoidalCategory.DayConvolution.associator** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：associator : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism for Day convolution
-/
def associator : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H :=
  corepresentableBy₂' F G H |>.ofIso (associatorCorepresentingIso F G H) |>.uniqueUpToIso <|
    corepresentableBy₂ F G H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the forward direction of the associator isomorphism
with respect to the unit transformations. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：associator_hom_unit_unit (x y z : C) : (unit F G).app (x, y) ▷ (H.obj z) ≫
 (unit (F ⊛ G) H).app (x otimes y, z) ≫ (associator F G H).hom.app ((x otimes y)
 otimes z) = (α_ _ _ _).hom ≫ (F.obj x ◁ (unit G H).app (y, z)) ≫ (unit F (G ⊛ H
)).app (x, y otimes z) ≫ (F ⊛ G ⊛ H).map (α_ _ _ _).inv
参数：x y z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitLeftUnit`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitRightUnit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.descOfIsLeftKanExtension.congr_simp`：∀ {C : Type 
u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Equivalence.funInvIdAssoc_inv_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Equivalence.funInvIdAssoc_hom_app`：funInvIdAssoc_hom_app 
(e : C ≌ D) (F : C ⥤ E) (X : C) : (funInvIdAssoc e F).hom.app X = F.map (e.unitI
nv.app X)
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Characterizing the forward direction of the associator isomorphism
with respect to the unit transformations.
-/
lemma associator_hom_unit_unit (x y z : C) :
    (unit F G).app (x, y) ▷ (H.obj z) ≫
      (unit (F ⊛ G) H).app (x ⊗ y, z) ≫
      (associator F G H).hom.app ((x ⊗ y) ⊗ z) =
    (α_ _ _ _).hom ≫
      (F.obj x ◁ (unit G H).app (y, z)) ≫
      (unit F (G ⊛ H)).app (x, y ⊗ z) ≫
      (F ⊛ G ⊛ H).map (α_ _ _ _).inv := by
  have := congrArg (fun t ↦ t.app ((x, y), z)) <|
      (corepresentableBy₂' F G H).homEquiv.rightInverse_symm <|
        (corepresentableBy₂ F G H |>.ofIso
          (associatorCorepresentingIso F G H).symm |>.homEquiv (𝟙 _))
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.CorepresentableBy.ofIso, corepresentableBy₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [whiskerLeft_id, Category.comp_id, Category.assoc] at this
  simp only [Category.assoc, this]
  dsimp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp


set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the inverse direction of the associator
with respect to the unit transformations -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.associator_inv_unit_unit** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：associator_inv_unit_unit (x y z : C) : F.obj x ◁ (unit G H).app (y, z) ≫ (
unit F (G ⊛ H)).app (x, y otimes z) ≫ (associator F G H).inv.app (x otimes y oti
mes z) = (α_ (F.obj x) (G.obj y) (H.obj z)).inv ≫ (unit F G).app (x, y) ▷ H.obj 
z ≫ (unit (F ⊛ G) H).app (x otimes y, z) ≫ ((F ⊛ G) ⊛ H).map (α_ x y z).hom
参数：x y z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitRightUnit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitLeftUnit`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Characterizing the inverse direction of the associator
with respect to the unit transformations
-/
lemma associator_inv_unit_unit (x y z : C) :
    F.obj x ◁ (unit G H).app (y, z) ≫
      (unit F (G ⊛ H)).app (x, y ⊗ z) ≫
      (associator F G H).inv.app (x ⊗ y ⊗ z) =
    (α_ (F.obj x) (G.obj y) (H.obj z)).inv ≫ (unit F G).app (x, y) ▷ H.obj z ≫
      (unit (F ⊛ G) H).app (x ⊗ y, z) ≫
      ((F ⊛ G) ⊛ H).map (α_ x y z).hom := by
  have := congrArg (fun t ↦ t.app (x, y, z)) <|
      (corepresentableBy₂ F G H).homEquiv.rightInverse_symm <|
        (corepresentableBy₂' F G H |>.ofIso
          (associatorCorepresentingIso F G H) |>.homEquiv (𝟙 _))
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.CorepresentableBy.ofIso, corepresentableBy₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [whiskerRight_tensor, id_whiskerRight, Category.id_comp, Iso.inv_hom_id] at this
  simp only [this]
  dsimp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp


set_option backward.isDefEq.respectTransparency false in
variable {F G H} in
/-
**CategoryTheory.MonoidalCategory.DayConvolution.associator_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：associator_naturality {F' G' H' : C ⥤ V} [DayConvolution F' G'] [DayConvol
ution G' H'] [DayConvolution F' (G' ⊛ H')] [DayConvolution (F' ⊛ G') H'] (f : F 
⟶ F') (g : G ⟶ G') (h : H ⟶ H') : map (map f g) h ≫ (associator F' G' H').hom = 
(associator F G H).hom ≫ map f (map g h)
参数：G' ⊛ H'；F' ⊛ G'；f : F ⟶ F'；g : G ⟶ G'；h : H ⟶ H'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitLeftUnit`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} V]   [inst_2 : Category…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit_
assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app`：unit_ap
p_map_app : (unit F G).app (x, y) ≫ (map f g).app (x otimes y : C) = (f.app x ot
imesₘ g.app y) ≫ (unit F' G').app (x, y)
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit`
：associator_hom_unit_unit (x y z : C) : (unit F G).app (x, y) ▷ (H.obj z) ≫ (uni
t (F ⊛ G) H).app (x otimes y, z) ≫ (associator F G H).hom.app…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
（共 31 条，此处仅展示前 30 条）
-/
theorem associator_naturality {F' G' H' : C ⥤ V}
    [DayConvolution F' G'] [DayConvolution G' H']
    [DayConvolution F' (G' ⊛ H')] [DayConvolution (F' ⊛ G') H']
    (f : F ⟶ F') (g : G ⟶ G') (h : H ⟶ H') :
      map (map f g) h ≫
        (associator F' G' H').hom =
      (associator F G H).hom ≫ map f (map g h) := by
  apply (corepresentableBy₂' F G H) |>.homEquiv.injective
  dsimp
  ext
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj, tensor_obj,
    Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, whiskerLeft_id, Category.comp_id,
    corepresentableBy_homEquiv_apply_app, NatTrans.comp_app, unit_app_map_app_assoc]
  rw [associator_hom_unit_unit_assoc]
  simp only [tensorHom_def, Category.assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, unit_app_map_app_assoc]
  rw [← comp_whiskerRight_assoc, unit_app_map_app]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, associator_hom_unit_unit, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, unit_app_map_app]
  simp [tensorHom_def]

section pentagon

variable [∀ (v : V) (d : C × C),
    Limits.PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalCategory.DayConvolution.pentagon** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：pentagon (H K : C ⥤ V) [DayConvolution G H] [DayConvolution (F ⊛ G) H] [Da
yConvolution F (G ⊛ H)] [DayConvolution H K] [DayConvolution G (H ⊛ K)] [DayConv
olution (G ⊛ H) K] [DayConvolution ((F ⊛ G) ⊛ H) K] [DayConvolution (F ⊛ G) (H ⊛
 K)] [DayConvolution (F ⊛ G ⊛ H) K] [DayConvolution F (G ⊛ H ⊛ K)] [DayConvoluti
on F ((G ⊛ H) ⊛ K)] : map (associator F G H).hom (𝟙 K) ≫ (associator F (G ⊛ H) K
).hom ≫ map (𝟙 F) (associator G H K).hom = (associator (F ⊛ G) H K).hom ≫ (assoc
iator F G (H ⊛ K)).hom
参数：H K : C ⥤ V；F ⊛ G；G ⊛ H；H ⊛ K；G ⊛ H；(F ⊛ G) ⊛ H；F ⊛ G；H ⊛ K；F ⊛ G ⊛ H；G ⊛ H ⊛
 K；(G ⊛ H) ⊛ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitLeftUnit`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_inv_unit_unit_
assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用引理 `CategoryTheory.Iso.map_hom_inv_id`：map_hom_inv_id (F : C ⥤ D) : F.map e.
hom ≫ F.map e.inv = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft_symm`：tensor_whiskerL
eft_symm (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : X ◁ Y ◁ f = (α_ X Y Z).inv ≫ (X oti
mes Y) ◁ f ≫ (α_ X Y Z').hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit_
assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor_symm_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoid
alCategory C] {X X' : C}   (f : X ⟶ X') (Y Z : C) {Z…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit`
：associator_hom_unit_unit (x y z : C) : (unit F G).app (x, y) ▷ (H.obj z) ≫ (uni
t (F ⊛ G) H).app (x otimes y, z) ≫ (associator F G H).hom.app…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
（共 38 条，此处仅展示前 30 条）
-/
lemma pentagon (H K : C ⥤ V)
    [DayConvolution G H] [DayConvolution (F ⊛ G) H] [DayConvolution F (G ⊛ H)]
    [DayConvolution H K] [DayConvolution G (H ⊛ K)] [DayConvolution (G ⊛ H) K]
    [DayConvolution ((F ⊛ G) ⊛ H) K] [DayConvolution (F ⊛ G) (H ⊛ K)]
    [DayConvolution (F ⊛ G ⊛ H) K] [DayConvolution F (G ⊛ H ⊛ K)]
    [DayConvolution F ((G ⊛ H) ⊛ K)] :
    map (associator F G H).hom (𝟙 K) ≫
        (associator F (G ⊛ H) K).hom ≫ map (𝟙 F) (associator G H K).hom =
      (associator (F ⊛ G) H K).hom ≫ (associator F G (H ⊛ K)).hom := by
  -- We repeatedly apply the fact that the functors are left Kan extensions
  apply Functor.hom_ext_of_isLeftKanExtension (α := unit ((F ⊛ G) ⊛ H) K)
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊛ H) (unit (F ⊛ G) H) K)
  have : (((F ⊛ G) ⊠ H) ⊠ K).IsLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K) :=
    isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _
      (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _
        (isPointwiseLeftKanExtensionUnit F G)) |>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K)
  -- And then we compute...
  ext ⟨⟨⟨i, j⟩, k⟩, l⟩
  have aux :
      ((unit F G).app (i, j) ⊗ₘ (unit H K).app (k, l)) ≫
        (unit (F ⊛ G) (H ⊛ K)).app ((i ⊗ j), (k ⊗ l)) =
      (α_ (F.obj i) (G.obj j) (H.obj k ⊗ K.obj l)).hom ≫
        F.obj i ◁ G.obj j ◁ (unit H K).app (k, l) ≫ F.obj i ◁ (unit G (H ⊛ K)).app (j, (k ⊗ l)) ≫
        (unit F (G ⊛ H ⊛ K)).app (i, (j ⊗ k ⊗ l)) ≫ (F ⊛ G ⊛ H ⊛ K).map (α_ i j (k ⊗ l)).inv ≫
        (associator F G (H ⊛ K)).inv.app ((i ⊗ j) ⊗ k ⊗ l) := by
    conv_rhs => simp only [Functor.comp_obj, tensor_obj, NatTrans.naturality,
      associator_inv_unit_unit_assoc, externalProductBifunctor_obj_obj, Iso.map_hom_inv_id,
      Category.comp_id]
    simp only [tensor_whiskerLeft_symm, Category.assoc, Iso.hom_inv_id_assoc,
    ← tensorHom_def'_assoc]
  dsimp
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id, unit_app_map_app_assoc,
    externalProductBifunctor_obj_obj, NatTrans.id_app, tensorHom_id, associator_hom_unit_unit_assoc,
    tensor_obj, NatTrans.naturality]
  conv_rhs =>
    simp only [whiskerRight_tensor_symm_assoc, Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
    rw [reassoc_of% aux]
  simp only [Iso.inv_hom_id_app_assoc, ← comp_whiskerRight_assoc, associator_hom_unit_unit F G H]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, whisker_assoc, Category.assoc,
    whiskerRight_comp_unit_app_assoc (F ⊛ G ⊛ H) K l (α_ i j k).inv,
    NatTrans.naturality_assoc, NatTrans.naturality, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, unit_app_map_app_assoc, NatTrans.id_app, id_tensorHom,
    Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, associator_hom_unit_unit]
  simp [← Functor.map_comp, pentagon_inv, pentagon_assoc]

end pentagon

end associator

end

end DayConvolution

/-- A `DayConvolutionUnit` structure on a functor `C ⥤ V` is the data of a pointwise
left Kan extension of `fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`. Again, this is
made a class to ease proofs when constructing `DayConvolutionMonoidalCategory` structures, but one
should avoid registering it globally. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit** 是 Mathlib 中的一个类，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：DayConvolutionUnit (F : C ⥤ V) where /-- A "canonical" structure map `𝟙_ V
 ⟶ F.obj (𝟙_ C)` that defines a natural transformation `fromPUnit (𝟙_ V) ⟶ fromP
Unit (𝟙_ C) ⋙ F`. -/ can : 𝟙_ V ⟶ F.obj (𝟙_ C) /-- The canonical map `𝟙_ V ⟶ F.o
bj (𝟙_ C)` exhibits `F` as a pointwise left Kan extension of `fromPUnit.{0} 𝟙_ V
` along `fromPUnit.{0} 𝟙_ C`. -/ isPointwiseLeftKanExtensionCan : Functor.LeftEx
tension.mk F ({ app _
参数：F : C ⥤ V；𝟙_ C；𝟙_ V；𝟙_ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DayConvolutionUnit` structure on a functor `C ⥤ V` is the data of a pointwise
left Kan extension of `fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`. Again, this i
s
made a class to ease proofs when constructing `DayConvolutionMonoidalCategory` s
tructures, but one
should avoid registering it globally.
-/
class DayConvolutionUnit (F : C ⥤ V) where
  /-- A "canonical" structure map `𝟙_ V ⟶ F.obj (𝟙_ C)` that defines a natural transformation
  `fromPUnit (𝟙_ V) ⟶ fromPUnit (𝟙_ C) ⋙ F`. -/
  can : 𝟙_ V ⟶ F.obj (𝟙_ C)
  /-- The canonical map `𝟙_ V ⟶ F.obj (𝟙_ C)` exhibits `F` as a pointwise left Kan extension
  of `fromPUnit.{0} 𝟙_ V` along `fromPUnit.{0} 𝟙_ C`. -/
  isPointwiseLeftKanExtensionCan : Functor.LeftExtension.mk F
    ({ app _ := can } : Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ F) |>.IsPointwiseLeftKanExtension

namespace DayConvolutionUnit

variable (U : C ⥤ V) [DayConvolutionUnit U]
open scoped DayConvolution
open ExternalProduct CategoryTheory.Functor

/-- A shorthand for the natural transformation of functors out of PUnit defined by
the canonical morphism `𝟙_ V ⟶ U.obj (𝟙_ C)` when `U` is a unit for Day convolution. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for the natural transformation of functors out of PUnit defined by
the canonical morphism `𝟙_ V ⟶ U.obj (𝟙_ C)` when `U` is a unit for Day convolut
ion.
-/
abbrev φ : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ U where
  app _ := can

/-- Since a convolution unit is a pointwise left Kan extension, maps out of it at
any object are uniquely characterized. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.hom_ext** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：hom_ext {c : C} {v : V} {g h : U.obj c ⟶ v} (e : forall f : 𝟙_ C ⟶ c, can 
≫ U.map f ≫ g = can ≫ U.map f ≫ h) : g = h
参数：e : forall f : 𝟙_ C ⟶ c, can ≫ U.map f ≫ g = can ≫ U.map f ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
Since a convolution unit is a pointwise left Kan extension, maps out of it at
any object are uniquely characterized.
-/
lemma hom_ext {c : C} {v : V} {g h : U.obj c ⟶ v}
    (e : ∀ f : 𝟙_ C ⟶ c, can ≫ U.map f ≫ g = can ≫ U.map f ≫ h) :
    g = h := by
  apply (isPointwiseLeftKanExtensionCan c).hom_ext
  intro j
  simpa using e j.hom

variable (F : C ⥤ V)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (F ⊠ U).IsLeftKanExtension <| extensionUnitRight U (φ U) F :=
  isPointwiseLeftKanExtensionExtensionUnitRight
    U (φ U) F isPointwiseLeftKanExtensionCan |>.isLeftKanExtension
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (U ⊠ F).IsLeftKanExtension <| extensionUnitLeft U (φ U) F :=
  isPointwiseLeftKanExtensionExtensionUnitLeft
    U (φ U) F isPointwiseLeftKanExtensionCan |>.isLeftKanExtension

set_option backward.isDefEq.respectTransparency false in
/-- A `CorepresentableBy` structure that characterizes maps out of `U ⊛ F`
by leveraging the fact that `U ⊠ F` is a left Kan extension of `(fromPUnit 𝟙_ V) ⊠ F`. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.corepresentableByLeft** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：corepresentableByLeft [DayConvolution U F] : (whiskeringLeft _ _ _).obj (t
ensor C) ⋙ (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)
) ⋙ .CorepresentableBy (U ⊛ F) where coyoneda.obj (.op <| Functor.fromPUnit.{0} 
(𝟙_ V) ⊠ F) homEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitLeftφ`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} V]   [inst_2 : Category…

--- 原说明 ---
A `CorepresentableBy` structure that characterizes maps out of `U ⊛ F`
by leveraging the fact that `U ⊠ F` is a left Kan extension of `(fromPUnit 𝟙_ V)
 ⊠ F`.
-/
def corepresentableByLeft [DayConvolution U F] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) |>.CorepresentableBy (U ⊛ F) where
  homEquiv :=
    Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit U F) _ |>.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  homEquiv_comp := by aesop

set_option backward.isDefEq.respectTransparency false in
/-- A `CorepresentableBy` structure that characterizes maps out of `F ⊛ U` by
leveraging the fact that `F ⊠ U` is a left Kan extension of `F ⊠ (fromPUnit 𝟙_ V)`. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.corepresentableByRight** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：corepresentableByRight [DayConvolution F U] : (whiskeringLeft _ _ _).obj (
tensor C) ⋙ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C)
)) ⋙ .CorepresentableBy (F ⊛ U) where coyoneda.obj (.op <| F ⊠ Functor.fromPUnit
.{0} (𝟙_ V)) homEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitRightφ`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} V]   [inst_2 : Category…

--- 原说明 ---
A `CorepresentableBy` structure that characterizes maps out of `F ⊛ U` by
leveraging the fact that `F ⊠ U` is a left Kan extension of `F ⊠ (fromPUnit 𝟙_ V
)`.
-/
def corepresentableByRight [DayConvolution F U] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) |>.CorepresentableBy (F ⊛ U) where
  homEquiv :=
    Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit F U) _ |>.trans <|
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  homEquiv_comp := by aesop

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of corepresentable functors that defines the left unitor for
Day convolution. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitorCorepresentingIso
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：leftUnitorCorepresentingIso : (whiskeringLeft _ _ _).obj (tensor C) ⋙ (whi
skeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙ coyoneda.ob
j (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) ≅ coyoneda.obj (.op <| F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of corepresentable functors that defines the left unitor for
Day convolution.
-/
def leftUnitorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) ≅
    coyoneda.obj (.op <| F) := by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.leftUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ ↦ Equiv.toIso <|
          (prod.leftUnitorEquivalence C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.leftUnitorEquivalence C).inverse ⋙ (Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C) ⋙
              tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ ↦ λ_ _) _
    _ ≅ _ := coyoneda.mapIso <| Iso.op <| NatIso.ofComponents fun _ ↦ (λ_ _).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of corepresentable functors that defines the right unitor for
Day convolution. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitorCorepresentingIs
o** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`
。
形式化陈述：rightUnitorCorepresentingIso : (whiskeringLeft _ _ _).obj (tensor C) ⋙ (wh
iskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙ coyoneda.o
bj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) ≅ coyoneda.obj (.op <| F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of corepresentable functors that defines the right unitor for
Day convolution.
-/
def rightUnitorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) ≅
    coyoneda.obj (.op <| F) := by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
          (whiskeringLeft _ _ _).obj (prod.rightUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ ↦ Equiv.toIso <|
          (prod.rightUnitorEquivalence C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.rightUnitorEquivalence C).inverse ⋙
              ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙ tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ ↦ ρ_ _) _
    _ ≅ _ := coyoneda.mapIso <| Iso.op <| NatIso.ofComponents fun _ ↦ (ρ_ _).symm

/-- The left unitor isomorphism for Day convolution. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：leftUnitor [DayConvolution U F] : U ⊛ F ≅ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The left unitor isomorphism for Day convolution.
-/
def leftUnitor [DayConvolution U F] : U ⊛ F ≅ F :=
  corepresentableByLeft U F |>.ofIso (leftUnitorCorepresentingIso F) |>.uniqueUpToIso
    <| Functor.corepresentableByEquiv.symm (.refl _)

/-- The right unitor isomorphism for Day convolution. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：rightUnitor [DayConvolution F U] : F ⊛ U ≅ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The right unitor isomorphism for Day convolution.
-/
def rightUnitor [DayConvolution F U] : F ⊛ U ≅ F :=
  corepresentableByRight U F |>.ofIso (rightUnitorCorepresentingIso F) |>.uniqueUpToIso
    <| Functor.corepresentableByEquiv.symm (.refl _)

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
variable [DayConvolution U F]

set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the forward direction of `leftUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor_hom_unit_app** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：leftUnitor_hom_unit_app (y : C) : can ▷ F.obj y ≫ (DayConvolution.unit U F
).app (𝟙_ C, y) ≫ (leftUnitor U F).hom.app (𝟙_ C otimes y) = (fun_ (F.obj y)).ho
m ≫ F.map (fun_ y).inv
参数：y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitLeftφ`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.descOfIsLeftKanExtension.congr_simp`：∀ {C : Type 
u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Equivalence.funInvIdAssoc_inv_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.funInvIdAssoc_hom_app`：funInvIdAssoc_hom_app 
(e : C ≌ D) (F : C ⥤ E) (X : C) : (funInvIdAssoc e F).hom.app X = F.map (e.unitI
nv.app X)
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Characterizing the forward direction of `leftUnitor` via the universal maps.
-/
lemma leftUnitor_hom_unit_app (y : C) :
    can ▷ F.obj y ≫ (DayConvolution.unit U F).app (𝟙_ C, y) ≫
      (leftUnitor U F).hom.app (𝟙_ C ⊗ y) =
    (λ_ (F.obj y)).hom ≫ F.map (λ_ y).inv := by
  have := congrArg (fun t ↦ t.app (.mk PUnit.unit, y)) <|
      (corepresentableByLeft U F).homEquiv.rightInverse_symm <|
        ((leftUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv] at this ⊢
  simp only [whiskerLeft_id, Category.comp_id] at this
  simp only [Category.comp_id, this]
  simp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor_inv_app** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：leftUnitor_inv_app (x : C) : (leftUnitor U F).inv.app x = (fun_ (F.obj x))
.inv ≫ can ▷ F.obj x ≫ (DayConvolution.unit U F).app (𝟙_ C, x) ≫ (U ⊛ F).map (fu
n_ x).hom
参数：x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitLeftφ`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_inv_app (x : C) :
    (leftUnitor U F).inv.app x =
    (λ_ (F.obj x)).inv ≫ can ▷ F.obj x ≫ (DayConvolution.unit U F).app (𝟙_ C, x) ≫
      (U ⊛ F).map (λ_ x).hom := by
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv]
  dsimp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp

set_option backward.isDefEq.respectTransparency false in
variable {F} in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor_naturality** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：leftUnitor_naturality {G : C ⥤ V} [DayConvolution U G] (f : F ⟶ G) : DayCo
nvolution.map (𝟙 _) f ≫ (leftUnitor U G).hom = (leftUnitor U F).hom ≫ f
参数：f : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitLeftφ`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor_hom_unit_a
pp`：leftUnitor_hom_unit_app (y : C) : can ▷ F.obj y ≫ (DayConvolution.unit U F).
app (𝟙_ C, y) ≫ (leftUnitor U F).hom.app (𝟙_ C otimes y) = (fun_…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor_hom_unit_a
pp_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type 
u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_naturality {G : C ⥤ V} [DayConvolution U G] (f : F ⟶ G) :
    DayConvolution.map (𝟙 _) f ≫ (leftUnitor U G).hom =
    (leftUnitor U F).hom ≫ f := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  ext
  simp [← whisker_exchange_assoc]

end

section

omit [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]
variable [DayConvolution F U]

set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the forward direction of `rightUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor_hom_unit_app** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：rightUnitor_hom_unit_app (x : C) : F.obj x ◁ can ≫ (DayConvolution.unit F 
U).app (x, 𝟙_ C) ≫ (rightUnitor U F).hom.app (x otimes 𝟙_ C) = (ρ_ _).hom ≫ F.ma
p (ρ_ x).inv
参数：x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitRightφ`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.descOfIsLeftKanExtension.congr_simp`：∀ {C : Type 
u_1} {H : Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]
   [inst_1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Equivalence.funInvIdAssoc_inv_app`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Equivalence.funInvIdAssoc_hom_app`：funInvIdAssoc_hom_app 
(e : C ≌ D) (F : C ⥤ E) (X : C) : (funInvIdAssoc e F).hom.app X = F.map (e.unitI
nv.app X)
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y

--- 原说明 ---
Characterizing the forward direction of `rightUnitor` via the universal maps.
-/
lemma rightUnitor_hom_unit_app (x : C) :
    F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (rightUnitor U F).hom.app (x ⊗ 𝟙_ C) =
    (ρ_ _).hom ≫ F.map (ρ_ x).inv := by
  have := congrArg (fun t ↦ t.app (x, .mk PUnit.unit)) <|
      (corepresentableByRight U F).homEquiv.rightInverse_symm <|
        ((rightUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv] at this ⊢
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id,
    Category.comp_id] at this
  simp only [Category.comp_id, this]
  simp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor_inv_app** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：rightUnitor_inv_app (x : C) : (rightUnitor U F).inv.app x = (ρ_ (F.obj x))
.inv ≫ F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫ (F ⊛ U).map (ρ_
 x).hom
参数：x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitRightφ`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_inv_app (x : C) :
    (rightUnitor U F).inv.app x =
    (ρ_ (F.obj x)).inv ≫ F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (F ⊛ U).map (ρ_ x).hom := by
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv, Iso.toEquiv, Equiv.toIso]
  dsimp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp

set_option backward.isDefEq.respectTransparency false in
variable {F} in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor_naturality** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolutionUnit`。
形式化陈述：rightUnitor_naturality {G : C ⥤ V} [DayConvolution G U] (f : F ⟶ G) : DayC
onvolution.map f (𝟙 _) ≫ (rightUnitor U G).hom = (rightUnitor U F).hom ≫ f
参数：f : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.instIsLeftKanExtensio
nProdDiscretePUnitExternalProductExtensionUnitRightφ`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor_hom_unit_
app`：rightUnitor_hom_unit_app (x : C) : F.obj x ◁ can ≫ (DayConvolution.unit F U
).app (x, 𝟙_ C) ≫ (rightUnitor U F).hom.app (x otimes 𝟙_ C) = (ρ_…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor_hom_unit_
app_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_naturality {G : C ⥤ V} [DayConvolution G U] (f : F ⟶ G) :
    DayConvolution.map f (𝟙 _) ≫ (rightUnitor U G).hom =
    (rightUnitor U F).hom ≫ f := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  ext
  simp [whisker_exchange_assoc]

end

end DayConvolutionUnit

section triangle

open DayConvolution
open DayConvolutionUnit
open ExternalProduct

variable [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorLeft v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorRight v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
  [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
  [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.DayConvolution.triangle** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : CategoryTheory.Monoida
lCategory C] [inst_3 : CategoryTheory.MonoidalCategory V]   [inst_4 :     ∀ (v :
 V) (d : C),       CategoryTheory.Limits.PreservesColimitsOfShape         (Categ
oryTheory.CostructuredArrow (CategoryTheory.MonoidalCategory.tensor C) d)       
  (CategoryTheory.MonoidalCategory.tensorLeft v)]   [inst_5 :     ∀ (v : V) (d :
 C),       CategoryTheory.Limits.PreservesColimitsOfShape         (CategoryTheor
y.CostructuredArrow (CategoryTheory.MonoidalCategory.tensor C) d)         (Categ
oryTheory.MonoidalCategory.tensorRight v)]   [inst_6 :     ∀ (v : V) (d : C),   
    CategoryTheory.Limits.PreservesColimitsOfShape         (CategoryTheory.Costr
ucturedArrow           (CategoryTheory.Functor.fromPUnit (CategoryTheory.Monoida
lCategoryStruct.tensorUnit C)) d)         (CategoryTheory.MonoidalCategory.tenso
rLeft v)]   [inst_7 :     ∀ (v : V) (d : C),       CategoryTheory.Limits.Preserv
esColimitsOfShape         (CategoryTheory.CostructuredArrow           (CategoryT
heory.Functor.fromPUnit (CategoryTheory.MonoidalCategoryStruct.tensorUnit C)) d)
         (CategoryTheory.MonoidalCategory.tensorRight v)]   [∀ (v : V) (d : C × 
C),       CategoryTheory.Limits.PreservesColimitsOfShape         (CategoryTheory
.CostructuredArrow           ((CategoryTheory.Functor.id C).prod             (Ca
tegoryTheory.Functor.fromPUnit (CategoryTheory.MonoidalCategoryStruct.tensorUnit
 C)))           d)         (CategoryTheory.MonoidalCategory.tensorRight v)]   (F
 G U : CategoryTheory.Functor C V) [inst_9 : CategoryTheory.MonoidalCategory.Day
ConvolutionUnit U]   [inst_10 : CategoryTheory.MonoidalCategory.DayConvolution F
 U]   [inst_11 : CategoryTheory.MonoidalCategory.DayConvolution U G]   [inst_12 
:     CategoryTheory.MonoidalCategory.DayConvolution F (CategoryTheory.MonoidalC
ategory.DayConvolution.convolution U G)]   [inst_13 :     CategoryTheory.Monoida
lCategory.DayConvolution (CategoryTheory.MonoidalCategory.DayConvolution.convolu
tion F U) G]   [inst_14 : CategoryTheory.MonoidalCategory.DayConvolution F G],  
 CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategory.DayConvolut
ion.associator F U G).hom       (CategoryTheory.MonoidalCategory.DayConvolution.
map (CategoryTheory.CategoryStruct.id F)         (CategoryTheory.MonoidalCategor
y.DayConvolutionUnit.leftUnitor U G).hom) =     CategoryTheory.MonoidalCategory.
DayConvolution.map       (CategoryTheory.MonoidalCategory.DayConvolutionUnit.rig
htUnitor U F).hom (CategoryTheory.CategoryStruct.id G)
参数：v : V；d : C；CategoryTheory.CostructuredArrow (CategoryTheory.MonoidalCategory
.tensor C) d；CategoryTheory.MonoidalCategory.tensorLeft v；v : V；d : C；CategoryTh
eory.CostructuredArrow (CategoryTheory.MonoidalCategory.tensor C) d；CategoryTheo
ry.MonoidalCategory.tensorRight v；v : V；d : C；CategoryTheory.CostructuredArrow  
         (CategoryTheory.Functor.fromPUnit (CategoryTheory.MonoidalCategoryStruc
t.tensorUnit C)) d；CategoryTheory.MonoidalCategory.tensorLeft v；v : V；d : C；Cate
goryTheory.CostructuredArrow           (CategoryTheory.Functor.fromPUnit (Catego
ryTheory.MonoidalCategoryStruct.tensorUnit C)) d；CategoryTheory.MonoidalCategory
.tensorRight v；v : V；d : C × C；CategoryTheory.CostructuredArrow           ((Cate
goryTheory.Functor.id C).prod             (CategoryTheory.Functor.fromPUnit (Cat
egoryTheory.MonoidalCategoryStruct.tensorUnit C)))           d；CategoryTheory.Mo
noidalCategory.tensorRight v；F G U : CategoryTheory.Functor C V；CategoryTheory.M
onoidalCategory.DayConvolution.convolution U G；CategoryTheory.MonoidalCategory.D
ayConvolution.convolution F U；CategoryTheory.MonoidalCategory.DayConvolution.ass
ociator F U G；CategoryTheory.MonoidalCategory.DayConvolution.map (CategoryTheory
.CategoryStruct.id F)         (CategoryTheory.MonoidalCategory.DayConvolutionUni
t.leftUnitor U G).hom；CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUn
itor U F；CategoryTheory.CategoryStruct.id G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitLeftUnit`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftK
anExtension`：∀ {C : Type u_1} {D : Type u_2} {H : Type u_4} [inst : CategoryTheo
ry.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit_
assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app`：unit_ap
p_map_app : (unit F G).app (x, y) ≫ (map f g).app (x otimes y : C) = (f.app x ot
imesₘ g.app y) ≫ (unit F' G').app (x, y)
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.leftUnitor_hom_unit_a
pp`：leftUnitor_hom_unit_app (y : C) : can ▷ F.obj y ≫ (DayConvolution.unit U F).
app (𝟙_ C, y) ≫ (leftUnitor U F).hom.app (𝟙_ C otimes y) = (fun_…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_middle_assoc`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheor
y.MonoidalCategory C] (X : C) {Y Y' : C}   (f : Y ⟶ Y') (Z :…
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolutionUnit.rightUnitor_hom_unit_
app`：rightUnitor_hom_unit_app (x : C) : F.obj x ◁ can ≫ (DayConvolution.unit F U
).app (x, 𝟙_ C) ≫ (rightUnitor U F).hom.app (x otimes 𝟙_ C) = (ρ_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.whiskerLeft_comp_unit_app
_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂
} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
（共 35 条，此处仅展示前 30 条）
-/
lemma DayConvolution.triangle (F G U : C ⥤ V) [DayConvolutionUnit U]
    [DayConvolution F U] [DayConvolution U G]
    [DayConvolution F (U ⊛ G)] [DayConvolution (F ⊛ U) G] [DayConvolution F G] :
    (DayConvolution.associator F U G).hom ≫
      DayConvolution.map (𝟙 F) (DayConvolutionUnit.leftUnitor U G).hom =
    DayConvolution.map (DayConvolutionUnit.rightUnitor U F).hom (𝟙 G) := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊛ U) (DayConvolution.unit F U) G)
  have : (F ⊠ U) ⊠ G |>.IsLeftKanExtension
      (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G) :=
    isPointwiseLeftKanExtensionExtensionUnitLeft (F ⊠ U) _ G
      (isPointwiseLeftKanExtensionExtensionUnitRight U (DayConvolutionUnit.φ U) F <|
        DayConvolutionUnit.isPointwiseLeftKanExtensionCan (F := U)) |>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G)
  ext
  dsimp
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id, whisker_assoc,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    DayConvolution.associator_hom_unit_unit_assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, unit_app_map_app_assoc, NatTrans.id_app, id_tensorHom,
    Category.assoc, Iso.inv_hom_id_assoc, unit_app_map_app, Functor.comp_obj,
    tensorHom_id, Iso.cancel_iso_hom_left]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_hom_unit_app,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, rightUnitor_hom_unit_app]
  simp [← Functor.map_comp]

end triangle

section

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

/-- The class `DayConvolutionMonoidalCategory C V D` bundles the necessary data to
turn a monoidal category `D` into a monoidal full subcategory of a category of
functors `C ⥤ V` endowed with a Day convolution monoidal structure.
The design of this class is to bundle a fully faithful functor into `C ⥤ V` with
left extensions on its values representing the fact that it maps tensors products
in `D` to Day convolutions, and furthermore ask that this data is "lawful", i.e that
once realized in the functor category, the objects behave like the corresponding ones
in the category `C ⥤ V`. -/
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct** 是
 Mathlib 中的一个类，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：LawfulDayConvolutionMonoidalCategoryStruct (C : Type u₁) [Category.{v₁} C]
 (V : Type u₂) [Category.{v₂} V] [MonoidalCategory C] [MonoidalCategory V] (D : 
Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D] where /-- a functor that i
nterprets element of `D` as functors `C ⥤ V` -/ ι (C V D) : D ⥤ C ⥤ V /-- a natu
ral transformation `ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d ⊗ d')` -/ convoluti
onExtensionUnit (C) (V) (d d' : D) : ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d ot
imes d') /-- `convolutionU
参数：C : Type u₁；V : Type u₂；D : Type u₃；C V D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class `DayConvolutionMonoidalCategory C V D` bundles the necessary data to
turn a monoidal category `D` into a monoidal full subcategory of a category of
functors `C ⥤ V` endowed with a Day convolution monoidal structure.
The design of this class is to bundle a fully faithful functor into `C ⥤ V` with
left extensions on its values representing the fact that it maps tensors product
s
in `D` to Day convolutions, and furthermore ask that this data is "lawful", i.e 
that
once realized in the functor category, the objects behave like the corresponding
 ones
in the category `C ⥤ V`. -/
-/
class LawfulDayConvolutionMonoidalCategoryStruct
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D] where
  /-- a functor that interprets element of `D` as functors `C ⥤ V` -/
  ι (C V D) : D ⥤ C ⥤ V
  /-- a natural transformation `ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d ⊗ d')` -/
  convolutionExtensionUnit (C) (V) (d d' : D) :
    ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d ⊗ d')
  /-- `convolutionUnitUnit` exhibits `ι.obj (d ⊗ d')` as a left Ken extension of
  `ι.obj d ⊠ ι.obj d'` along `tensor C`. -/
  isPointwiseLeftKanExtensionConvolutionExtensionUnit (d d' : D) :
    (Functor.LeftExtension.mk _ <|
      convolutionExtensionUnit d d').IsPointwiseLeftKanExtension
  /-- a map `𝟙_ V ⟶ (ι.obj <| 𝟙_ D).obj (𝟙_ C)`, that we think of as defining a
  natural transformation
  `fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ (ι.obj <| 𝟙_ D)`. -/
  unitUnit (C) (V) (D) : 𝟙_ V ⟶ (ι.obj <| 𝟙_ D).obj (𝟙_ C)
  /-- the natural transformation induced by `unitUnit` exhibits
  `(ι.obj <| 𝟙_ D).obj (𝟙_ C)` as a left Kan extension of `fromPUnit.{0} (𝟙_ V)` as a
  along `fromPUnit.{0} (𝟙_ C)`. -/
  isPointwiseLeftKanExtensionUnitUnit (C) (V) (D) :
    Functor.LeftExtension.mk _
      ({ app _ := unitUnit } : Functor.fromPUnit.{0} (𝟙_ V) ⟶
        Functor.fromPUnit.{0} (𝟙_ C) ⋙ (ι.obj <| 𝟙_ D)) |>.IsPointwiseLeftKanExtension
  /-- The field `ι` interprets an element of `D` as a functor `C ⥤ V`. -/
  faithful_ι : ι.Faithful := by infer_instance
  convolutionExtensionUnit_comp_ι_map_tensorHom_app (C) (V) {d₁ d₂ d₁' d₂' : D}
    (f₁ : d₁ ⟶ d₁') (f₂ : d₂ ⟶ d₂') (x y : C) :
    (convolutionExtensionUnit d₁ d₂).app (x, y) ≫
      (ι.map (f₁ ⊗ₘ f₂)).app (x ⊗ y) =
    ((ι.map f₁).app x ⊗ₘ (ι.map f₂).app y) ≫
      (convolutionExtensionUnit d₁' d₂').app (x, y)
  convolutionExtensionUnit_comp_ι_map_whiskerLeft_app (V)
    (d₁ : D) {d₂ d₂' : D}
    (f₂ : d₂ ⟶ d₂') (x y : C) :
    (convolutionExtensionUnit d₁ d₂).app (x, y) ≫
      (ι.map (d₁ ◁ f₂)).app (x ⊗ y) =
    ((ι.obj d₁).obj x ◁ (ι.map f₂).app y) ≫
      (convolutionExtensionUnit d₁ d₂').app (x, y)
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app (C) (V)
    {d₁ d₁' : D} (f₁ : d₁ ⟶ d₁') (d₂ : D) (x y : C) :
    (convolutionExtensionUnit d₁ d₂).app (x, y) ≫
      (ι.map (f₁ ▷ d₂)).app (x ⊗ y) =
    ((ι.map f₁).app x ▷ (ι.obj d₂).obj y) ≫
      (convolutionExtensionUnit d₁' d₂).app (x, y)
  associator_hom_unit_unit (V) (d d' d'' : D) (x y z : C) :
    (convolutionExtensionUnit d d').app (x, y) ▷ (ι.obj d'').obj z ≫
      (convolutionExtensionUnit (d ⊗ d') d'').app (x ⊗ y, z) ≫
      (ι.map (α_ d d' d'').hom).app ((x ⊗ y) ⊗ z) =
    (α_ _ _ _).hom ≫
      ((ι.obj d).obj x ◁ (convolutionExtensionUnit d' d'').app (y, z)) ≫
      (convolutionExtensionUnit d (d' ⊗ d'')).app (x, y ⊗ z) ≫
      (ι.obj (d ⊗ d' ⊗ d'')).map (α_ _ _ _).inv
  leftUnitor_hom_unit_app (V) (d : D) (y : C) :
    unitUnit ▷ (ι.obj d).obj y ≫
      (convolutionExtensionUnit (𝟙_ D) d).app
        (𝟙_ C, y) ≫
      (ι.map (λ_ d).hom).app (𝟙_ C ⊗ y) =
    (λ_ ((ι.obj d).obj y)).hom ≫ (ι.obj d).map (λ_ y).inv
  rightUnitor_hom_unit_app (V) (d : D) (y : C) :
    (ι.obj d).obj y ◁ unitUnit ≫
      (convolutionExtensionUnit d (𝟙_ D)).app (y, 𝟙_ C) ≫
      (ι.map (ρ_ d).hom).app (y ⊗ 𝟙_ C) =
    (ρ_ _).hom ≫ (ι.obj d).map (ρ_ y).inv

namespace LawfulDayConvolutionMonoidalCategoryStruct

attribute [instance] faithful_ι

variable (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]

open scoped DayConvolution

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (d ⊗ d')` is a
Day convolution of `(ι C V).obj d` and `(ι C V).d'`. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.con
volution** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayCon
volutionMonoidalCategoryStruct`。
形式化陈述：convolution (d d' : D) : DayConvolution (ι C V D |>.obj d) (ι C V D |>.obj
 d') where convolution
参数：d d' : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (d ⊗ d')` is a
Day convolution of `(ι C V).obj d` and `(ι C V).d'`.
-/
def convolution (d d' : D) :
    DayConvolution (ι C V D |>.obj d) (ι C V D |>.obj d') where
  convolution := (ι C V D).obj (d ⊗ d')
  unit := convolutionExtensionUnit C V d d'
  isPointwiseLeftKanExtensionUnit :=
    isPointwiseLeftKanExtensionConvolutionExtensionUnit d d'

attribute [local instance] convolution

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (d ⊗ d' ⊗ d'')`
is a (triple) Day convolution of `(ι C V).obj d`, `(ι C V).obj d'` and
`(ι C V).obj d''`. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.con
volution** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayCon
volutionMonoidalCategoryStruct`。
形式化陈述：convolution (d d' : D) : DayConvolution (ι C V D |>.obj d) (ι C V D |>.obj
 d') where convolution
参数：d d' : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (d ⊗ d' ⊗ d'')`
is a (triple) Day convolution of `(ι C V).obj d`, `(ι C V).obj d'` and
`(ι C V).obj d''`.
-/
def convolution₂ (d d' d'' : D) :
    DayConvolution (ι C V D |>.obj d) ((ι C V D |>.obj d') ⊛ (ι C V D |>.obj d'')) :=
  convolution C V D _ _

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj ((d ⊗ d') ⊗ d'')`
is a (triple) Day convolution of `(ι C V).obj d`, `(ι C V).obj d'` and
`(ι C V).obj d''`. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.con
volution** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayCon
volutionMonoidalCategoryStruct`。
形式化陈述：convolution (d d' : D) : DayConvolution (ι C V D |>.obj d) (ι C V D |>.obj
 d') where convolution
参数：d d' : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj ((d ⊗ d') ⊗ d'')`
is a (triple) Day convolution of `(ι C V).obj d`, `(ι C V).obj d'` and
`(ι C V).obj d''`.
-/
def convolution₂' (d d' d'' : D) :
    DayConvolution ((ι C V D |>.obj d) ⊛ (ι C V D |>.obj d')) (ι C V D |>.obj d'') :=
  convolution C V D _ _

attribute [local instance] convolution₂ convolution₂'

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayConvolutionMon
oidalCategoryStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_map_tensorHom_hom_eq_tensorHom
    {d₁ d₂ : D} {d₁' d₂' : D}
    (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂') :
    (ι C V D).map (f ⊗ₘ f') =
    DayConvolution.map (ι C V D |>.map f) (ι C V D |>.map f') := by
  apply DayConvolution.corepresentableBy
    (ι C V D |>.obj d₁) (ι C V D |>.obj d₁') |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app,
    DayConvolution.unit_app_map_app]
  exact convolutionExtensionUnit_comp_ι_map_tensorHom_app C V _ _ _ _

set_option backward.isDefEq.respectTransparency false in
open DayConvolution in
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayConvolutionMon
oidalCategoryStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_map_associator_hom_eq_associator_hom (d d' d'')
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)] :
    (ι C V D).map (α_ d d' d'').hom =
    (DayConvolution.associator
      (ι C V D |>.obj d) (ι C V D |>.obj d') (ι C V D |>.obj d'')).hom := by
  apply corepresentableBy₂'
    (ι C V D |>.obj d) (ι C V D |>.obj d') (ι C V D |>.obj d'') |>.homEquiv.injective
  dsimp
  ext ⟨⟨x, y⟩, z⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj,
    tensor_obj, Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, whiskerLeft_id,
    Category.comp_id, corepresentableBy_homEquiv_apply_app,
    DayConvolution.associator_hom_unit_unit]
  exact associator_hom_unit_unit V _ _ _ _ _ _

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (𝟙_ D)`
is a Day convolution unit. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.con
volutionUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDa
yConvolutionMonoidalCategoryStruct`。
形式化陈述：convolutionUnit : DayConvolutionUnit (ι C V D |>.obj <| 𝟙_ D) where can
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (𝟙_ D)`
is a Day convolution unit.
-/
def convolutionUnit : DayConvolutionUnit (ι C V D |>.obj <| 𝟙_ D) where
  can := unitUnit _ _ _
  isPointwiseLeftKanExtensionCan := isPointwiseLeftKanExtensionUnitUnit _ _ _

attribute [local instance] convolutionUnit

set_option backward.isDefEq.respectTransparency false in
open DayConvolutionUnit in
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayConvolutionMon
oidalCategoryStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_map_leftUnitor_hom_eq_leftUnitor_hom (d : D)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)] :
    (ι C V D).map (λ_ d).hom =
    (DayConvolutionUnit.leftUnitor
      (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)).hom := by
  apply corepresentableByLeft
    (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d) |>.homEquiv.injective
  dsimp
  ext ⟨_, x⟩
  dsimp [corepresentableByLeft]
  simp only [whiskerLeft_id, Category.comp_id,
    DayConvolutionUnit.leftUnitor_hom_unit_app]
  exact leftUnitor_hom_unit_app V d x

set_option backward.isDefEq.respectTransparency false in
open DayConvolutionUnit in
/-
**CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.LawfulDayConvolutionMon
oidalCategoryStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_map_rightUnitor_hom_eq_rightUnitor_hom (d : D)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)] :
    (ι C V D).map (ρ_ d).hom =
    (DayConvolutionUnit.rightUnitor
      (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)).hom := by
  apply corepresentableByRight
    (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d) |>.homEquiv.injective
  dsimp
  ext ⟨x, _⟩
  dsimp [corepresentableByRight]
  simp only [id_whiskerRight, Category.id_comp,
    DayConvolutionUnit.rightUnitor_hom_unit_app]
  exact rightUnitor_hom_unit_app V d x

end LawfulDayConvolutionMonoidalCategoryStruct

set_option backward.isDefEq.respectTransparency false in
open LawfulDayConvolutionMonoidalCategoryStruct in
attribute [local instance] convolution convolution₂ convolution₂' convolutionUnit in
open DayConvolution DayConvolutionUnit in
/-- We can promote a `LawfulDayConvolutionMonoidalCategoryStruct` to a monoidal category,
note that every non-prop data is already here, so this is just about showing that they
satisfy the axioms of a monoidal category. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.monoidalOfLawfulDayConvolutionMonoidalCategory
Struct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：monoidalOfLawfulDayConvolutionMonoidalCategoryStruct (D : Type u₃) [Catego
ry.{v₃} D] [MonoidalCategoryStruct D] [LawfulDayConvolutionMonoidalCategoryStruc
t C V D] [forall (v : V) (d : C), Limits.PreservesColimitsOfShape (CostructuredA
rrow (tensor C) d) (tensorLeft v)] [forall (v : V) (d : C), Limits.PreservesColi
mitsOfShape (CostructuredArrow (tensor C) d) (tensorRight v)] [forall (v : V) (d
 : C), Limits.PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0}
 <| 𝟙_ C) d) (tensorLeft v
参数：D : Type u₃；v : V；d : C；CostructuredArrow (tensor C) d；tensorLeft v；v : V；d :
 C；CostructuredArrow (tensor C) d；tensorRight v；v : V；d : C；CostructuredArrow (F
unctor.fromPUnit.{0} <| 𝟙_ C) d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can promote a `LawfulDayConvolutionMonoidalCategoryStruct` to a monoidal cate
gory,
note that every non-prop data is already here, so this is just about showing tha
t they
satisfy the axioms of a monoidal category.
-/
def monoidalOfLawfulDayConvolutionMonoidalCategoryStruct
    (D : Type u₃) [Category.{v₃} D]
    [MonoidalCategoryStruct D]
    [LawfulDayConvolutionMonoidalCategoryStruct C V D]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)] :
    MonoidalCategory D :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun x y => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      apply (DayConvolution.corepresentableBy
        (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨_, _⟩
      simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
        corepresentableBy_homEquiv_apply_app, unit_app_map_app, NatTrans.id_app,
        tensorHom_id, id_whiskerRight, Category.id_comp]
      dsimp [DayConvolution.convolution]
      simp)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom, Functor.map_comp]
      apply (corepresentableBy (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨_, _⟩
      simp)
    (id_tensorHom := fun x {y₁ y₂} f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom]
      apply (corepresentableBy (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨x, y⟩
      dsimp
      simp only [Functor.map_id, unit_app_map_app, Functor.comp_obj, tensor_obj,
        NatTrans.id_app, id_tensorHom]
      dsimp [unit]
      rw [convolutionExtensionUnit_comp_ι_map_whiskerLeft_app])
    (tensorHom_id := fun x {y₁ y₂} f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom]
      apply (corepresentableBy (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨x, y⟩
      dsimp
      simp only [Functor.map_id, DayConvolution.unit_app_map_app, Functor.comp_obj,
        tensor_obj, NatTrans.id_app, tensorHom_id]
      dsimp [DayConvolution.unit]
      rw [convolutionExtensionUnit_comp_ι_map_whiskerRight_app])
    (associator_naturality := fun f₁ f₂ f₃ => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, ι_map_associator_hom_eq_associator_hom,
        ι_map_tensorHom_hom_eq_tensorHom]
      exact DayConvolution.associator_naturality
        ((ι C V D).map f₁) ((ι C V D).map f₂) ((ι C V D).map f₃))
    (leftUnitor_naturality := fun f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      rw [ι_map_leftUnitor_hom_eq_leftUnitor_hom,
        ι_map_leftUnitor_hom_eq_leftUnitor_hom]
      exact DayConvolutionUnit.leftUnitor_naturality
        (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.map f))
    (rightUnitor_naturality := fun f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      rw [ι_map_rightUnitor_hom_eq_rightUnitor_hom, ι_map_rightUnitor_hom_eq_rightUnitor_hom]
      exact DayConvolutionUnit.rightUnitor_naturality
        (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.map f))
    (pentagon := fun a b c d => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, Functor.map_id, ι_map_tensorHom_hom_eq_tensorHom,
        ι_map_associator_hom_eq_associator_hom]
      -- this is a bit painful...
      let : DayConvolution
          (((ι C V D |>.obj a) ⊛ (ι C V D |>.obj b)) ⊛ (ι C V D |>.obj c))
          (ι C V D |>.obj d) :=
        convolution C V D _ _
      let : DayConvolution
          ((ι C V D |>.obj a) ⊛ (ι C V D |>.obj b))
          ((ι C V D |>.obj c) ⊛ (ι C V D |>.obj d)) :=
        convolution C V D _ _
      let : DayConvolution
          ((ι C V D |>.obj a) ⊛ ((ι C V D |>.obj b) ⊛ (ι C V D |>.obj c)))
          (ι C V D |>.obj d) :=
        convolution C V D _ _
      let : DayConvolution
          (ι C V D |>.obj a)
          ((ι C V D |>.obj b) ⊛ ((ι C V D |>.obj c) ⊛ (ι C V D |>.obj d))) :=
        convolution C V D _ _
      let : DayConvolution
          (ι C V D |>.obj a)
          (((ι C V D |>.obj b) ⊛ (ι C V D |>.obj c)) ⊛ (ι C V D |>.obj d)) :=
        convolution C V D _ _
      exact DayConvolution.pentagon
        (ι C V D |>.obj a) (ι C V D |>.obj b) (ι C V D |>.obj c) (ι C V D |>.obj d))
    (triangle := fun a b => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, Functor.map_id, ι_map_tensorHom_hom_eq_tensorHom,
        ι_map_associator_hom_eq_associator_hom, ι_map_leftUnitor_hom_eq_leftUnitor_hom,
        ι_map_rightUnitor_hom_eq_rightUnitor_hom]
      exact DayConvolution.triangle
        (ι C V D |>.obj a) (ι C V D |>.obj b) (ι C V D |>.obj <| 𝟙_ D))

/-! In what follows, we give a constructor for `LawfulDayConvolutionMonoidalCategoryStruct`
that does not assume a pre-existing `MonoidalCategoryStruct` and builds one from
the data of suitable convolutions, while giving definitional control over
as many parameters as we can. -/

/-- An `InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D` bundles the
core data needed to construct a full `LawfulDayConvolutionMonoidalCategoryStructCore`.
We are making this a class so that it can act as a "proxy" for inferring `DayConvolution`
instances (which is all the more important that we are modifying the instances given in the
constructor to get better ones defeq-wise). As this object is purely about the internals
of definitions of Day convolutions monoidal structures, it is advised to not register
this class globally. -/
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：InducedLawfulDayConvolutionMonoidalCategoryStructCore (C : Type u₁) [Categ
ory.{v₁} C] (V : Type u₂) [Category.{v₂} V] [MonoidalCategory C] [MonoidalCatego
ry V] (D : Type u₃) [Category.{v₃} D] where /-- A functor that interprets elemen
ts of `D` as functors `C ⥤ V`. -/ ι (C V D) : D ⥤ C ⥤ V /-- The functor `ι` is f
ully faithful. -/ fullyFaithulι : ι.FullyFaithful /-- Candidate function for the
 tensor product of objects. -/ tensorObj (C) (V) : D -> D -> D /-- First candida
te Day convolutions betwee
参数：C : Type u₁；V : Type u₂；D : Type u₃；C V D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D` bundles the
core data needed to construct a full `LawfulDayConvolutionMonoidalCategoryStruct
Core`.
We are making this a class so that it can act as a "proxy" for inferring `DayCon
volution`
instances (which is all the more important that we are modifying the instances g
iven in the
constructor to get better ones defeq-wise). As this object is purely about the i
nternals
of definitions of Day convolutions monoidal structures, it is advised to not reg
ister
this class globally. -/
-/
class InducedLawfulDayConvolutionMonoidalCategoryStructCore
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    (D : Type u₃) [Category.{v₃} D] where
  /-- A functor that interprets elements of `D` as functors `C ⥤ V`. -/
  ι (C V D) : D ⥤ C ⥤ V
  /-- The functor `ι` is fully faithful. -/
  fullyFaithulι : ι.FullyFaithful
  /-- Candidate function for the tensor product of objects. -/
  tensorObj (C) (V) : D → D → D
  /-- First candidate Day convolutions between objects.
  Note that the name here is primed as in fact, we will use the other fields
  in this class to produce convolutions with more controlled defeq properties. -/
  convolutions' : ∀ (d d' : D), DayConvolution (ι.obj d) (ι.obj d')
  /-- Isomorphisms that exhibits the essential image of `ι` as closed under day
  convolution. -/
  tensorObjIsoConvolution (C) (V) : ∀ (d d' : D),
    ι.obj (tensorObj d d') ≅ (convolutions' d d').convolution
  /-- Candidate component of units for the `LawfulDayConvolutionMonoidalCategoryStruct`,
  this defaults to the ones deduced by `convolutions'` and `tensorObjIsoConvolution`. -/
  convolutionUnitApp (V) :
      ∀ (d d' : D) (x y : C),
        (ι.obj d).obj x ⊗ (ι.obj d').obj y ⟶ (ι.obj (tensorObj d d')).obj (x ⊗ y) :=
    fun d d' x y =>
      (convolutions' d d').unit.app (x, y) ≫
        (tensorObjIsoConvolution d d').inv.app (x ⊗ y)
  /-- Lawfulness of `convolutionUnitApp`. -/
  convolutionUnitApp_eq (V) :
      ∀ (d d' : D) (x y : C),
        convolutionUnitApp d d' x y =
        (convolutions' d d').unit.app (x, y) ≫
          (tensorObjIsoConvolution d d').inv.app (x ⊗ y) := by
    cat_disch
  /-- Candidate `tensorHom`. This defaults to the one that corresponds to
  `DayConvolution.map` through `convolutions'`. -/
  tensorHom :
      ∀ {d₁ d₂ : D} {d₁' d₂' : D},
        (d₁ ⟶ d₂) → (d₁' ⟶ d₂') → (tensorObj d₁ d₁' ⟶ tensorObj d₂ d₂') :=
    fun {d₁ d₂} {d₁' d₂' : D} f f' => fullyFaithulι.preimage <|
      (tensorObjIsoConvolution d₁ d₁').hom ≫
        (DayConvolution.map (ι.map f) (ι.map f')) ≫ (tensorObjIsoConvolution d₂ d₂').inv
  /-- Lawfulness of `tensorHom`. -/
  tensorHom_eq :
      ∀ {d₁ d₂ : D} {d₁' d₂' : D} (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂'),
        ι.map (tensorHom f f') = (tensorObjIsoConvolution d₁ d₁').hom ≫
          (DayConvolution.map (ι.map f) (ι.map f')) ≫
          (tensorObjIsoConvolution d₂ d₂').inv := by
    cat_disch
  /-- Candidate tensor unit. -/
  tensorUnit (C) (V) (D) : D
  /-- DayConvolutionUnit structure on the candidate. -/
  tensorUnitConvolutionUnit : DayConvolutionUnit (ι.obj tensorUnit)

namespace InducedLawfulDayConvolutionMonoidalCategoryStructCore

attribute [instance_reducible, local instance] tensorUnitConvolutionUnit

section

variable (D : Type u₃) [Category.{v₃} D]
    [InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D]

set_option backward.isDefEq.respectTransparency false in
variable {D} in
/-- With the data of chosen isomorphic objects to given day convolutions,
and provably equal unit maps through these isomorphisms,
we can transform a given family of Day convolutions to one with
convolutions definitionally equals to the given objects, and component of units
definitionally equal to the provided map family. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.convolutions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.
InducedLawfulDayConvolutionMonoidalCategoryStructCore`。
形式化陈述：convolutions (d d' : D) : DayConvolution ((ι C V D).obj d) ((ι C V D).obj 
d') where convolution
参数：d d' : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
With the data of chosen isomorphic objects to given day convolutions,
and provably equal unit maps through these isomorphisms,
we can transform a given family of Day convolutions to one with
convolutions definitionally equals to the given objects, and component of units
definitionally equal to the provided map family.
-/
def convolutions (d d' : D) :
    DayConvolution ((ι C V D).obj d) ((ι C V D).obj d') where
  convolution := (ι C V D).obj (tensorObj C V d d')
  unit :=
    { app x := convolutionUnitApp V d d' x.1 x.2
      naturality := by
        intros
        simp only [convolutionUnitApp_eq, Category.assoc, NatTrans.naturality_assoc]
        simp }
  isPointwiseLeftKanExtensionUnit :=
    Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
      (StructuredArrow.isoMk
        (tensorObjIsoConvolution C V d d').symm
        (by
          ext ⟨x, y⟩
          simp [convolutionUnitApp_eq V d d' x y]))
      (convolutions' d d' |>.isPointwiseLeftKanExtensionUnit)

attribute [local instance] convolutions

variable
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]

open scoped DayConvolution

/-- Given a fully faithful functor `ι : C ⥤ V ⥤ D`,
a family of Day convolutions, candidate functions for `tensorObj` and `tensorHom`,
suitable isomorphisms
`ι.obj (tensorObj d d') ≅ ι.obj (tensorObj d) ⊛ ι.obj (tensorObj d')`
that behave in a lawful way with respect to the chosen Day convolutions, we can
construct a `MonoidalCategoryStruct` on `D`. -/
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.mkMonoidalCategoryStruct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Mon
oidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStructCore`。
形式化陈述：mkMonoidalCategoryStruct : MonoidalCategoryStruct D where tensorObj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fully faithful functor `ι : C ⥤ V ⥤ D`,
a family of Day convolutions, candidate functions for `tensorObj` and `tensorHom
`,
suitable isomorphisms
`ι.obj (tensorObj d d') ≅ ι.obj (tensorObj d) ⊛ ι.obj (tensorObj d')`
that behave in a lawful way with respect to the chosen Day convolutions, we can
construct a `MonoidalCategoryStruct` on `D`.
-/
abbrev mkMonoidalCategoryStruct : MonoidalCategoryStruct D where
  tensorObj := tensorObj C V
  tensorHom := tensorHom
  tensorUnit := tensorUnit C V D
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  associator x y z :=
    -- To make this work we use the better instance `convolutions`
    letI : DayConvolution (ι C V D |>.obj x) ((ι C V D |>.obj y) ⊛ (ι C V D |>.obj z)) :=
      convolutions C V _ _
    letI : DayConvolution ((ι C V D |>.obj x) ⊛ (ι C V D |>.obj y)) (ι C V D |>.obj z) :=
      convolutions C V _ _
    fullyFaithulι.preimageIso <|
      DayConvolution.associator (ι C V D |>.obj x) (ι C V D |>.obj y) (ι C V D |>.obj z)
  leftUnitor x :=
    letI : DayConvolution (ι C V D |>.obj <| tensorUnit C V D) (ι C V D |>.obj x) :=
      convolutions C V _ _
    fullyFaithulι.preimageIso <|
      DayConvolutionUnit.leftUnitor (ι C V D |>.obj <| tensorUnit C V D) (ι C V D |>.obj x)
  rightUnitor x :=
    letI : DayConvolution (ι C V D |>.obj x) (ι C V D |>.obj <| tensorUnit C V D) :=
      convolutions C V _ _
    fullyFaithulι.preimageIso <|
      DayConvolutionUnit.rightUnitor (ι C V D |>.obj <| tensorUnit C V D) (ι C V D |>.obj x)
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.id_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.
InducedLawfulDayConvolutionMonoidalCategoryStructCore`。
形式化陈述：id_tensorHom (x : D) {y y' : D} (f : y ⟶ y') : letI
参数：x : D；f : y ⟶ y'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_tensorHom (x : D) {y y' : D} (f : y ⟶ y') :
    letI := mkMonoidalCategoryStruct C V D
    (𝟙 x) ⊗ₘ f = x ◁ f :=
  rfl
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.tensorHom_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.
InducedLawfulDayConvolutionMonoidalCategoryStructCore`。
形式化陈述：tensorHom_id {x x' : D} (f : x ⟶ x') (y : D) : letI
参数：f : x ⟶ x'；y : D。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom_id {x x' : D} (f : x ⟶ x') (y : D) :
    letI := mkMonoidalCategoryStruct C V D
    f ⊗ₘ (𝟙 y) = f ▷ y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.InducedLawfu
lDayConvolutionMonoidalCategoryStructCore`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_map_tensorHom_eq {d₁ d₁' d₂ d₂' : D} (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂') :
    letI := mkMonoidalCategoryStruct C V D
    (ι C V D).map (f ⊗ₘ f') =
    DayConvolution.map ((ι C V D).map f) ((ι C V D).map f') := by
  dsimp +instances [mkMonoidalCategoryStruct]
  rw [tensorHom_eq]
  apply (convolutions C V d₁ d₁').corepresentableBy.homEquiv.injective
  dsimp
  ext ⟨u₁, u₂⟩
  dsimp
  simp only [DayConvolution.unit_app_map_app, Functor.comp_obj, tensor_obj]
  simp +instances [convolutions, convolutionUnitApp_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The monoidal category struct constructed in `DayConvolution.mkMonoidalCategoryStruct` extends
to a `LawfulDayConvolutionMonoidalCategoryStruct`. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.mkLawfulDayConvolutionMonoidalCategoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStruc
tCore`。
形式化陈述：mkLawfulDayConvolutionMonoidalCategoryStruct : letI : MonoidalCategoryStru
ct D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category struct constructed in `DayConvolution.mkMonoidalCategorySt
ruct` extends
to a `LawfulDayConvolutionMonoidalCategoryStruct`.
-/
def mkLawfulDayConvolutionMonoidalCategoryStruct :
    letI : MonoidalCategoryStruct D := mkMonoidalCategoryStruct C V D
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : MonoidalCategoryStruct D := mkMonoidalCategoryStruct C V D
  { ι := ι C V D
    faithful_ι := fullyFaithulι.faithful
    convolutionExtensionUnit d d' :=
      (convolutions C V d d').unit
    isPointwiseLeftKanExtensionConvolutionExtensionUnit d d' :=
      (convolutions C V d d').isPointwiseLeftKanExtensionUnit
    unitUnit := tensorUnitConvolutionUnit.can
    isPointwiseLeftKanExtensionUnitUnit :=
      tensorUnitConvolutionUnit.isPointwiseLeftKanExtensionCan
    convolutionExtensionUnit_comp_ι_map_tensorHom_app := by
      intros d₁ d₁' d₂ d₂' f f' x y
      simp [ι_map_tensorHom_eq C V D f f']
    convolutionExtensionUnit_comp_ι_map_whiskerLeft_app := by
      intros d₁ d₂ d₂' f x y
      simp [← id_tensorHom, ι_map_tensorHom_eq C V D]
    convolutionExtensionUnit_comp_ι_map_whiskerRight_app := by
      intros
      simp [← tensorHom_id, ι_map_tensorHom_eq C V D]
    associator_hom_unit_unit d₁ d₂ d₃ x₁ x₂ x₃ := by
      simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj, associator,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      let : DayConvolution (ι C V D |>.obj d₁) ((ι C V D |>.obj d₂) ⊛ (ι C V D |>.obj d₃)) :=
        convolutions C V _ _
      let : DayConvolution ((ι C V D |>.obj d₁) ⊛ (ι C V D |>.obj d₂)) (ι C V D |>.obj d₃) :=
        convolutions C V _ _
      apply DayConvolution.associator_hom_unit_unit
    leftUnitor_hom_unit_app _ _ := by
      simp only [Functor.comp_obj, tensor_obj, leftUnitor,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      apply DayConvolutionUnit.leftUnitor_hom_unit_app
    rightUnitor_hom_unit_app _ _ := by
      simp only [Functor.comp_obj, tensor_obj, rightUnitor,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      apply DayConvolutionUnit.rightUnitor_hom_unit_app }

end

variable {C V} in
/-- Given a fully faithful functor `ι : D ⥤ C ⥤ V` and mere existence of Day convolutions of
`ι.obj d` and `ι.obj d'` such that the convolution remains in the essential image of `ι`,
construct an `InducedLawfulDayConvolutionMonoidalCategoryStructCore` by letting all other
data be the generic ones from the `HasPointwiseLeftKanExtension` API. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.InducedLawfulDayConvolutionMonoidalCategoryStr
uctCore.ofHasDayConvolutions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalC
ategory.InducedLawfulDayConvolutionMonoidalCategoryStructCore`。
形式化陈述：ofHasDayConvolutions {D : Type u₃} [Category.{v₃} D] (ι : D ⥤ C ⥤ V) (ffι 
: ι.FullyFaithful) [hasDayConvolution : forall (d d' : D), (tensor C).HasPointwi
seLeftKanExtension (ι.obj d ⊠ ι.obj d')] (essImageDayConvolution : forall (d d' 
: D), ι.essImage (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')) [has
DayConvolutionUnit : (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtensio
n (Functor.fromPUnit.{0} <| 𝟙_ V)] (essImageDayConvolutionUnit : ι.essImage (Fun
ctor.fromPUnit.{0} <| 𝟙_ C
参数：ι : D ⥤ C ⥤ V；ffι : ι.FullyFaithful；d d' : D；tensor C；ι.obj d ⊠ ι.obj d'；essI
mageDayConvolution : forall (d d' : D), ι.essImage (tensor C).pointwiseLeftKanEx
tension (ι.obj d ⊠ ι.obj d')；Functor.fromPUnit.{0} <| 𝟙_ C；Functor.fromPUnit.{0}
 <| 𝟙_ V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fully faithful functor `ι : D ⥤ C ⥤ V` and mere existence of Day convolu
tions of
`ι.obj d` and `ι.obj d'` such that the convolution remains in the essential imag
e of `ι`,
construct an `InducedLawfulDayConvolutionMonoidalCategoryStructCore` by letting 
all other
data be the generic ones from the `HasPointwiseLeftKanExtension` API.
-/
noncomputable def ofHasDayConvolutions
    {D : Type u₃} [Category.{v₃} D]
    (ι : D ⥤ C ⥤ V)
    (ffι : ι.FullyFaithful)
    [hasDayConvolution : ∀ (d d' : D),
      (tensor C).HasPointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')]
    (essImageDayConvolution : ∀ (d d' : D),
      ι.essImage <| (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d'))
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    (essImageDayConvolutionUnit :
      ι.essImage <|
        (Functor.fromPUnit.{0} <| 𝟙_ C).pointwiseLeftKanExtension
          (Functor.fromPUnit.{0} <| 𝟙_ V)) :
    InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D where
  ι := ι
  fullyFaithulι := ffι
  tensorObj := fun d d' ↦ essImageDayConvolution d d' |>.witness
  convolutions' := fun d d' ↦
    { convolution := (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')
      unit := (tensor C).pointwiseLeftKanExtensionUnit (ι.obj d ⊠ ι.obj d')
      isPointwiseLeftKanExtensionUnit :=
        (tensor C).pointwiseLeftKanExtensionIsPointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d') }
  tensorObjIsoConvolution := fun d d' => Functor.essImage.getIso _
  tensorUnit := essImageDayConvolutionUnit.witness
  tensorUnitConvolutionUnit :=
    { can :=
        ((Functor.fromPUnit.{0} <| 𝟙_ C).pointwiseLeftKanExtensionUnit
            (Functor.fromPUnit.{0} <| 𝟙_ V)).app (.mk PUnit.unit) ≫
          (essImageDayConvolutionUnit.getIso.inv.app (𝟙_ C))
      isPointwiseLeftKanExtensionCan :=
        Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
        (StructuredArrow.isoMk
          (essImageDayConvolutionUnit.getIso).symm)
        (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
          (Functor.fromPUnit.{0} <| 𝟙_ C)
          (Functor.fromPUnit.{0} <| 𝟙_ V)) }

end InducedLawfulDayConvolutionMonoidalCategoryStructCore

section

variable {C V}
    {D : Type u₃} [Category.{v₃} D]
    (ι : D ⥤ C ⥤ V)
    (ffι : ι.FullyFaithful)
    [hasDayConvolution : ∀ (d d' : D),
      (tensor C).HasPointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')]
    (essImageDayConvolution : ∀ (d d' : D),
      ι.essImage <| (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d'))
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    (essImageDayConvolutionUnit :
      ι.essImage <|
        (Functor.fromPUnit.{0} <| 𝟙_ C).pointwiseLeftKanExtension
          (Functor.fromPUnit.{0} <| 𝟙_ V))
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [∀ (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-- Under suitable assumptions on existence of relevant Kan extensions and preservation
of relevant colimits by the tensor product of `V`, we can define a `MonoidalCategory D`
from the data of a fully faithful functor `ι : D ⥤ C ⥤ V` whose essential image
contains a Day convolution unit and is stable under binary Day convolutions. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.monoidalOfHasDayConvolutions** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：monoidalOfHasDayConvolutions : MonoidalCategory D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Under suitable assumptions on existence of relevant Kan extensions and preservat
ion
of relevant colimits by the tensor product of `V`, we can define a `MonoidalCate
gory D`
from the data of a fully faithful functor `ι : D ⥤ C ⥤ V` whose essential image
contains a Day convolution unit and is stable under binary Day convolutions.
-/
noncomputable def monoidalOfHasDayConvolutions : MonoidalCategory D :=
  letI induced : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit
  letI := induced.mkMonoidalCategoryStruct
  letI : LawfulDayConvolutionMonoidalCategoryStruct C V D :=
    induced.mkLawfulDayConvolutionMonoidalCategoryStruct
  monoidalOfLawfulDayConvolutionMonoidalCategoryStruct C V D

open InducedLawfulDayConvolutionMonoidalCategoryStructCore in
/-- The monoidal category constructed via `monoidalOfHasDayConvolutions` has a canonical
`LawfulDayConvolutionMonoidalCategoryStruct C V D`. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalCategory.lawfulDayConvolutionMonoidalCategoryStructOfHa
sDayConvolutions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions : letI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category constructed via `monoidalOfHasDayConvolutions` has a canon
ical
`LawfulDayConvolutionMonoidalCategoryStruct C V D`.
-/
noncomputable def lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions :
    letI := monoidalOfHasDayConvolutions
      ι ffι essImageDayConvolution essImageDayConvolutionUnit
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit
  letI := monoidalOfHasDayConvolutions
    ι ffι essImageDayConvolution essImageDayConvolutionUnit
  mkLawfulDayConvolutionMonoidalCategoryStruct C V D

end

end

end

end CategoryTheory.MonoidalCategory

