/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Braidings for Day convolution

In this file, we show that if `C` is a braided monoidal category and
`V` also a braided monoidal category, then the Day convolution monoidal structure
on `C ⥤ V` is also braided monoidal. We prove it by constructing an explicit
braiding isomorphism whenever sufficient Day convolutions exist, and we
prove that it satisfies the forward and reverse hexagon identities.

Furthermore, we show that when both `C` and `V` are symmetric monoidal
categories, then the Day convolution monoidal structure is symmetric as well.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.MonoidalCategory.DayConvolution
open scoped ExternalProduct
open Opposite

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory V] [BraidedCategory V]
  (F G : C ⥤ V)

section

variable [DayConvolution F G] [DayConvolution G F]

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.braidingHomCorepresenting** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：braidingHomCorepresenting : F ⊠ G ⟶ tensor C ⋙ G ⊛ F where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`.
-/
def braidingHomCorepresenting : F ⊠ G ⟶ tensor C ⋙ G ⊛ F where
  app _ := (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_ _ _).hom
  naturality {x y} f := by simp [tensorHom_def, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.braidingInvCorepresenting** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：braidingInvCorepresenting : G ⊠ F ⟶ tensor C ⋙ F ⊛ G where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `F ⊠ G ⟶ (tensor C) ⋙ (G ⊛ F)` that corepresents
the braiding morphism `F ⊛ G ⟶ G ⊛ F`.
-/
def braidingInvCorepresenting : G ⊠ F ⟶ tensor C ⋙ F ⊛ G where
  app _ := (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_ _ _).inv
  naturality {x y} f := by simp [tensorHom_def, ← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism for Day convolution. -/
/-
**CategoryTheory.MonoidalCategory.DayConvolution.braiding** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：braiding : F ⊛ G ≅ G ⊛ F where .homEquiv.symm braidingHomCorepresenting F 
G hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The braiding isomorphism for Day convolution.
-/
def braiding : F ⊛ G ≅ G ⊛ F where
  hom := corepresentableBy F G |>.homEquiv.symm <| braidingHomCorepresenting F G
  inv := corepresentableBy G F |>.homEquiv.symm <| braidingInvCorepresenting F G
  hom_inv_id := by
    apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G) (unit F G)
    ext
    simp [-tensor_obj]
  inv_hom_id := by
    apply Functor.hom_ext_of_isLeftKanExtension (G ⊛ F) (unit G F)
    ext
    simp [-tensor_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：unit_app_braiding_hom_app (x y : C) : (unit F G).app (x, y) ≫ (braiding F 
G).hom.app (x otimes y) = (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_
 _ _).hom
参数：x y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unit_app_braiding_hom_app (x y : C) :
    (unit F G).app (x, y) ≫ (braiding F G).hom.app (x ⊗ y) =
    (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (G ⊛ F).map (β_ _ _).hom := by
  change
    (unit F G).app (x, y) ≫ (braiding F G).hom.app ((tensor C).obj (x, y)) = _
  simp [braiding, braidingHomCorepresenting, -tensor_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_inv_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：unit_app_braiding_inv_app (x y : C) : (unit G F).app (x, y) ≫ (braiding F 
G).inv.app (x otimes y) = (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_
 _ _).inv
参数：x y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac_app`：descOfIsLeftKan
Extension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) : α.app X ≫ (F'.descOfIsLe
ftKanExtension α G β).app (L.obj X) = β.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unit_app_braiding_inv_app (x y : C) :
    (unit G F).app (x, y) ≫ (braiding F G).inv.app (x ⊗ y) =
    (β_ _ _).inv ≫ (unit F G).app (_, _) ≫ (F ⊛ G).map (β_ _ _).inv := by
  change
    (unit G F).app (x, y) ≫ (braiding F G).inv.app ((tensor C).obj (x, y)) = _
  simp [braiding, braidingHomCorepresenting, -tensor_obj]

end

variable {F G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.braiding_naturality_right** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：braiding_naturality_right (H : C ⥤ V) (η : F ⟶ G) [DayConvolution F H] [Da
yConvolution H F] [DayConvolution G H] [DayConvolution H G] : DayConvolution.map
 (𝟙 H) η ≫ (braiding H G).hom = (braiding H F).hom ≫ DayConvolution.map η (𝟙 H)
参数：H : C ⥤ V；η : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
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
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
`：unit_app_braiding_hom_app (x y : C) : (unit F G).app (x, y) ≫ (braiding F G).h
om.app (x otimes y) = (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right_assoc`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoid
alCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂
} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma braiding_naturality_right (H : C ⥤ V) (η : F ⟶ G)
    [DayConvolution F H] [DayConvolution H F]
    [DayConvolution G H] [DayConvolution H G] :
    DayConvolution.map (𝟙 H) η ≫ (braiding H G).hom =
    (braiding H F).hom ≫ DayConvolution.map η (𝟙 H) := by
  apply Functor.hom_ext_of_isLeftKanExtension (H ⊛ F) (unit H F)
  ext ⟨_, _⟩
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.DayConvolution.braiding_naturality_left** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：braiding_naturality_left (η : F ⟶ G) (H : C ⥤ V) [DayConvolution F H] [Day
Convolution H F] [DayConvolution G H] [DayConvolution H G] : DayConvolution.map 
η (𝟙 H) ≫ (braiding G H).hom = (braiding F H).hom ≫ DayConvolution.map (𝟙 H) η
参数：η : F ⟶ G；H : C ⥤ V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
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
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
`：unit_app_braiding_hom_app (x y : C) : (unit F G).app (x, y) ≫ (braiding F G).h
om.app (x otimes y) = (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left_assoc`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoida
lCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂
} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma braiding_naturality_left (η : F ⟶ G) (H : C ⥤ V)
    [DayConvolution F H] [DayConvolution H F]
    [DayConvolution G H] [DayConvolution H G] :
    DayConvolution.map η (𝟙 H) ≫ (braiding G H).hom =
    (braiding F H).hom ≫ DayConvolution.map (𝟙 H) η := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ H) (unit F H)
  ext ⟨_, _⟩
  simp

variable
  [∀ (v : V) (d : C),
    Limits.PreservesColimitsOfShape (CostructuredArrow (tensor C) d) (tensorLeft v)]
  [∀ (v : V) (d : C),
    Limits.PreservesColimitsOfShape (CostructuredArrow (tensor C) d) (tensorRight v)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F G) in
/-
**CategoryTheory.MonoidalCategory.DayConvolution.hexagon_forward** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：hexagon_forward (H : C ⥤ V) [DayConvolution F G] [DayConvolution G H] [Day
Convolution F (G ⊛ H)] [DayConvolution (F ⊛ G) H] [DayConvolution H F] [DayConvo
lution G (H ⊛ F)] [DayConvolution (G ⊛ H) F] [DayConvolution G F] [DayConvolutio
n (G ⊛ F) H] [DayConvolution F H] [DayConvolution G (F ⊛ H)] : (associator F G H
).hom ≫ (braiding F (G ⊛ H)).hom ≫ (associator G H F).hom = (DayConvolution.map 
(braiding F G).hom (𝟙 H)) ≫ (associator G F H).hom ≫ (DayConvolution.map (𝟙 G) (
braiding F H).hom)
参数：H : C ⥤ V；G ⊛ H；F ⊛ G；H ⊛ F；G ⊛ H；G ⊛ F；F ⊛ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitLeftUnit`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_hom_unit_unit_
assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂
} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Iso.map_hom_inv_id`：map_hom_inv_id (F : C ⥤ D) : F.map e.
hom ≫ F.map e.inv = 𝟙 _
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right_assoc`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoid
alCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `CategoryTheory.Iso.map_inv_hom_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
`：unit_app_braiding_hom_app (x y : C) : (unit F G).app (x, y) ≫ (braiding F G).h
om.app (x otimes y) = (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.whiskerRight_comp_unit_ap
p_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u
₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
（共 40 条，此处仅展示前 30 条）
-/
lemma hexagon_forward (H : C ⥤ V)
    [DayConvolution F G] [DayConvolution G H] [DayConvolution F (G ⊛ H)]
    [DayConvolution (F ⊛ G) H] [DayConvolution H F] [DayConvolution G (H ⊛ F)]
    [DayConvolution (G ⊛ H) F] [DayConvolution G F] [DayConvolution (G ⊛ F) H]
    [DayConvolution F H] [DayConvolution G (F ⊛ H)] :
    (associator F G H).hom ≫ (braiding F (G ⊛ H)).hom ≫ (associator G H F).hom =
    (DayConvolution.map (braiding F G).hom (𝟙 H)) ≫ (associator G F H).hom ≫
      (DayConvolution.map (𝟙 G) (braiding F H).hom) := by
  apply Functor.hom_ext_of_isLeftKanExtension ((F ⊛ G) ⊛ H) (unit _ H)
  apply Functor.hom_ext_of_isLeftKanExtension ((F ⊛ G) ⊠ H)
    (ExternalProduct.extensionUnitLeft (F ⊛ G) (unit F G) H)
  ext ⟨⟨x, y⟩, z⟩
  dsimp
  simp only [whiskerLeft_id, Category.comp_id, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, tensor_obj, NatTrans.naturality_assoc,
    NatTrans.naturality, unit_app_braiding_hom_app_assoc,
    BraidedCategory.braiding_tensor_left_hom, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom, Iso.map_inv_hom_id_assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, unit_app_map_app_assoc,
    NatTrans.id_app, tensorHom_id]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    unit_app_braiding_hom_app]
  simp only [whiskerLeft_comp, ← Functor.map_comp, Category.assoc,
    Functor.comp_obj, tensor_obj, comp_whiskerRight,
    whiskerRight_comp_unit_app_assoc, NatTrans.naturality_assoc,
    NatTrans.naturality, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, unit_app_map_app_assoc, NatTrans.id_app,
    id_tensorHom]
  rw [← BraidedCategory.hexagon_reverse, ← whiskerLeft_comp_assoc]
  have := unit_app_braiding_hom_app F H x z =≫ (H ⊛ F).map (β_ z x).inv
  dsimp at this
  simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
  rw [← this, whiskerLeft_comp_assoc]
  simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F G) in
/-
**CategoryTheory.MonoidalCategory.DayConvolution.hexagon_reverse** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：hexagon_reverse (H : C ⥤ V) [DayConvolution F G] [DayConvolution G H] [Day
Convolution F (G ⊛ H)] [DayConvolution (F ⊛ G) H] [DayConvolution H (F ⊛ G)] [Da
yConvolution H F] [DayConvolution (H ⊛ F) G] [DayConvolution H G] [DayConvolutio
n F (H ⊛ G)] [DayConvolution F H] [DayConvolution (F ⊛ H) G] : (associator F G H
).inv ≫ (braiding (F ⊛ G) H).hom ≫ (associator H F G).inv = (DayConvolution.map 
(𝟙 F) (braiding G H).hom) ≫ (associator F H G).inv ≫ (DayConvolution.map (braidi
ng F H).hom (𝟙 G))
参数：H : C ⥤ V；G ⊛ H；F ⊛ G；F ⊛ G；H ⊛ F；H ⊛ G；F ⊛ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.instIsLeftKanExtensionPro
dExternalProductConvolutionExtensionUnitRightUnit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.associator_inv_unit_unit_
assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂}
 [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂
} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left_assoc`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoida
lCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.Iso.map_hom_inv_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app_assoc`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
`：unit_app_braiding_hom_app (x y : C) : (unit F G).app (x, y) ≫ (braiding F G).h
om.app (x otimes y) = (β_ _ _).hom ≫ (unit G F).app (_, _) ≫ (…
（共 43 条，此处仅展示前 30 条）
-/
lemma hexagon_reverse (H : C ⥤ V)
    [DayConvolution F G] [DayConvolution G H] [DayConvolution F (G ⊛ H)]
    [DayConvolution (F ⊛ G) H] [DayConvolution H (F ⊛ G)] [DayConvolution H F]
    [DayConvolution (H ⊛ F) G] [DayConvolution H G] [DayConvolution F (H ⊛ G)]
    [DayConvolution F H] [DayConvolution (F ⊛ H) G] :
    (associator F G H).inv ≫ (braiding (F ⊛ G) H).hom ≫ (associator H F G).inv =
    (DayConvolution.map (𝟙 F) (braiding G H).hom) ≫ (associator F H G).inv ≫
      (DayConvolution.map (braiding F H).hom (𝟙 G)) := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G ⊛ H) (unit _ _)
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊠ (G ⊛ H))
    (ExternalProduct.extensionUnitRight (G ⊛ H) (unit G H) F)
  ext ⟨x, y, z⟩
  dsimp
  simp only [whiskerRight_tensor, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, associator_inv_unit_unit_assoc,
    externalProductBifunctor_obj_obj, tensor_obj, NatTrans.naturality_assoc,
    NatTrans.naturality, unit_app_braiding_hom_app_assoc,
    BraidedCategory.braiding_tensor_right_hom, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id, Category.comp_id,
    BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_tensor_left_hom, Iso.map_hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, unit_app_map_app_assoc,
    NatTrans.id_app, id_tensorHom]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    unit_app_braiding_hom_app]
  simp only [comp_whiskerRight, ← Functor.map_comp, Category.assoc, Functor.comp_obj, tensor_obj,
    whiskerLeft_comp, whiskerLeft_comp_unit_app_assoc, NatTrans.naturality_assoc,
    NatTrans.naturality, associator_inv_unit_unit_assoc, externalProductBifunctor_obj_obj,
    unit_app_map_app_assoc, NatTrans.id_app, tensorHom_id]
  congr 2
  rw [← BraidedCategory.hexagon_forward, ← comp_whiskerRight_assoc]
  have := unit_app_braiding_hom_app F H x z =≫ (H ⊛ F).map (β_ z x).inv
  dsimp at this
  simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id] at this
  rw [← this, comp_whiskerRight_assoc]
  simp [← Functor.map_comp]

end

section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalCategory V] [SymmetricCategory V]
  (F G : C ⥤ V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.DayConvolution.symmetry** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MonoidalCategory.DayConvolution`。
形式化陈述：symmetry [DayConvolution F G] [DayConvolution G F] : (braiding F G).hom ≫ 
(braiding G F).hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.hom_ext_of_isLeftKanExtension`：hom_ext_of_isLeftK
anExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G) (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiske
rLeft L γ₂) : γ₁ = γ₂
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
· 使用定理 `CategoryTheory.MonoidalCategory.DayConvolution.unit_app_braiding_hom_app
_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {V : Type u₂
} [inst_1 : CategoryTheory.Category.{v₂, u₂} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   [self
 : CategoryTheory.SymmetricCate…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symmetry [DayConvolution F G] [DayConvolution G F] :
    (braiding F G).hom ≫ (braiding G F).hom = 𝟙 _ := by
  apply Functor.hom_ext_of_isLeftKanExtension (F ⊛ G) (unit F G)
  ext ⟨x, y⟩
  simp [← Functor.map_comp]

end

end CategoryTheory.MonoidalCategory.DayConvolution

