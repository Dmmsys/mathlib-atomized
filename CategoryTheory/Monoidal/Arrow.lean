/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Limits.HasLimits
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Monoidal structure on the arrow category of a cartesian closed category.

If `C` is a braided, cartesian closed category with pushouts and an initial object, then `Arrow C`
has a symmetric monoidal category structure given by the pushout-product (the Leibniz construction
given by the tensor product on `C`).

If `C` also has pullbacks, then `Arrow C` has a monoidal closed structure given by the pullback-hom
(the Leibniz construction given by the internal hom on `C`).

-/

public section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory CategoryTheory.Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

attribute [local simp] PushoutObjObj.ι ofHasPushout_pt ofHasPushout_inl ofHasPushout_inr

namespace MonoidalCategory.Arrow.PushoutProduct

noncomputable section

/-- The monoidal category instance induced by the pushout-product. -/
@[simps]
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category instance induced by the pushout-product.
-/
scoped instance [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : MonoidalCategoryStruct (Arrow C) where
  tensorObj X Y := X □ Y
  whiskerLeft X _ _ f := (pushoutProduct.obj X).map f
  whiskerRight f X := (pushoutProduct.map f).app X
  tensorUnit := initial.to (𝟙_ C)
  associator _ _ _ := PushoutProduct.associator ..
  leftUnitor := PushoutProduct.leftUnitor
  rightUnitor := PushoutProduct.rightUnitor

variable [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.tensorHom_comp_tensorHom*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`
。
形式化陈述：tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Arrow C} (f₁ : X₁ ⟶ Y₁) (f₂ 
: X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (
f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；g₁ : Y₁ ⟶ Z₁；g₂ : Y₂ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsPushout.inl_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPushout.inr_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
-/
lemma tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Arrow C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  refine Arrow.hom_ext _ _ ?_ (by simp [whisker_exchange_assoc])
  apply pushout.hom_ext <;> simp [whisker_exchange_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_naturality** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C} (f₁ : X₁ ⟶ Y₁) (f₂ : X
₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ 
X₁ X₂ X₃).hom ≫ (f₁ otimesₘ (f₂ otimesₘ f₃))
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory
.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用引理 `CategoryTheory.Functor.PushoutObjObj.mapArrowLeft_comp`：mapArrowLeft_com
p {f₁'' : Arrow C₁} (sq₁₂'' : F.PushoutObjObj f₁''.hom f₂.hom) (sq : f₁ ⟶ f₁') (
sq' : f₁' ⟶ f₁'') : mapArrowLeft sq₁₂ sq₁₂' …
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_hom_left
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasPushouts C]   [inst_2 : CategoryTheory.MonoidalC…
· 使用定理 `CategoryTheory.IsPushout.inl_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inl_desc_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
MonoidalCategory C] {Z X Y P : C}   {f : Z ⟶ X} {g : Z ⟶ Y…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
· 使用定理 `CategoryTheory.Functor.map_isPushout`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
（共 71 条，此处仅展示前 30 条）
-/
lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext (by simp [whisker_exchange_assoc]) ?_) (by simp)
  apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
  · suffices _ ◁ _ ◁ f₃.right ≫ (α_ _ _ _).inv ≫ f₁.right ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
      _ ◁ f₂.left ▷ _ ≫ _ ◁ pushout.inr _ _ = _ ◁ f₂.left ▷ _ ≫ _ ◁ _ ◁ f₃.right ≫
      _ ◁ pushout.inr _ _ ≫ f₁.right ▷ pushout (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) by
      simp [← whisker_exchange_assoc, reassoc_of% this]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange, whisker_exchange_assoc,
      ← whisker_exchange, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      ← associator_inv_naturality_left_assoc, associator_naturality_right_assoc,
      Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  · suffices ((α_ _ _ _).hom ≫ _ ◁ _ ◁ f₃.right ≫ (α_ _ _ _).inv ≫ f₁.left ▷ _ ▷ _ ≫
      (α_ _ _ _).hom ≫ _ ◁ f₂.right ▷ _ = f₁.left ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
      _ ◁ f₂.right ▷ _ ≫ _ ◁ _ ◁ f₃.right) by
      simp [← whisker_exchange_assoc, reassoc_of% this]
    cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.leftUnitor_naturality** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：leftUnitor_naturality {X Y : Arrow C} (f : X ⟶ Y) : 𝟙_ _ ◁ f ≫ (fun_ Y).ho
m = (fun_ X).hom ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
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
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory
.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.IsPushout.inl_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.braiding_tensorUnit_left`：braiding_tensorUnit_left (X : C
) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc_assoc`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma leftUnitor_naturality {X Y : Arrow C} (f : X ⟶ Y) :
    𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext (by simp) ?_) (by simp)
  apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.rightUnitor_naturality** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：rightUnitor_naturality {X Y : Arrow C} (f : X ⟶ Y) : f ▷ 𝟙_ _ ≫ (ρ_ Y).hom
 = (ρ_ X).hom ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `CategoryTheory.IsPushout.inr_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_naturality {X Y : Arrow C} (f : X ⟶ Y) :
    f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext ?_ (by simp)) (by simp)
  apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.pentagon** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：pentagon (W X Y Z : Arrow C) : (α_ W X Y).hom ▷ Z ≫ (α_ W (X otimes Y) Z).
hom ≫ W ◁ (α_ X Y Z).hom = (α_ (W otimes X) Y Z).hom ≫ (α_ W X (Y otimes Z)).hom
参数：W X Y Z : Arrow C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory
.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Limits.pushout.desc.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPushout …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_hom_left
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasPushouts C]   [inst_2 : CategoryTheory.MonoidalC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `CategoryTheory.IsPushout.inl_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `CategoryTheory.MonoidalCategory.Limits.colimit.whiskerLeft_ι_desc_assoc`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.MonoidalCategory C] {J : Type u₁}   [inst_2 : CategoryTheo…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_assoc`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (W X Y 
Z : C) {Z_1 : C}   (h :     Category…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.IsPushout.isoPushout.congr_simp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl i
nl_1 : X ⟶ P}   (e_inl : inl = inl_1…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
· 使用定理 `CategoryTheory.Functor.map_isPushout`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
（共 46 条，此处仅展示前 30 条）
-/
lemma pentagon (W X Y Z : Arrow C) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext (by simp) ?_) (by simp)
  apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext (by simp)
  apply ((tensorRight _ ⋙ tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;>
  simp [associator_naturality_left_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.triangle** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：triangle (X Y : Arrow C) : (α_ X (𝟙_ _) Y).hom ≫ X ◁ (fun_ Y).hom = (ρ_ X)
.hom ▷ Y
参数：X Y : Arrow C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory
.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Limits.pushout.desc.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPushout …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.braiding_tensorUnit_left`：braiding_tensorUnit_left (X : C
) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_hom_left
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasPushouts C]   [inst_2 : CategoryTheory.MonoidalC…
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `CategoryTheory.MonoidalCategory.Limits.whiskerLeft_inl_comp_pushoutSymme
try_hom_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 
: CategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.MonoidalCategory.Limits.colimit.whiskerLeft_ι_desc_assoc`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.MonoidalCategory C] {J : Type u₁}   [inst_2 : CategoryTheo…
· 使用定理 `CategoryTheory.MonoidalCategory.triangle_assoc`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C) {Z : C}   (h : CategoryTheory.Mon…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
· 使用定理 `CategoryTheory.Functor.map_isPushout`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
（共 40 条，此处仅展示前 30 条）
-/
lemma triangle (X Y : Arrow C) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext (by simp) ?_) (by simp)
  apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
  · apply (initialIsInitial.ofIso ((initialIsoIsInitial ?_) ≪≫ (mulZero ?_).symm)).hom_ext <;>
    exact initialIsInitial.ofIso (zeroMul initialIsInitial).symm
  · simp [← comp_whiskerRight_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The monoidal category instance induced by the pushout-product. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category instance induced by the pushout-product.
-/
scoped instance : MonoidalCategory (Arrow C) where
  tensorHom_comp_tensorHom := tensorHom_comp_tensorHom
  associator_naturality := associator_naturality
  leftUnitor_naturality := leftUnitor_naturality
  rightUnitor_naturality := rightUnitor_naturality
  pentagon := pentagon
  triangle := triangle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hexagon_forward** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：hexagon_forward (X Y Z : Arrow C) : (α_ X Y Z).hom ≫ (braiding X (Y otimes
 Z)).hom ≫ (α_ Y Z X).hom = ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (br
aiding X Z).hom)
参数：X Y Z : Arrow C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory
.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_hom_left
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasPushouts C]   [inst_2 : CategoryTheory.MonoidalC…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right_assoc`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoid
alCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_hom_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {in
l : X ⟶ P}   {inr : Y ⟶ P} (h : Categor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
· 使用定理 `CategoryTheory.IsPushout.inl_desc_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}
   {inr : Y ⟶ P} (hP : Catego…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `CategoryTheory.MonoidalCategory.Limits.whiskerLeft_inl_comp_pushoutSymme
try_hom_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 
: CategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.MonoidalCategory.Limits.HasColimit.whiskerLeft_isoOfNatIs
o_ι_hom_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 
: CategoryTheory.MonoidalCategory C] {J : Type u₁}   [inst_2 : CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
（共 47 条，此处仅展示前 30 条）
-/
lemma hexagon_forward (X Y Z : Arrow C) :
    (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext (by simp) ?_) (by simp)
  apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hexagon_reverse** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：hexagon_reverse (X Y Z : Arrow C) : (α_ X Y Z).inv ≫ (braiding (X otimes Y
) Z).hom ≫ (α_ Z X Y).inv = (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braidi
ng X Z).hom ▷ Y)
参数：X Y Z : Arrow C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用引理 `CategoryTheory.IsPushout.hom_ext`：hom_ext (hP : IsPushout f g inl inr) {
W : C} {k l : P ⟶ W} (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
· 使用定理 `CategoryTheory.Functor.map_isPushout`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesColimitsTensorLeft`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A
 : C)   [CategoryTheory.Closed A], C…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory
.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_inv_left
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryThe
ory.Limits.HasPushouts C]   [inst_2 : CategoryTheory.MonoidalC…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_hom_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {in
l : X ⟶ P}   {inr : Y ⟶ P} (h : Categor…
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.IsPushout.desc.congr_simp`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {Z X Y P : C} {f f_1 : Z ⟶ X} (e_f : f = f_1)   {g
 g_1 : Z ⟶ Y} (e_g : g = g_1) …
（共 46 条，此处仅展示前 30 条）
-/
lemma hexagon_reverse (X Y Z : Arrow C) :
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
  refine Arrow.hom_ext _ _ (pushout.hom_ext ?_ (by simp)) (by simp)
  apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The braided category instance induced by the pushout-product. -/
@[simps -isSimp]
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.braidedCategory** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPushouts C] →       [inst_2 : CategoryTheory.Limits.Ha
sInitial C] →         [inst_3 : CategoryTheory.CartesianMonoidalCategory C] →   
        [inst_4 : CategoryTheory.MonoidalClosed C] →             [inst_5 : Categ
oryTheory.BraidedCategory C] → CategoryTheory.BraidedCategory (CategoryTheory.Ar
row C)
参数：CategoryTheory.Arrow C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hexagon_forward`：he
xagon_forward (X Y Z : Arrow C) : (α_ X Y Z).hom ≫ (braiding X (Y otimes Z)).hom
 ≫ (α_ Y Z X).hom = ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).…
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hexagon_reverse`：he
xagon_reverse (X Y Z : Arrow C) : (α_ X Y Z).inv ≫ (braiding (X otimes Y) Z).hom
 ≫ (α_ Z X Y).inv = (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).…

--- 原说明 ---
The braided category instance induced by the pushout-product.
-/
scoped instance braidedCategory : BraidedCategory (Arrow C) where
  braiding := braiding
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] braidedCategory_braiding in
/-- The symmetric category instance induced by the pushout-product. -/
@[simps! -isSimp]
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.symmetricCategory** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPushouts C] →       [inst_2 : CategoryTheory.Limits.Ha
sInitial C] →         [inst_3 : CategoryTheory.CartesianMonoidalCategory C] →   
        [inst_4 : CategoryTheory.MonoidalClosed C] →             [inst_5 : Categ
oryTheory.BraidedCategory C] → CategoryTheory.SymmetricCategory (CategoryTheory.
Arrow C)
参数：CategoryTheory.Arrow C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetric category instance induced by the pushout-product.
-/
scoped instance symmetricCategory : SymmetricCategory (Arrow C) where

/-- The monoidal closed instance induced by the pushout-product and pullback-hom. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal closed instance induced by the pushout-product and pullback-hom.
-/
scoped instance [HasPullbacks C] : MonoidalClosed (Arrow C) where
  closed X := {
    rightAdj := pullbackHom.obj (Opposite.op X)
    adj := LeibnizAdjunction.adj _ _ (MonoidalClosed.internalHomAdjunction₂) X }

end

end MonoidalCategory.Arrow.PushoutProduct

end CategoryTheory

