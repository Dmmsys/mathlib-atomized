/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.HomCongr

/-!
# Bijections between morphisms in two localized categories

Given two localization functors `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` for the same
class of morphisms `W : MorphismProperty C`, we define a bijection
`Localization.homEquiv W L₁ L₂ : (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y)`
between the types of morphisms in the two localized categories.

More generally, given a localizer morphism `Φ : LocalizerMorphism W₁ W₂`, we define a map
`Φ.homMap L₁ L₂ : (L₁.obj X ⟶ L₁.obj Y) ⟶ (L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y))`.
The definition `Localization.homEquiv` is obtained by applying the construction
to the identity localizer morphism.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C]
  [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace LocalizerMorphism

variable {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {W₃ : MorphismProperty C₃}
  (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃)
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
  (L₃ : C₃ ⥤ D₃) [L₃.IsLocalization W₃]
  {X Y Z : C₁}

/-- If `Φ : LocalizerMorphism W₁ W₂` is a morphism of localizers, `L₁` and `L₂`
are localization functors for `W₁` and `W₂`, then this is the induced map
`(L₁.obj X ⟶ L₁.obj Y) ⟶ (L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y))`
for all objects `X` and `Y`. -/
/-
**CategoryTheory.LocalizerMorphism.homMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.LocalizerMorphism`。
形式化陈述：homMap (f : L₁.obj X ⟶ L₁.obj Y) : L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.fu
nctor.obj Y)
参数：f : L₁.obj X ⟶ L₁.obj Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ : LocalizerMorphism W₁ W₂` is a morphism of localizers, `L₁` and `L₂`
are localization functors for `W₁` and `W₂`, then this is the induced map
`(L₁.obj X ⟶ L₁.obj Y) ⟶ (L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y))`
for all objects `X` and `Y`.
-/
noncomputable def homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y) :=
  Iso.homCongr ((CatCommSq.iso _ _ _ _).symm.app _) ((CatCommSq.iso _ _ _ _).symm.app _)
    ((Φ.localizedFunctor L₁ L₂).map f)

@[simp]
/-
**CategoryTheory.LocalizerMorphism.homMap_map** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.LocalizerMorphism`。
形式化陈述：homMap_map (f : X ⟶ Y) : Φ.homMap L₁ L₂ (L₁.map f) = L₂.map (Φ.functor.map
 f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.homCongr_apply`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y),   (α.
homCongr β) f = Categor…
· 使用引理 `CategoryTheory.CatCommSq.iso_inv_naturality`：iso_inv_naturality [h : Cat
CommSq T L R B] {x y : C₁} (f : x ⟶ y) : B.map (L.map f) ≫ (iso T L R B).inv.app
 y = (iso T L R B).inv.app x ≫ R.…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homMap_map (f : X ⟶ Y) :
    Φ.homMap L₁ L₂ (L₁.map f) = L₂.map (Φ.functor.map f) := by
  dsimp [homMap]
  simp

variable (X) in
@[simp]
/-
**CategoryTheory.LocalizerMorphism.homMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.LocalizerMorphism`。
形式化陈述：homMap_id : Φ.homMap L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj (Φ.functor.obj X))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.LocalizerMorphism.homMap.congr_simp`：∀ {C₁ : Type u_2} {C
₂ : Type u_3} {D₁ : Type u_5} {D₂ : Type u_6} [inst : CategoryTheory.Category.{v
_2, u_2} C₁]   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_map`：homMap_map (f : X ⟶ Y) : Φ.
homMap L₁ L₂ (L₁.map f) = L₂.map (Φ.functor.map f)
-/
lemma homMap_id :
    Φ.homMap L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj (Φ.functor.obj X)) := by
  simpa using Φ.homMap_map L₁ L₂ (𝟙 X)

@[reassoc]
/-
**CategoryTheory.LocalizerMorphism.homMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.LocalizerMorphism`。
形式化陈述：homMap_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) : Φ.homMap
 L₁ L₂ (f ≫ g) = Φ.homMap L₁ L₂ f ≫ Φ.homMap L₁ L₂ g
参数：f : L₁.obj X ⟶ L₁.obj Y；g : L₁.obj Y ⟶ L₁.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.homCongr_apply`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y),   (α.
homCongr β) f = Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homMap_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) :
    Φ.homMap L₁ L₂ (f ≫ g) = Φ.homMap L₁ L₂ f ≫ Φ.homMap L₁ L₂ g := by
  simp [homMap]

@[reassoc]
/-
**CategoryTheory.LocalizerMorphism.homMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.LocalizerMorphism`。
形式化陈述：homMap_apply (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L
₁.obj Y) : Φ.homMap L₁ L₂ f = e.hom.app X ≫ G.map f ≫ e.inv.app Y
参数：G : D₁ ⥤ D₂；e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G；f : L₁.obj X ⟶ L₁.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Localization.liftNatIso_hom`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma homMap_apply (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y) :
    Φ.homMap L₁ L₂ f = e.hom.app X ≫ G.map f ≫ e.inv.app Y := by
  let G' := Φ.localizedFunctor L₁ L₂
  let e' := CatCommSq.iso Φ.functor L₁ L₂ G'
  change e'.hom.app X ≫ G'.map f ≫ e'.inv.app Y = _
  let : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  let α : G' ≅ G := Localization.liftNatIso L₁ W₁ (L₁ ⋙ G') (Φ.functor ⋙ L₂) _ _ e'.symm
  have : e = e' ≪≫ Functor.isoWhiskerLeft _ α := by
    ext
    simp [α, this]
  simp [this]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.LocalizerMorphism.id_homMap** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.LocalizerMorphism`。
形式化陈述：id_homMap (f : L₁.obj X ⟶ L₁.obj Y) : (id W₁).homMap L₁ L₁ f = f
参数：f : L₁.obj X ⟶ L₁.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_apply`：homMap_apply (G : D₁ ⥤ D₂
) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y) : Φ.homMap L₁ L₂ f = e
.hom.app X ≫ G.map f ≫ e.inv.app Y
-/
lemma id_homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    (id W₁).homMap L₁ L₁ f = f := by
  simpa using (id W₁).homMap_apply L₁ L₁ (𝟭 D₁) (Iso.refl _) f

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.LocalizerMorphism.homMap_homMap** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.LocalizerMorphism`。
形式化陈述：homMap_homMap (f : L₁.obj X ⟶ L₁.obj Y) : Ψ.homMap L₂ L₃ (Φ.homMap L₁ L₂ f
) = (Φ.comp Ψ).homMap L₁ L₃ f
参数：f : L₁.obj X ⟶ L₁.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_apply`：homMap_apply (G : D₁ ⥤ D₂
) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y) : Φ.homMap L₁ L₂ f = e
.hom.app X ≫ G.map f ≫ e.inv.app Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homMap_homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    Ψ.homMap L₂ L₃ (Φ.homMap L₁ L₂ f) = (Φ.comp Ψ).homMap L₁ L₃ f := by
  let G := Φ.localizedFunctor L₁ L₂
  let G' := Ψ.localizedFunctor L₂ L₃
  let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso _ _ _ _
  let e' : Ψ.functor ⋙ L₃ ≅ L₂ ⋙ G' := CatCommSq.iso _ _ _ _
  rw [Φ.homMap_apply L₁ L₂ G e, Ψ.homMap_apply L₂ L₃ G' e',
    (Φ.comp Ψ).homMap_apply L₁ L₃ (G ⋙ G')
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e' ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _)]
  dsimp
  simp only [Functor.map_comp, assoc, comp_id, id_comp]

end LocalizerMorphism

namespace Localization

variable (W : MorphismProperty C) (L₁ : C ⥤ D₁) [L₁.IsLocalization W]
  (L₂ : C ⥤ D₂) [L₂.IsLocalization W] (L₃ : C ⥤ D₃) [L₃.IsLocalization W]
  {X Y Z : C}

set_option backward.isDefEq.respectTransparency false in
/-- Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`. -/
@[simps -isSimp apply]
/-
**CategoryTheory.Localization.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Localization`。
形式化陈述：homEquiv : (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`.
-/
noncomputable def homEquiv :
    (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y) where
  toFun := (LocalizerMorphism.id W).homMap L₁ L₂
  invFun := (LocalizerMorphism.id W).homMap L₂ L₁
  left_inv f := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap
  right_inv g := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap

@[simp]
/-
**CategoryTheory.Localization.homEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：homEquiv_symm_apply (g : L₂.obj X ⟶ L₂.obj Y) : (homEquiv W L₁ L₂).symm g 
= homEquiv W L₂ L₁ g
参数：g : L₂.obj X ⟶ L₂.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma homEquiv_symm_apply (g : L₂.obj X ⟶ L₂.obj Y) :
    (homEquiv W L₁ L₂).symm g = homEquiv W L₂ L₁ g := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.homEquiv_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Localization`。
形式化陈述：homEquiv_eq (G : D₁ ⥤ D₂) (e : L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y) : ho
mEquiv W L₁ L₂ f = e.inv.app X ≫ G.map f ≫ e.hom.app Y
参数：G : D₁ ⥤ D₂；e : L₁ ⋙ G ≅ L₂；f : L₁.obj X ⟶ L₁.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.homEquiv_apply`：∀ {C : Type u_1} {D₁ : Type 
u_5} {D₂ : Type u_6} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_5, u_5…
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_apply`：homMap_apply (G : D₁ ⥤ D₂
) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y) : Φ.homMap L₁ L₂ f = e
.hom.app X ≫ G.map f ≫ e.inv.app Y
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `CategoryTheory.Iso.symm_inv`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y : C} (α : X ≅ Y), α.symm.inv = α.hom
-/
lemma homEquiv_eq (G : D₁ ⥤ D₂) (e : L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₁ L₂ f = e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  rw [homEquiv_apply, LocalizerMorphism.homMap_apply (LocalizerMorphism.id W) L₁ L₂ G e.symm,
    Iso.symm_hom, Iso.symm_inv]

@[simp]
/-
**CategoryTheory.Localization.homEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Localization`。
形式化陈述：homEquiv_refl (f : L₁.obj X ⟶ L₁.obj Y) : homEquiv W L₁ L₁ f = f
参数：f : L₁.obj X ⟶ L₁.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.id_homMap`：id_homMap (f : L₁.obj X ⟶ L₁
.obj Y) : (id W₁).homMap L₁ L₁ f = f
-/
lemma homEquiv_refl (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₁ L₁ f = f := by
  apply LocalizerMorphism.id_homMap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Localization.homEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Localization`。
形式化陈述：homEquiv_trans (f : L₁.obj X ⟶ L₁.obj Y) : homEquiv W L₂ L₃ (homEquiv W L₁
 L₂ f) = homEquiv W L₁ L₃ f
参数：f : L₁.obj X ⟶ L₁.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_homMap`：homMap_homMap (f : L₁.ob
j X ⟶ L₁.obj Y) : Ψ.homMap L₂ L₃ (Φ.homMap L₁ L₂ f) = (Φ.comp Ψ).homMap L₁ L₃ f
-/
lemma homEquiv_trans (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₂ L₃ (homEquiv W L₁ L₂ f) = homEquiv W L₁ L₃ f := by
  dsimp only [homEquiv_apply]
  apply LocalizerMorphism.homMap_homMap
/-
**CategoryTheory.Localization.homEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Localization`。
形式化陈述：homEquiv_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) : homEqu
iv W L₁ L₂ (f ≫ g) = homEquiv W L₁ L₂ f ≫ homEquiv W L₁ L₂ g
参数：f : L₁.obj X ⟶ L₁.obj Y；g : L₁.obj Y ⟶ L₁.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_comp`：homMap_comp (f : L₁.obj X 
⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) : Φ.homMap L₁ L₂ (f ≫ g) = Φ.homMap L₁ L₂ 
f ≫ Φ.homMap L₁ L₂ g
-/
lemma homEquiv_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) :
    homEquiv W L₁ L₂ (f ≫ g) = homEquiv W L₁ L₂ f ≫ homEquiv W L₁ L₂ g := by
  apply LocalizerMorphism.homMap_comp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Localization.homEquiv_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Localization`。
形式化陈述：homEquiv_map (f : X ⟶ Y) : homEquiv W L₁ L₂ (L₁.map f) = L₂.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_map`：homMap_map (f : X ⟶ Y) : Φ.
homMap L₁ L₂ (L₁.map f) = L₂.map (Φ.functor.map f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_map (f : X ⟶ Y) : homEquiv W L₁ L₂ (L₁.map f) = L₂.map f := by
  simp [homEquiv_apply]

set_option backward.defeqAttrib.useBackward true in
variable (X) in
@[simp]
/-
**CategoryTheory.Localization.homEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Localization`。
形式化陈述：homEquiv_id : homEquiv W L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.homMap_id`：homMap_id : Φ.homMap L₁ L₂ (
𝟙 (L₁.obj X)) = 𝟙 (L₂.obj (Φ.functor.obj X))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_id : homEquiv W L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X) := by
  simp [homEquiv_apply]
/-
**CategoryTheory.Localization.homEquiv_isoOfHom_inv** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization`。
形式化陈述：homEquiv_isoOfHom_inv (f : Y ⟶ X) (hf : W f) : homEquiv W L₁ L₂ (isoOfHom 
L₁ W f hf).inv = (isoOfHom L₂ W f hf).inv
参数：f : Y ⟶ X；hf : W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Localization.isoOfHom_hom`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Localization.homEquiv_map`：homEquiv_map (f : X ⟶ Y) : hom
Equiv W L₁ L₂ (L₁.map f) = L₂.map f
· 使用引理 `CategoryTheory.Localization.homEquiv_comp`：homEquiv_comp (f : L₁.obj X ⟶
 L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) : homEquiv W L₁ L₂ (f ≫ g) = homEquiv W L₁ 
L₂ f ≫ homEquiv W L₁ L₂ g
· 使用引理 `CategoryTheory.Localization.isoOfHom_inv_hom_id`：isoOfHom_inv_hom_id {X 
Y : C} (f : X ⟶ Y) (hf : W f) : (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _
· 使用引理 `CategoryTheory.Localization.homEquiv_id`：homEquiv_id : homEquiv W L₁ L₂ 
(𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X)
-/
lemma homEquiv_isoOfHom_inv (f : Y ⟶ X) (hf : W f) :
    homEquiv W L₁ L₂ (isoOfHom L₁ W f hf).inv = (isoOfHom L₂ W f hf).inv := by
  rw [← cancel_mono (isoOfHom L₂ W f hf).hom, Iso.inv_hom_id, isoOfHom_hom,
    ← homEquiv_map W L₁ L₂ f, ← homEquiv_comp, isoOfHom_inv_hom_id, homEquiv_id]

end Localization

end CategoryTheory

