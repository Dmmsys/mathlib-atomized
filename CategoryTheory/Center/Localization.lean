/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Localization of the center of a category

Given a localization functor `L : C ⥤ D` with respect to `W : MorphismProperty C`,
we define a localization map `CatCenter C → CatCenter D` for the centers
of these categories. In case `L` is an additive functor between preadditive
categories, we promote this to a ring morphism `CatCenter C →+* CatCenter D`.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (r s : CatCenter C) (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace CatCenter

/-- Given `r : CatCenter C` and `L : C ⥤ D` a localization functor with respect
to `W : MorphismProperty D`, this is the induced element in `CatCenter D`
obtained by localization. -/
/-
**CategoryTheory.CatCenter.localization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.CatCenter`。
形式化陈述：localization : CatCenter D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `r : CatCenter C` and `L : C ⥤ D` a localization functor with respect
to `W : MorphismProperty D`, this is the induced element in `CatCenter D`
obtained by localization.
-/
noncomputable def localization : CatCenter D :=
  Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (Functor.whiskerRight r L)

@[simp]
/-
**CategoryTheory.CatCenter.localization_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：localization_app (X : C) : (r.localization L W).app (L.obj X) = L.map (r.a
pp X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localization_app (X : C) :
    (r.localization L W).app (L.obj X) = L.map (r.app X) := by
  dsimp [localization]
  simp only [Localization.liftNatTrans_app, Functor.id_obj, Functor.whiskerRight_app,
    NatTrans.naturality, Functor.comp_map, Functor.id_map, Iso.hom_inv_id_app_assoc]

include W
/-
**CategoryTheory.CatCenter.ext_of_localization** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.CatCenter`。
形式化陈述：ext_of_localization (r s : CatCenter D) (h : forall (X : C), r.app (L.obj 
X) = s.app (L.obj X)) : r = s
参数：r s : CatCenter D；h : forall (X : C), r.app (L.obj X) = s.app (L.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.natTrans_ext`：natTrans_ext (L : C ⥤ D) (W) [
L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂} (h : forall X : C, τ.app (L
.obj X) = τ'.app (L.obj X)) : …
-/
lemma ext_of_localization (r s : CatCenter D)
    (h : ∀ (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s :=
  Localization.natTrans_ext L W h
/-
**CategoryTheory.CatCenter.localization_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：localization_one : (1 : CatCenter C).localization L W = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.ext_of_localization`：ext_of_localization (r s :
 CatCenter D) (h : forall (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CatCenter.localization_app`：localization_app (X : C) : (r
.localization L W).app (L.obj X) = L.map (r.app X)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localization_one :
    (1 : CatCenter C).localization L W = 1 :=
  ext_of_localization L W _ _ (fun X => by simp)
/-
**CategoryTheory.CatCenter.localization_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：localization_mul : (r * s).localization L W = r.localization L W * s.local
ization L W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.ext_of_localization`：ext_of_localization (r s :
 CatCenter D) (h : forall (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CatCenter.localization_app`：localization_app (X : C) : (r
.localization L W).app (L.obj X) = L.map (r.app X)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localization_mul :
    (r * s).localization L W = r.localization L W * s.localization L W :=
  ext_of_localization L W _ _ (fun X => by simp)

section Preadditive

variable [Preadditive C] [Preadditive D] [L.Additive]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CatCenter.localization_zero** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.CatCenter`。
形式化陈述：localization_zero : (0 : CatCenter C).localization L W = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.ext_of_localization`：ext_of_localization (r s :
 CatCenter D) (h : forall (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CatCenter.localization_app`：localization_app (X : C) : (r
.localization L W).app (L.obj X) = L.map (r.app X)
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localization_zero :
    (0 : CatCenter C).localization L W = 0 :=
  ext_of_localization L W _ _ (fun X => by simp)
/-
**CategoryTheory.CatCenter.localization_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：localization_add : (r + s).localization L W = r.localization L W + s.local
ization L W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.ext_of_localization`：ext_of_localization (r s :
 CatCenter D) (h : forall (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CatCenter.localization_app`：localization_app (X : C) : (r
.localization L W).app (L.obj X) = L.map (r.app X)
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma localization_add :
    (r + s).localization L W = r.localization L W + s.localization L W :=
  ext_of_localization L W _ _ (by simp)

/-- The morphism of rings `CatCenter C →+* CatCenter D` when `L : C ⥤ D`
is an additive localization functor between preadditive categories. -/
/-
**CategoryTheory.CatCenter.localizationRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.CatCenter`。
形式化陈述：localizationRingHom : CatCenter C ->+* CatCenter D where toFun r
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.localization_one`：localization_one : (1 : CatCe
nter C).localization L W = 1
· 使用引理 `CategoryTheory.CatCenter.localization_mul`：localization_mul : (r * s).lo
calization L W = r.localization L W * s.localization L W
· 使用引理 `CategoryTheory.CatCenter.localization_zero`：localization_zero : (0 : Cat
Center C).localization L W = 0
· 使用引理 `CategoryTheory.CatCenter.localization_add`：localization_add : (r + s).lo
calization L W = r.localization L W + s.localization L W

--- 原说明 ---
The morphism of rings `CatCenter C →+* CatCenter D` when `L : C ⥤ D`
is an additive localization functor between preadditive categories.
-/
noncomputable def localizationRingHom : CatCenter C →+* CatCenter D where
  toFun r := r.localization L W
  map_zero' := localization_zero L W
  map_one' := localization_one L W
  map_add' _ _ := localization_add _ _ _ _
  map_mul' _ _ := localization_mul _ _ _ _

end Preadditive

end CatCenter

end CategoryTheory

