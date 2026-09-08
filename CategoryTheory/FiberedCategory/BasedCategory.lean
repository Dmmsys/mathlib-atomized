/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# The bicategory of based categories

In this file we define the type `BasedCategory 𝒮`, and give it the structure of a strict
bicategory. Given a category `𝒮`, we define the type `BasedCategory 𝒮` as the type of categories
`𝒳` equipped with a functor `𝒳.p : 𝒳 ⥤ 𝒮`.

We also define a type of functors between based categories `𝒳` and `𝒴`, which we call
`BasedFunctor 𝒳 𝒴` and denote as `𝒳 ⥤ᵇ 𝒴`. These are defined as functors between the underlying
categories `𝒳.obj` and `𝒴.obj` which commute with the projections to `𝒮`.

Natural transformations between based functors `F G : 𝒳 ⥤ᵇ 𝒴 ` are given by the structure
`BasedNatTrans F G`. These are defined as natural transformations `α` between the functors
underlying `F` and `G` such that `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`.
-/

@[expose] public section

universe v₅ u₅ v₄ u₄ v₃ u₃ v₂ u₂ v₁ u₁

namespace CategoryTheory

open CategoryTheory.Functor Category NatTrans IsHomLift

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

set_option linter.checkUnivs false in
/-- A based category over `𝒮` is a category `𝒳` together with a functor `p : 𝒳 ⥤ 𝒮`. -/
/-
**CategoryTheory.BasedCategory** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where /-- The type of object
s in a `BasedCategory` -/ obj : Type u₂ /-- The underlying category of a `BasedC
ategory`. -/ category : Category.{v₂} obj
参数：𝒮 : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A based category over `𝒮` is a category `𝒳` together with a functor `p : 𝒳 ⥤ 𝒮`.
-/
structure BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where
  /-- The type of objects in a `BasedCategory` -/
  obj : Type u₂
  /-- The underlying category of a `BasedCategory`. -/
  category : Category.{v₂} obj := by infer_instance
  /-- The functor to the base. -/
  p : obj ⥤ 𝒮
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : Category 𝒳.obj := 𝒳.category

/-- The based category associated to a functor `p : 𝒳 ⥤ 𝒮`. -/
/-
**CategoryTheory.BasedCategory.ofFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.BasedCategory`。
形式化陈述：{𝒮 : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] →     {𝒳 : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] → CategoryTheory.F
unctor 𝒳 𝒮 → CategoryTheory.BasedCategory 𝒮
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The based category associated to a functor `p : 𝒳 ⥤ 𝒮`.
-/
def BasedCategory.ofFunctor {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) : BasedCategory 𝒮 where
  obj := 𝒳
  p := p

/-- A functor between based categories is a functor between the underlying categories that commutes
with the projections. -/
/-
**CategoryTheory.BasedFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：BasedFunctor (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
 extends 𝒳.obj ⥤ 𝒴.obj where w : toFunctor ⋙ 𝒴.p = 𝒳.p
参数：𝒳 : BasedCategory.{v₂, u₂} 𝒮；𝒴 : BasedCategory.{v₃, u₃} 𝒮。
继承自：𝒳.obj ⥤ 𝒴.obj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between based categories is a functor between the underlying categorie
s that commutes
with the projections.
-/
structure BasedFunctor (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) extends
    𝒳.obj ⥤ 𝒴.obj where
  w : toFunctor ⋙ 𝒴.p = 𝒳.p := by cat_disch

/-- Notation for `BasedFunctor`. -/
scoped infixr:26 " ⥤ᵇ " => BasedFunctor

namespace BasedFunctor

initialize_simps_projections BasedFunctor (+toFunctor, -obj, -map)

/-- The identity based functor. -/
@[simps]
/-
**CategoryTheory.BasedFunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Based
Functor`。
形式化陈述：id (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : 𝒳 ⥤ᵇ 𝒳 where toFunctor
参数：𝒳 : BasedCategory.{v₂, u₂} 𝒮。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity based functor.
-/
def id (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : 𝒳 ⥤ᵇ 𝒳 where
  toFunctor := 𝟭 𝒳.obj

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Notation for the identity functor on a based category. -/
scoped notation "𝟭" => BasedFunctor.id

/-- The composition of two based functors. -/
@[simps]
/-
**CategoryTheory.BasedFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bas
edFunctor`。
形式化陈述：comp {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) : 𝒳 ⥤ᵇ 𝒵 whe
re toFunctor
参数：F : 𝒳 ⥤ᵇ 𝒴；G : 𝒴 ⥤ᵇ 𝒵。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two based functors.
-/
def comp {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) : 𝒳 ⥤ᵇ 𝒵 where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  w := by rw [Functor.assoc, G.w, F.w]

/-- Notation for composition of based functors. -/
scoped infixr:80 " ⋙ " => BasedFunctor.comp

@[simp]
/-
**CategoryTheory.BasedFunctor.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
BasedFunctor`。
形式化陈述：comp_id (F : 𝒳 ⥤ᵇ 𝒴) : F ⋙ 𝟭 𝒴 = F
参数：F : 𝒳 ⥤ᵇ 𝒴。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_id (F : 𝒳 ⥤ᵇ 𝒴) : F ⋙ 𝟭 𝒴 = F :=
  rfl

@[simp]
/-
**CategoryTheory.BasedFunctor.id_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
BasedFunctor`。
形式化陈述：id_comp (F : 𝒳 ⥤ᵇ 𝒴) : 𝟭 𝒳 ⋙ F = F
参数：F : 𝒳 ⥤ᵇ 𝒴。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_comp (F : 𝒳 ⥤ᵇ 𝒴) : 𝟭 𝒳 ⋙ F = F :=
  rfl

@[simp]
/-
**CategoryTheory.BasedFunctor.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.BasedFunctor`。
形式化陈述：comp_assoc {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {𝒜 : BasedCategory.{v₅, u₅} 𝒮} (
F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) (H : 𝒵 ⥤ᵇ 𝒜) : (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H)
参数：F : 𝒳 ⥤ᵇ 𝒴；G : 𝒴 ⥤ᵇ 𝒵；H : 𝒵 ⥤ᵇ 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_assoc {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {𝒜 : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (G : 𝒴 ⥤ᵇ 𝒵) (H : 𝒵 ⥤ᵇ 𝒜) : (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) :=
  rfl

@[simp]
/-
**CategoryTheory.BasedFunctor.w_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ba
sedFunctor`。
形式化陈述：w_obj (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : 𝒴.p.obj (F.obj a) = 𝒳.p.obj a
参数：F : 𝒳 ⥤ᵇ 𝒴；a : 𝒳.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.comp_obj`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.BasedFunctor.w`：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} 𝒮] {𝒳 : CategoryTheory.BasedCategory 𝒮}   {𝒴 : CategoryTheory.Ba
sedCategory 𝒮} (sel…
-/
lemma w_obj (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : 𝒴.p.obj (F.obj a) = 𝒳.p.obj a := by
  rw [← Functor.comp_obj, F.w]
/-
**CategoryTheory.BasedFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.BasedFu
nctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (𝟙 (F.obj a)) :=
  IsHomLift.id (w_obj F a)

section

variable (F : 𝒳 ⥤ᵇ 𝒴) {R S : 𝒮} {a b : 𝒳.obj} (f : R ⟶ S) (φ : a ⟶ b)

set_option backward.defeqAttrib.useBackward true in
/-- For a based functor `F : 𝒳 ⟶ 𝒴`, then whenever an arrow `φ` in `𝒳` lifts some `f` in `𝒮`,
then `F(φ)` also lifts `f`. -/
/-
**CategoryTheory.BasedFunctor.preserves_isHomLift** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.BasedFunctor`。
形式化陈述：preserves_isHomLift [IsHomLift 𝒳.p f φ] : IsHomLift 𝒴.p f (F.map φ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_fac`：of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) 
(φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : f = eqToHom ha.symm ≫ p.m
ap φ ≫ eqToHom hb) : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.BasedFunctor.w_obj`：w_obj (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : 𝒴.p.
obj (F.obj a) = 𝒳.p.obj a
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.BasedFunctor.w`：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} 𝒮] {𝒳 : CategoryTheory.BasedCategory 𝒮}   {𝒴 : CategoryTheory.Ba
sedCategory 𝒮} (sel…
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用引理 `CategoryTheory.IsHomLift.fac`：fac : f = eqToHom (domain_eq p f φ).symm ≫
 p.map φ ≫ eqToHom (codomain_eq p f φ)

--- 原说明 ---
For a based functor `F : 𝒳 ⟶ 𝒴`, then whenever an arrow `φ` in `𝒳` lifts some `f
` in `𝒮`,
then `F(φ)` also lifts `f`.
-/
instance preserves_isHomLift [IsHomLift 𝒳.p f φ] : IsHomLift 𝒴.p f (F.map φ) := by
  apply of_fac 𝒴.p f (F.map φ) (Eq.trans (F.w_obj a) (domain_eq 𝒳.p f φ))
    (Eq.trans (F.w_obj b) (codomain_eq 𝒳.p f φ))
  rw [← Functor.comp_map, congr_hom F.w]
  simpa using (fac 𝒳.p f φ)

set_option backward.defeqAttrib.useBackward true in
/-- For a based functor `F : 𝒳 ⟶ 𝒴`, and an arrow `φ` in `𝒳`, then `φ` lifts an arrow `f` in `𝒮`
if `F(φ)` does. -/
/-
**CategoryTheory.BasedFunctor.isHomLift_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.BasedFunctor`。
形式化陈述：isHomLift_map [IsHomLift 𝒴.p f (F.map φ)] : IsHomLift 𝒳.p f φ
参数：F.map φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.of_fac`：of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) 
(φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S) (h : f = eqToHom ha.symm ≫ p.m
ap φ ≫ eqToHom hb) : …
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.BasedFunctor.w_obj`：w_obj (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : 𝒴.p.
obj (F.obj a) = 𝒳.p.obj a
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.BasedFunctor.w`：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} 𝒮] {𝒳 : CategoryTheory.BasedCategory 𝒮}   {𝒴 : CategoryTheory.Ba
sedCategory 𝒮} (sel…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsHomLift.fac`：fac : f = eqToHom (domain_eq p f φ).symm ≫
 p.map φ ≫ eqToHom (codomain_eq p f φ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.congr_hom`：congr_hom {F G : C ⥤ D} (h : F = G) {X
 Y} (f : X ⟶ Y) : F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_o
bj h Y).symm
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a based functor `F : 𝒳 ⟶ 𝒴`, and an arrow `φ` in `𝒳`, then `φ` lifts an arro
w `f` in `𝒮`
if `F(φ)` does.
-/
lemma isHomLift_map [IsHomLift 𝒴.p f (F.map φ)] : IsHomLift 𝒳.p f φ := by
  apply of_fac 𝒳.p f φ (F.w_obj a ▸ domain_eq 𝒴.p f (F.map φ))
    (F.w_obj b ▸ codomain_eq 𝒴.p f (F.map φ))
  simp [congr_hom F.w.symm, fac 𝒴.p f (F.map φ)]
/-
**CategoryTheory.BasedFunctor.isHomLift_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.BasedFunctor`。
形式化陈述：isHomLift_iff : IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.BasedFunctor.isHomLift_map`：isHomLift_map [IsHomLift 𝒴.p 
f (F.map φ)] : IsHomLift 𝒳.p f φ
-/
lemma isHomLift_iff : IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ :=
  ⟨fun _ ↦ isHomLift_map F f φ, fun _ ↦ preserves_isHomLift F f φ⟩

end

end BasedFunctor


/-- A `BasedNatTrans` between two `BasedFunctor`s is a natural transformation `α` between the
underlying functors, such that for all `a : 𝒳`, `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`. -/
/-
**CategoryTheory.BasedNatTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：BasedNatTrans {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮
} (F G : 𝒳 ⥤ᵇ 𝒴) extends CategoryTheory.NatTrans F.toFunctor G.toFunctor where i
sHomLift' : forall (a : 𝒳.obj), IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (toNatTrans.app a)
参数：F G : 𝒳 ⥤ᵇ 𝒴。
继承自：CategoryTheory.NatTrans F.toFunctor G.toFunctor。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `BasedNatTrans` between two `BasedFunctor`s is a natural transformation `α` be
tween the
underlying functors, such that for all `a : 𝒳`, `α.app a` lifts `𝟙 S` whenever `
𝒳.p.obj a = S`.
-/
structure BasedNatTrans {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F G : 𝒳 ⥤ᵇ 𝒴) extends CategoryTheory.NatTrans F.toFunctor G.toFunctor where
  isHomLift' : ∀ (a : 𝒳.obj), IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (toNatTrans.app a) := by cat_disch

namespace BasedNatTrans

open BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

initialize_simps_projections BasedNatTrans (+toNatTrans, -app)

section

variable {F G : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G)

@[ext]
/-
**CategoryTheory.BasedNatTrans.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Bas
edNatTrans`。
形式化陈述：ext (β : BasedNatTrans F G) (h : α.toNatTrans = β.toNatTrans) : α = β
参数：β : BasedNatTrans F G；h : α.toNatTrans = β.toNatTrans。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext (β : BasedNatTrans F G) (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α; subst h; rfl
/-
**CategoryTheory.BasedNatTrans.app_isHomLift** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.BasedNatTrans`。
形式化陈述：app_isHomLift (a : 𝒳.obj) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.toNatTrans.ap
p a)
参数：a : 𝒳.obj。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.BasedNatTrans.isHomLift'`：∀ {𝒮 : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} 𝒮] {𝒳 : CategoryTheory.BasedCategory 𝒮}   {𝒴 : Categor
yTheory.BasedCategory 𝒮} {F G…
-/
instance app_isHomLift (a : 𝒳.obj) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.toNatTrans.app a) :=
  α.isHomLift' a
/-
**CategoryTheory.BasedNatTrans.isHomLift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.BasedNatTrans`。
形式化陈述：isHomLift {a : 𝒳.obj} {S : 𝒮} (ha : 𝒳.p.obj a = S) : IsHomLift 𝒴.p (𝟙 S) (
α.toNatTrans.app a)
参数：ha : 𝒳.p.obj a = S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isHomLift {a : 𝒳.obj} {S : 𝒮} (ha : 𝒳.p.obj a = S) :
    IsHomLift 𝒴.p (𝟙 S) (α.toNatTrans.app a) := by
  subst ha; infer_instance

end

/-- The identity natural transformation is a `BasedNatTrans`. -/
@[simps]
/-
**CategoryTheory.BasedNatTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Base
dNatTrans`。
形式化陈述：id (F : 𝒳 ⥤ᵇ 𝒴) : BasedNatTrans F F where toNatTrans
参数：F : 𝒳 ⥤ᵇ 𝒴。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity natural transformation is a `BasedNatTrans`.
-/
def id (F : 𝒳 ⥤ᵇ 𝒴) : BasedNatTrans F F where
  toNatTrans := CategoryTheory.NatTrans.id F.toFunctor
  isHomLift' := fun a ↦ of_fac 𝒴.p _ _ (w_obj F a) (w_obj F a) (by simp)

/-- Composition of `BasedNatTrans`, given by composition of the underlying natural
transformations. -/
@[simps]
/-
**CategoryTheory.BasedNatTrans.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ba
sedNatTrans`。
形式化陈述：comp {F G H : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) : Ba
sedNatTrans F H where toNatTrans
参数：α : BasedNatTrans F G；β : BasedNatTrans G H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `BasedNatTrans`, given by composition of the underlying natural
transformations.
-/
def comp {F G H : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) : BasedNatTrans F H where
  toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
  isHomLift' := by
    intro a
    rw [CategoryTheory.NatTrans.vcomp_app]
    infer_instance

@[simps]
/-
**CategoryTheory.BasedNatTrans.homCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.BasedNatTrans`。
形式化陈述：homCategory (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) 
: Category (𝒳 ⥤ᵇ 𝒴) where Hom
参数：𝒳 : BasedCategory.{v₂, u₂} 𝒮；𝒴 : BasedCategory.{v₃, u₃} 𝒮。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance homCategory (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) :
    Category (𝒳 ⥤ᵇ 𝒴) where
  Hom := BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp

@[ext]
/-
**CategoryTheory.BasedNatTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.BasedNatTrans.homCategory`。
形式化陈述：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] {𝒳 : CategoryT
heory.BasedCategory 𝒮}   {𝒴 : CategoryTheory.BasedCategory 𝒮} {F G : CategoryThe
ory.BasedFunctor 𝒳 𝒴} (α β : F ⟶ G),   α.toNatTrans = β.toNatTrans → α = β
参数：α β : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.BasedNatTrans.ext`：ext (β : BasedNatTrans F G) (h : α.toN
atTrans = β.toNatTrans) : α = β
-/
lemma homCategory.ext {F G : 𝒳 ⥤ᵇ 𝒴} (α β : F ⟶ G) (h : α.toNatTrans = β.toNatTrans) : α = β :=
  BasedNatTrans.ext α β h

/-- The forgetful functor from the category of based functors `𝒳 ⥤ᵇ 𝒴` to the category of
functors of underlying categories, `𝒳.obj ⥤ 𝒴.obj`. -/
@[simps]
/-
**CategoryTheory.BasedNatTrans.forgetful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.BasedNatTrans`。
形式化陈述：forgetful (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) : 
(𝒳 ⥤ᵇ 𝒴) ⥤ (𝒳.obj ⥤ 𝒴.obj) where obj
参数：𝒳 : BasedCategory.{v₂, u₂} 𝒮；𝒴 : BasedCategory.{v₃, u₃} 𝒮。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of based functors `𝒳 ⥤ᵇ 𝒴` to the catego
ry of
functors of underlying categories, `𝒳.obj ⥤ 𝒴.obj`.
-/
def forgetful (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) :
    (𝒳 ⥤ᵇ 𝒴) ⥤ (𝒳.obj ⥤ 𝒴.obj) where
  obj := fun F ↦ F.toFunctor
  map := fun α ↦ α.toNatTrans

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.BasedNatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.BasedN
atTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forgetful 𝒳 𝒴).ReflectsIsomorphisms where
  reflects {F G} α _ := by
    constructor
    use {
      toNatTrans := inv ((forgetful 𝒳 𝒴).map α)
      isHomLift' := fun a ↦ by simp [lift_id_inv_isIso] }
    aesop

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.BasedNatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.BasedN
atTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) [IsIso α] : IsIso (X := F.toFunctor) α.toNatTrans := by
  rw [← forgetful_map]; infer_instance

end BasedNatTrans

namespace BasedNatIso

open BasedNatTrans

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- The identity natural transformation is a based natural isomorphism. -/
@[simps]
/-
**CategoryTheory.BasedNatIso.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.BasedN
atIso`。
形式化陈述：id (F : 𝒳 ⥤ᵇ 𝒴) : F ≅ F where hom
参数：F : 𝒳 ⥤ᵇ 𝒴。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity natural transformation is a based natural isomorphism.
-/
def id (F : 𝒳 ⥤ᵇ 𝒴) : F ≅ F where
  hom := 𝟙 F
  inv := 𝟙 F

variable {F G : 𝒳 ⥤ᵇ 𝒴}

/-- The inverse of a based natural transformation whose underlying natural transformation is an
isomorphism. -/
/-
**CategoryTheory.BasedNatIso.mkNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
BasedNatIso`。
形式化陈述：mkNatIso (α : F.toFunctor ≅ G.toFunctor) (isHomLift' : forall a : 𝒳.obj, I
sHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.hom.app a)) : F ≅ G where hom
参数：α : F.toFunctor ≅ G.toFunctor；isHomLift' : forall a : 𝒳.obj, IsHomLift 𝒴.p (𝟙
 (𝒳.p.obj a)) (α.hom.app a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a based natural transformation whose underlying natural transform
ation is an
isomorphism.
-/
def mkNatIso (α : F.toFunctor ≅ G.toFunctor)
    (isHomLift' : ∀ a : 𝒳.obj, IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.hom.app a)) : F ≅ G where
  hom := { toNatTrans := α.hom }
  inv := {
    toNatTrans := α.inv
    isHomLift' := fun a ↦ by
      have : 𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) (α.app a).hom := (Iso.app_hom α a) ▸ isHomLift' a
      rw [← Iso.app_inv]
      apply IsHomLift.lift_id_inv }

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.BasedNatIso.isIso_of_toNatTrans_isIso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.BasedNatIso`。
形式化陈述：isIso_of_toNatTrans_isIso (α : F ⟶ G) [IsIso (X
参数：α : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsIsomorphisms.reflects`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `CategoryTheory.BasedNatTrans.instReflectsIsomorphismsBasedFunctorFunctor
ObjForgetful`：∀ {𝒮 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] {𝒳 : C
ategoryTheory.BasedCategory 𝒮}   {𝒴 : CategoryTheory.BasedCategory 𝒮}, (Ca…
-/
lemma isIso_of_toNatTrans_isIso (α : F ⟶ G) [IsIso (X := F.toFunctor) α.toNatTrans] : IsIso α :=
  have : IsIso ((forgetful 𝒳 𝒴).map α) := by simp_all
  Functor.ReflectsIsomorphisms.reflects (forgetful 𝒳 𝒴) α

end BasedNatIso

namespace BasedCategory

open BasedFunctor BasedNatTrans

section

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Left-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying functors
and natural transformations. -/
@[simps]
/-
**CategoryTheory.BasedCategory.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.BasedCategory`。
形式化陈述：whiskerLeft {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α 
: G ⟶ H) : F ⋙ G ⟶ F ⋙ H where toNatTrans
参数：F : 𝒳 ⥤ᵇ 𝒴；α : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-whiskering in the bicategory `BasedCategory` is given by whiskering the und
erlying functors
and natural transformations.
-/
def whiskerLeft {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  toNatTrans := Functor.whiskerLeft F.toFunctor α.toNatTrans
  isHomLift' := fun a ↦ α.isHomLift (F.w_obj a)

/-- Right-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying
functors and natural transformations. -/
@[simps]
/-
**CategoryTheory.BasedCategory.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.BasedCategory`。
形式化陈述：whiskerRight {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) (H 
: 𝒴 ⥤ᵇ 𝒵) : F ⋙ H ⟶ G ⋙ H where toNatTrans
参数：α : F ⟶ G；H : 𝒴 ⥤ᵇ 𝒵。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-whiskering in the bicategory `BasedCategory` is given by whiskering the un
derlying
functors and natural transformations.
-/
def whiskerRight {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) (H : 𝒴 ⥤ᵇ 𝒵) :
    F ⋙ H ⟶ G ⋙ H where
  toNatTrans := Functor.whiskerRight α.toNatTrans H.toFunctor
  isHomLift' := fun _ ↦ BasedFunctor.preserves_isHomLift _ _ _

end

/-- The category of based categories. -/
@[simps]
/-
**CategoryTheory.BasedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.BasedC
ategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of based categories.
-/
instance : Category (BasedCategory.{v₂, u₂} 𝒮) where
  Hom := BasedFunctor
  id := id
  comp := comp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The bicategory of based categories. -/
/-
**CategoryTheory.BasedCategory.bicategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.BasedCategory`。
形式化陈述：bicategory : Bicategory (BasedCategory.{v₂, u₂} 𝒮) where Hom 𝒳 𝒴
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicategory of based categories.
-/
instance bicategory : Bicategory (BasedCategory.{v₂, u₂} 𝒮) where
  Hom 𝒳 𝒴 := 𝒳 ⥤ᵇ 𝒴
  id 𝒳 := 𝟭 𝒳
  comp F G := F ⋙ G
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft {_ _ _} F {_ _} α := whiskerLeft F α
  whiskerRight {_ _ _} _ _ α H := whiskerRight α H
  associator _ _ _ := BasedNatIso.id _
  leftUnitor {_ _} F := BasedNatIso.id F
  rightUnitor {_ _} F := BasedNatIso.id F

set_option backward.isDefEq.respectTransparency.types false in
/-- The bicategory structure on `BasedCategory.{v₂, u₂} 𝒮` is strict. -/
/-
**CategoryTheory.BasedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.BasedC
ategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicategory structure on `BasedCategory.{v₂, u₂} 𝒮` is strict.
-/
instance : Bicategory.Strict (BasedCategory.{v₂, u₂} 𝒮) where

end BasedCategory

end CategoryTheory

