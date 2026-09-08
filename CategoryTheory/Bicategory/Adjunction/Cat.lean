/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj

/-!
# Adjunctions in `Cat`

We show that adjunctions in the bicategory `Cat` correspond to
adjunctions between functors in the usual categorical sense.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory

section

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')

namespace Adjunction

attribute [local simp] bicategoricalComp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction in the bicategorical sense attached to an adjunction between functors. -/
@[simps]
/-
**CategoryTheory.Adjunction.toCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adju
nction`。
形式化陈述：toCat : Bicategory.Adjunction F.toCatHom G.toCatHom where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction in the bicategorical sense attached to an adjunction between func
tors.
-/
def toCat : Bicategory.Adjunction F.toCatHom G.toCatHom where
  unit := .ofNatTrans adj.unit
  counit := .ofNatTrans adj.counit

set_option backward.defeqAttrib.useBackward true in
/-- The adjunction of functors corresponding to an adjunction in the bicategory `Cat`. -/
@[simps]
/-
**CategoryTheory.Adjunction.ofCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adju
nction`。
形式化陈述：ofCat {C D : Cat} {F : C ⟶ D} {G : D ⟶ C} (adj : Bicategory.Adjunction F G
) : F.toFunctor ⊣ G.toFunctor where unit
参数：adj : Bicategory.Adjunction F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction of functors corresponding to an adjunction in the bicategory `Cat
`.
-/
def ofCat {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    F.toFunctor ⊣ G.toFunctor where
  unit := adj.unit.toNatTrans
  counit := adj.counit.toNatTrans
  left_triangle_components X := by
    simpa using congr($(adj.left_triangle).toNatTrans.app X)
  right_triangle_components X := by
    simpa using congr($(adj.right_triangle).toNatTrans.app X)

@[simp]
/-
**CategoryTheory.Adjunction.toCat_ofCat** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：toCat_ofCat {C D : Cat} {F : C ⟶ D} {G : D ⟶ C} (adj : Bicategory.Adjuncti
on F G) : (Adjunction.ofCat adj).toCat = adj
参数：adj : Bicategory.Adjunction F G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCat_ofCat
    {C D : Cat} {F : C ⟶ D} {G : D ⟶ C} (adj : Bicategory.Adjunction F G) :
    (Adjunction.ofCat adj).toCat = adj := rfl

@[simp]
/-
**CategoryTheory.Adjunction.ofCat_toCat** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：ofCat_toCat : Adjunction.ofCat adj.toCat = adj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCat_toCat :
    Adjunction.ofCat adj.toCat = adj := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Adjunction.toCat_comp_toCat** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：toCat_comp_toCat : adj.toCat.comp adj'.toCat = (adj.comp adj').toCat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.Adjunction.ext`：∀ {B : Type u₁} {inst : Catego
ryTheory.Bicategory B} {a b : B} {f : a ⟶ b} {g : b ⟶ a}   {x y : CategoryTheory
.Bicategory.Adjunction f g}, x…
· 使用定理 `CategoryTheory.Cat.Hom₂.ext`：∀ {C D : CategoryTheory.Cat} {F G : C ⟶ D} 
{η₁ η₂ : F ⟶ G}, η₁.toNatTrans = η₂.toNatTrans → η₁ = η₂
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
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
-/
lemma toCat_comp_toCat : adj.toCat.comp adj'.toCat = (adj.comp adj').toCat := by
  cat_disch

end Adjunction

end

namespace Bicategory

@[simp]
/-
**CategoryTheory.Bicategory.Adjunction.ofCat_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory.Adjunction`。
形式化陈述：∀ (C : CategoryTheory.Cat),   CategoryTheory.Adjunction.ofCat (CategoryThe
ory.Bicategory.Adjunction.id C) = CategoryTheory.Adjunction.id
参数：C : CategoryTheory.Cat；CategoryTheory.Bicategory.Adjunction.id C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Adjunction.ofCat_id (C : Cat.{v, u}) :
    Adjunction.ofCat (Adjunction.id C) = CategoryTheory.Adjunction.id :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Bicategory.Adjunction.ofCat_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory.Adjunction`。
形式化陈述：∀ {C D E : CategoryTheory.Cat} {F : C ⟶ D} {G : D ⟶ C} (adj : CategoryTheo
ry.Bicategory.Adjunction F G) {F' : D ⟶ E}   {G' : E ⟶ D} (adj' : CategoryTheory
.Bicategory.Adjunction F' G'),   CategoryTheory.Adjunction.ofCat (adj.comp adj')
 =     (CategoryTheory.Adjunction.ofCat adj).comp (CategoryTheory.Adjunction.ofC
at adj')
参数：adj : CategoryTheory.Bicategory.Adjunction F G；adj' : CategoryTheory.Bicatego
ry.Adjunction F' G'；adj.comp adj'；CategoryTheory.Adjunction.ofCat adj；CategoryTh
eory.Adjunction.ofCat adj'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.ext`：ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F
 ⊣ G} (h : adj.unit = adj'.unit) : adj = adj'
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
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Adjunction.ofCat_comp {C D E : Cat.{v, u}}
    {F : C ⟶ D} {G : D ⟶ C} (adj : F ⊣ G)
    {F' : D ⟶ E} {G' : E ⟶ D} (adj' : F' ⊣ G') :
    Adjunction.ofCat (adj.comp adj') = (Adjunction.ofCat adj).comp (Adjunction.ofCat adj') := by
  ext
  simp [bicategoricalComp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Bicategory.toNatTrans_mateEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：toNatTrans_mateEquiv {C D E F : Cat} {G : C ⟶ E} {H : D ⟶ F} {L₁ : C ⟶ D} 
{R₁ : D ⟶ C} {L₂ : E ⟶ F} {R₂ : F ⟶ E} (adj₁ : Bicategory.Adjunction L₁ R₁) (adj
₂ : Bicategory.Adjunction L₂ R₂) (f : G ≫ L₂ ⟶ L₁ ≫ H) : (Bicategory.mateEquiv a
dj₁ adj₂ f).toNatTrans = CategoryTheory.mateEquiv (Adjunction.ofCat adj₁) (Adjun
ction.ofCat adj₂) f.toNatTrans
参数：adj₁ : Bicategory.Adjunction L₁ R₁；adj₂ : Bicategory.Adjunction L₂ R₂；f : G ≫
 L₂ ⟶ L₁ ≫ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerLeft`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η 
: h ⟶ h'),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor_inv`：whiskerLeft_right
Unitor_inv (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).inv = (ρ_ (f ≫ g)).inv ≫ (α_ f g
 (𝟙 c)).hom
· 使用定理 `CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {B : Typ
e u} [inst : CategoryTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c
) (h : c ⟶ d) (i : d ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Functor.whiskerRight_twice`：whiskerRight_twice {H K : B ⥤
 C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) : whiskerRight (whiskerRight α F) G = (F
unctor.associator _ _ _).hom ≫ …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNatTrans_mateEquiv {C D E F : Cat}
    {G : C ⟶ E} {H : D ⟶ F} {L₁ : C ⟶ D} {R₁ : D ⟶ C} {L₂ : E ⟶ F} {R₂ : F ⟶ E}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂)
    (f : G ≫ L₂ ⟶ L₁ ≫ H) :
    (Bicategory.mateEquiv adj₁ adj₂ f).toNatTrans =
      CategoryTheory.mateEquiv (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans := by
  ext X
  simp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Bicategory.toNatTrans_conjugateEquiv** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：toNatTrans_conjugateEquiv {C D : Cat} {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C} (adj
₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂) (f : L₂ ⟶ 
L₁) : (Bicategory.conjugateEquiv adj₁ adj₂ f).toNatTrans = CategoryTheory.conjug
ateEquiv (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans
参数：adj₁ : Bicategory.Adjunction L₁ R₁；adj₂ : Bicategory.Adjunction L₂ R₂；f : L₂ 
⟶ L₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Bicategory.toNatTrans_mateEquiv`：toNatTrans_mateEquiv {C 
D E F : Cat} {G : C ⟶ E} {H : D ⟶ F} {L₁ : C ⟶ D} {R₁ : D ⟶ C} {L₂ : E ⟶ F} {R₂ 
: F ⟶ E} (adj₁ : Bicategory.Adjuncti…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNatTrans_conjugateEquiv {C D : Cat}
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (adj₁ : Bicategory.Adjunction L₁ R₁) (adj₂ : Bicategory.Adjunction L₂ R₂) (f : L₂ ⟶ L₁) :
    (Bicategory.conjugateEquiv adj₁ adj₂ f).toNatTrans =
      CategoryTheory.conjugateEquiv
        (Adjunction.ofCat adj₁) (Adjunction.ofCat adj₂) f.toNatTrans := by
  dsimp [Bicategory.conjugateEquiv]
  rw [toNatTrans_mateEquiv]
  ext X
  simp [CategoryTheory.conjugateEquiv]

namespace Adj

variable {C₁ C₂ : Adj Cat.{v, u}} (α : C₁ ⟶ C₂)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Adj.left_triangle_components** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Bicategory.Adj`。
形式化陈述：left_triangle_components (X : C₁.obj) : α.l.toFunctor.map (α.adj.unit.toNa
tTrans.app X) ≫ α.adj.counit.toNatTrans.app (α.l.toFunctor.obj X) = 𝟙 (α.l.toFun
ctor.obj X)
参数：X : C₁.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma left_triangle_components (X : C₁.obj) :
    α.l.toFunctor.map (α.adj.unit.toNatTrans.app X) ≫
      α.adj.counit.toNatTrans.app (α.l.toFunctor.obj X) =
    𝟙 (α.l.toFunctor.obj X) :=
  (Adjunction.ofCat α.adj).left_triangle_components _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Adj.right_triangle_components** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Bicategory.Adj`。
形式化陈述：right_triangle_components (X : C₂.obj) : α.adj.unit.toNatTrans.app (α.r.to
Functor.obj X) ≫ α.r.toFunctor.map (α.adj.counit.toNatTrans.app X) = 𝟙 (α.r.toFu
nctor.obj X)
参数：X : C₂.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma right_triangle_components (X : C₂.obj) :
    α.adj.unit.toNatTrans.app (α.r.toFunctor.obj X) ≫
       α.r.toFunctor.map (α.adj.counit.toNatTrans.app X) =
    𝟙 (α.r.toFunctor.obj X) :=
  (Adjunction.ofCat α.adj).right_triangle_components _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Adj.unit_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Bicategory.Adj`。
形式化陈述：unit_naturality {X Y : C₁.obj} (f : X ⟶ Y) : α.adj.unit.toNatTrans.app X ≫
 α.r.toFunctor.map (α.l.toFunctor.map f) = f ≫ α.adj.unit.toNatTrans.app Y
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma unit_naturality {X Y : C₁.obj} (f : X ⟶ Y) :
    α.adj.unit.toNatTrans.app X ≫ α.r.toFunctor.map (α.l.toFunctor.map f) =
    f ≫ α.adj.unit.toNatTrans.app Y :=
  (Adjunction.ofCat α.adj).unit_naturality f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.Adj.counit_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Bicategory.Adj`。
形式化陈述：counit_naturality {X Y : C₂.obj} (f : X ⟶ Y) : α.l.toFunctor.map (α.r.toFu
nctor.map f) ≫ α.adj.counit.toNatTrans.app Y = α.adj.counit.toNatTrans.app X ≫ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma counit_naturality {X Y : C₂.obj} (f : X ⟶ Y) :
    α.l.toFunctor.map (α.r.toFunctor.map f) ≫ α.adj.counit.toNatTrans.app Y =
      α.adj.counit.toNatTrans.app X ≫ f :=
  (Adjunction.ofCat α.adj).counit_naturality f

end Adj

end Bicategory

end CategoryTheory

