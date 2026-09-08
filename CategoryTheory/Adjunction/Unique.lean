/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang, Dagur Asgeirsson, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
/-!

# Uniqueness of adjoints

This file shows that adjoints are unique up to natural isomorphism.

## Main results

* `Adjunction.leftAdjointUniq` : If `F` and `F'` are both left adjoint to `G`, then they are
  naturally isomorphic.

* `Adjunction.rightAdjointUniq` : If `G` and `G'` are both right adjoint to `F`, then they are
  naturally isomorphic.

-/

@[expose] public section

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
/-
**CategoryTheory.Adjunction.leftAdjointUniq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) 
: F ≅ F'
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic
.
-/
def leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  ((conjugateIsoEquiv adj1 adj2).symm (Iso.refl G)).symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
 (adj2 : F' ⊣ G) (x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).hom.ap
p x) = adj2.unit.app x
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.conjugateEquiv_symm_apply_app`：∀ {C : Type u₁} {D : Type 
u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  simp [leftAdjointUniq]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.unit_leftAdjointUniq_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：unit_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 :
 F' ⊣ G) : adj1.unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).hom G = adj2.uni
t
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`：homEquiv_lef
tAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (
x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    adj1.unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).hom G = adj2.unit := by
  ext x
  rw [NatTrans.comp_app, ← homEquiv_leftAdjointUniq_hom_app adj1 adj2]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：unit_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (ad
j2 : F' ⊣ G) (x : C) : adj1.unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).hom.
app x) = adj2.unit.app x
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom`：unit_leftAdjointUniq
_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : adj1.unit ≫ whi
skerRight (leftAdjointUniq adj1 adj2).ho…
-/
theorem unit_leftAdjointUniq_hom_app
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    adj1.unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  rw [← unit_leftAdjointUniq_hom adj1 adj2]; rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.leftAdjointUniq_hom_counit** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：leftAdjointUniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2
 : F' ⊣ G) : whiskerLeft G (leftAdjointUniq adj1 adj2).hom ≫ adj2.counit = adj1.
counit
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.conjugateEquiv_symm_apply_app`：∀ {C : Type u₁} {D : Type 
u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftAdjointUniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq adj1 adj2).hom ≫ adj2.counit = adj1.counit := by
  ext x
  simp only [Functor.comp_obj, Functor.id_obj, leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, NatTrans.comp_app, whiskerLeft_app,
    conjugateEquiv_symm_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp,
    Category.assoc]
  rw [← adj1.counit_naturality, ← Category.assoc, ← F.map_comp]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Adjunction`。
形式化陈述：leftAdjointUniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (
adj2 : F' ⊣ G) (x : D) : (leftAdjointUniq adj1 adj2).hom.app (G.obj x) ≫ adj2.co
unit.app x = adj1.counit.app x
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G；x : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.leftAdjointUniq_hom_counit`：leftAdjointUniq_ho
m_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : whiskerLeft
 G (leftAdjointUniq adj1 adj2).hom ≫ adj2.…
-/
theorem leftAdjointUniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : D) :
    (leftAdjointUniq adj1 adj2).hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x := by
  rw [← leftAdjointUniq_hom_counit adj1 adj2]
  rfl
/-
**CategoryTheory.Adjunction.leftAdjointUniq_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：leftAdjointUniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : 
F' ⊣ G) (x : C) : (leftAdjointUniq adj1 adj2).inv.app x = (leftAdjointUniq adj2 
adj1).hom.app x
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G；x : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftAdjointUniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).inv.app x = (leftAdjointUniq adj2 adj1).hom.app x :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.leftAdjointUniq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：leftAdjointUniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 
: F' ⊣ G) (adj3 : F'' ⊣ G) : (leftAdjointUniq adj1 adj2).hom ≫ (leftAdjointUniq 
adj2 adj3).hom = (leftAdjointUniq adj1 adj3).hom
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G；adj3 : F'' ⊣ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conjugateIsoEquiv_symm_apply_inv`：∀ {C : Type u₁} {D : Ty
pe u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.conjugateEquiv_symm_comp`：conjugateEquiv_symm_comp (α : R
₁ ⟶ R₂) (β : R₂ ⟶ R₃) : (conjugateEquiv adj₂ adj₃).symm β ≫ (conjugateEquiv adj₁
 adj₂).symm α = (conjugateEqu…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftAdjointUniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) :
    (leftAdjointUniq adj1 adj2).hom ≫ (leftAdjointUniq adj2 adj3).hom =
      (leftAdjointUniq adj1 adj3).hom := by
  simp [leftAdjointUniq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.leftAdjointUniq_trans_app** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：leftAdjointUniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (a
dj2 : F' ⊣ G) (adj3 : F'' ⊣ G) (x : C) : (leftAdjointUniq adj1 adj2).hom.app x ≫
 (leftAdjointUniq adj2 adj3).hom.app x = (leftAdjointUniq adj1 adj3).hom.app x
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G；adj3 : F'' ⊣ G；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.leftAdjointUniq_trans`：leftAdjointUniq_trans {
F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (adj3 : F'' ⊣ G) : 
(leftAdjointUniq adj1 adj2).hom ≫ (le…
-/
theorem leftAdjointUniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).hom.app x ≫ (leftAdjointUniq adj2 adj3).hom.app x =
      (leftAdjointUniq adj1 adj3).hom.app x := by
  rw [← leftAdjointUniq_trans adj1 adj2 adj3]
  rfl

@[simp]
/-
**CategoryTheory.Adjunction.leftAdjointUniq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：leftAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) : (leftAdjoint
Uniq adj1 adj1).hom = 𝟙 _
参数：adj1 : F ⊣ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.conjugateIsoEquiv_symm_apply_inv`：∀ {C : Type u₁} {D : Ty
pe u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.conjugateEquiv_symm_id`：conjugateEquiv_symm_id : (conjuga
teEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (leftAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  simp [leftAdjointUniq]

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
/-
**CategoryTheory.Adjunction.rightAdjointUniq** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
 : G ≅ G'
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphi
c.
-/
def rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
  conjugateIsoEquiv adj1 adj2 (Iso.refl _)
/-
**CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_symm_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : 
F ⊣ G) (adj2 : F ⊣ G') (x : D) : (adj2.homEquiv _ _).symm ((rightAdjointUniq adj
1 adj2).hom.app x) = adj1.counit.app x
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'；x : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.conjugateIsoEquiv_apply_hom`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.conjugateEquiv_apply_app`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_symm_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F ⊣ G') (x : D) :
    (adj2.homEquiv _ _).symm ((rightAdjointUniq adj1 adj2).hom.app x) = adj1.counit.app x := by
  simp [rightAdjointUniq]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：unit_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (a
dj2 : F ⊣ G') (x : C) : adj1.unit.app x ≫ (rightAdjointUniq adj1 adj2).hom.app (
F.obj x) = adj2.unit.app x
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.conjugateEquiv_apply_app`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : C) : adj1.unit.app x ≫ (rightAdjointUniq adj1 adj2).hom.app (F.obj x) =
      adj2.unit.app x := by
  simp only [Functor.id_obj, Functor.comp_obj, rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    Iso.refl_hom, conjugateEquiv_apply_app, NatTrans.id_app, Functor.map_id, Category.id_comp]
  rw [← adj2.unit_naturality_assoc, ← G'.map_comp]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.unit_rightAdjointUniq_hom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：unit_rightAdjointUniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 
: F ⊣ G') : adj1.unit ≫ whiskerLeft F (rightAdjointUniq adj1 adj2).hom = adj2.un
it
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`：unit_rightAdjoi
ntUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : C)
 : adj1.unit.app x ≫ (rightAdjointUniq adj1 a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_rightAdjointUniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    adj1.unit ≫ whiskerLeft F (rightAdjointUniq adj1 adj2).hom = adj2.unit := by
  ext x
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：rightAdjointUniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) 
(adj2 : F ⊣ G') (x : D) : F.map ((rightAdjointUniq adj1 adj2).hom.app x) ≫ adj2.
counit.app x = adj1.counit.app x
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'；x : D。
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
· 使用定理 `CategoryTheory.conjugateIsoEquiv_apply_hom`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.conjugateEquiv_apply_app`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightAdjointUniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) :
    F.map ((rightAdjointUniq adj1 adj2).hom.app x) ≫ adj2.counit.app x = adj1.counit.app x := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.rightAdjointUniq_hom_counit** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：rightAdjointUniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj
2 : F ⊣ G') : whiskerRight (rightAdjointUniq adj1 adj2).hom F ≫ adj2.counit = ad
j1.counit
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`：rightAdjointU
niq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x 
: D) : F.map ((rightAdjointUniq adj1 adj2).hom.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightAdjointUniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    whiskerRight (rightAdjointUniq adj1 adj2).hom F ≫ adj2.counit = adj1.counit := by
  ext
  simp
/-
**CategoryTheory.Adjunction.rightAdjointUniq_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：rightAdjointUniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 :
 F ⊣ G') (x : D) : (rightAdjointUniq adj1 adj2).inv.app x = (rightAdjointUniq ad
j2 adj1).hom.app x
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'；x : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightAdjointUniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (x : D) : (rightAdjointUniq adj1 adj2).inv.app x = (rightAdjointUniq adj2 adj1).hom.app x :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.rightAdjointUniq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：rightAdjointUniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2
 : F ⊣ G') (adj3 : F ⊣ G'') : (rightAdjointUniq adj1 adj2).hom ≫ (rightAdjointUn
iq adj2 adj3).hom = (rightAdjointUniq adj1 adj3).hom
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'；adj3 : F ⊣ G''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conjugateIsoEquiv_apply_hom`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.conjugateEquiv_comp`：conjugateEquiv_comp (α : L₂ ⟶ L₁) (β
 : L₃ ⟶ L₂) : conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β = conjugat
eEquiv adj₁ adj₃ (β ≫ α)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightAdjointUniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') :
    (rightAdjointUniq adj1 adj2).hom ≫ (rightAdjointUniq adj2 adj3).hom =
      (rightAdjointUniq adj1 adj3).hom := by
  simp [rightAdjointUniq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.rightAdjointUniq_trans_app** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：rightAdjointUniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (
adj2 : F ⊣ G') (adj3 : F ⊣ G'') (x : D) : (rightAdjointUniq adj1 adj2).hom.app x
 ≫ (rightAdjointUniq adj2 adj3).hom.app x = (rightAdjointUniq adj1 adj3).hom.app
 x
参数：adj1 : F ⊣ G；adj2 : F ⊣ G'；adj3 : F ⊣ G''；x : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.rightAdjointUniq_trans`：rightAdjointUniq_trans
 {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (adj3 : F ⊣ G'') 
: (rightAdjointUniq adj1 adj2).hom ≫ (…
-/
theorem rightAdjointUniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')
    (adj3 : F ⊣ G'') (x : D) :
    (rightAdjointUniq adj1 adj2).hom.app x ≫ (rightAdjointUniq adj2 adj3).hom.app x =
      (rightAdjointUniq adj1 adj3).hom.app x := by
  rw [← rightAdjointUniq_trans adj1 adj2 adj3]
  rfl


@[simp]
/-
**CategoryTheory.Adjunction.rightAdjointUniq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：rightAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) : (rightAdjoi
ntUniq adj1 adj1).hom = 𝟙 _
参数：adj1 : F ⊣ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conjugateIsoEquiv_apply_hom`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.conjugateEquiv_id`：conjugateEquiv_id : conjugateEquiv adj
₁ adj₁ (𝟙 _) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightAdjointUniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
    (rightAdjointUniq adj1 adj1).hom = 𝟙 _ := by
  delta rightAdjointUniq
  simp

end Adjunction

end CategoryTheory

