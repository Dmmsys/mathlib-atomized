/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.CommSq

/-!
# Pseudofunctors from strict bicategory

This file provides an API for pseudofunctors `F` from a strict bicategory `B`. In
particular, this shall apply to pseudofunctors from locally discrete bicategories.

Firstly, we study the compatibilities of the flexible variants `mapId'` and `mapComp'`
of `mapId` and `mapComp` with respect to the composition with identities and the
associativity.

Secondly, given a commutative square `t ≫ r = l ≫ b` in `B`, we construct an
isomorphism `F.map t ≫ F.map r ≅ F.map l ≫ F.map b`
(see `Pseudofunctor.isoMapOfCommSq`).

-/

@[expose] public section

namespace CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

open Bicategory

namespace Pseudofunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᵖ C)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pseudofunctor.mapComp'_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ : B} (f : b₀ ⟶ b₁),   F.mapComp' f
 (CategoryTheory.CategoryStruct.id b₁) f ⋯ =     (CategoryTheory.Bicategory.righ
tUnitor (F.map f)).symm ≪≫       CategoryTheory.Bicategory.whiskerLeftIso (F.map
 f) (F.mapId b₁).symm
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；CategoryTheory.CategoryStruc
t.id b₁；CategoryTheory.Bicategory.rightUnitor (F.map f)；F.map f；F.mapId b₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'.eq_1`：∀ {B : Type u₁} [inst : Cate
goryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   
(F : CategoryTheory.Pseudofuncto…
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_right_hom`：mapComp_id_right_hom 
(f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom = F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv ≫
 F.map f ◁ (F.mapId b).inv
· 使用定理 `CategoryTheory.Bicategory.Strict.comp_id`：∀ {B : Type u} {inst : Categor
yTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b : B} (f :
 a ⟶ b),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Bicategory.Strict.rightUnitor_eqToIso`：∀ {B : Type u} {in
st : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a
 b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.eqToIso.hom`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {X Y : C} (p : X = Y),   (CategoryTheory.eqToIso p).hom = Catego
ryTheory.eqToHom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_comp_assoc`：∀ {B : Type u₁} [inst : Ca
tegoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C] 
  (self : CategoryTheory.PrelaxFun…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mapComp'_comp_id {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' f (𝟙 b₁) f = (ρ_ _).symm ≪≫ whiskerLeftIso _ (F.mapId b₁).symm := by
  ext
  rw [mapComp']
  dsimp
  rw [F.mapComp_id_right_hom f, Strict.rightUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'_comp_id_hom** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ : B} (f : b₀ ⟶ b₁),   (F.mapComp' 
f (CategoryTheory.CategoryStruct.id b₁) f ⋯).hom =     CategoryTheory.CategorySt
ruct.comp (CategoryTheory.Bicategory.rightUnitor (F.map f)).inv       (CategoryT
heory.Bicategory.whiskerLeft (F.map f) (F.mapId b₁).inv)
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；F.mapComp' f (CategoryTheory
.CategoryStruct.id b₁) f ⋯；CategoryTheory.Bicategory.rightUnitor (F.map f)；Categ
oryTheory.Bicategory.whiskerLeft (F.map f) (F.mapId b₁).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_comp_id`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp'_comp_id_hom {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' f (𝟙 b₁) f).hom = (ρ_ _).inv ≫ _ ◁ (F.mapId b₁).inv := by
  simp [mapComp'_comp_id]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'_comp_id_inv** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ : B} (f : b₀ ⟶ b₁),   (F.mapComp' 
f (CategoryTheory.CategoryStruct.id b₁) f ⋯).inv =     CategoryTheory.CategorySt
ruct.comp (CategoryTheory.Bicategory.whiskerLeft (F.map f) (F.mapId b₁).hom)    
   (CategoryTheory.Bicategory.rightUnitor (F.map f)).hom
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；F.mapComp' f (CategoryTheory
.CategoryStruct.id b₁) f ⋯；CategoryTheory.Bicategory.whiskerLeft (F.map f) (F.ma
pId b₁).hom；CategoryTheory.Bicategory.rightUnitor (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_comp_id`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp'_comp_id_inv {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' f (𝟙 b₁) f).inv = _ ◁ (F.mapId b₁).hom ≫ (ρ_ _).hom := by
  simp [mapComp'_comp_id]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pseudofunctor.mapComp'_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ : B} (f : b₀ ⟶ b₁),   F.mapComp' (
CategoryTheory.CategoryStruct.id b₀) f f ⋯ =     (CategoryTheory.Bicategory.left
Unitor (F.map f)).symm ≪≫       CategoryTheory.Bicategory.whiskerRightIso (F.map
Id b₀).symm (F.map f)
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；CategoryTheory.CategoryStruc
t.id b₀；CategoryTheory.Bicategory.leftUnitor (F.map f)；F.mapId b₀；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'.eq_1`：∀ {B : Type u₁} [inst : Cate
goryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   
(F : CategoryTheory.Pseudofuncto…
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_left_hom`：mapComp_id_left_hom (f
 : a ⟶ b) : (F.mapComp (𝟙 a) f).hom = F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv
 ≫ (F.mapId a).inv ▷ F.map f
· 使用定理 `CategoryTheory.Bicategory.Strict.id_comp`：∀ {B : Type u} {inst : Categor
yTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b : B} (f :
 a ⟶ b),   CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Bicategory.Strict.leftUnitor_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b : B} (f : a ⟶ b),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.eqToIso.hom`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {X Y : C} (p : X = Y),   (CategoryTheory.eqToIso p).hom = Catego
ryTheory.eqToHom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_comp_assoc`：∀ {B : Type u₁} [inst : Ca
tegoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C] 
  (self : CategoryTheory.PrelaxFun…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mapComp'_id_comp {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' (𝟙 b₀) f f = (λ_ _).symm ≪≫ whiskerRightIso (F.mapId b₀).symm _ := by
  ext
  rw [mapComp']
  dsimp
  rw [F.mapComp_id_left_hom f, Strict.leftUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'_id_comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ : B} (f : b₀ ⟶ b₁),   (F.mapComp' 
(CategoryTheory.CategoryStruct.id b₀) f f ⋯).hom =     CategoryTheory.CategorySt
ruct.comp (CategoryTheory.Bicategory.leftUnitor (F.map f)).inv       (CategoryTh
eory.Bicategory.whiskerRight (F.mapId b₀).inv (F.map f))
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；F.mapComp' (CategoryTheory.C
ategoryStruct.id b₀) f f ⋯；CategoryTheory.Bicategory.leftUnitor (F.map f)；Catego
ryTheory.Bicategory.whiskerRight (F.mapId b₀).inv (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_id_comp`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp'_id_comp_hom {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' (𝟙 b₀) f f).hom = (λ_ _).inv ≫ (F.mapId b₀).inv ▷ _ := by
  simp [mapComp'_id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'_id_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ : B} (f : b₀ ⟶ b₁),   (F.mapComp' 
(CategoryTheory.CategoryStruct.id b₀) f f ⋯).inv =     CategoryTheory.CategorySt
ruct.comp (CategoryTheory.Bicategory.whiskerRight (F.mapId b₀).hom (F.map f))   
    (CategoryTheory.Bicategory.leftUnitor (F.map f)).hom
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；F.mapComp' (CategoryTheory.C
ategoryStruct.id b₀) f f ⋯；CategoryTheory.Bicategory.whiskerRight (F.mapId b₀).h
om (F.map f)；CategoryTheory.Bicategory.leftUnitor (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_id_comp`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp'_id_comp_inv {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' (𝟙 b₀) f f).inv = (F.mapId b₀).hom ▷ _ ≫ (λ_ _).hom := by
  simp [mapComp'_id_comp]

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃).hom =
    (F.mapComp' f₀₂ f₂₃ f).hom ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom := by
  subst h₀₂ h₁₃ hf
  simp [mapComp_assoc_right_hom, Strict.associator_eqToIso, mapComp']

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).inv ≫ (F.mapComp' f₀₂ f₂₃ f).hom =
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ := by
  rw [← cancel_epi (F.mapComp' f₀₁ f₁₃ f hf).hom, Iso.hom_inv_id_assoc,
    F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_assoc _ _ _ _ _ _ h₀₂ h₁₃ hf]
  simp

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.whiskerLeft_mapComp'_inv_comp_mapComp'** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv (hf : f₀₁ ≫ f₁₃ = f) :
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫ (F.mapComp' f₀₁ f₁₃ f hf).inv =
    (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫
      (F.mapComp' f₀₂ f₂₃ f).inv := by
  simp [← cancel_mono (F.mapComp' f₀₂ f₂₃ f).hom,
    F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom _ _ _ _ _ _ h₀₂ h₁₃ hf]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).hom ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ =
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv := by
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_assoc _ _ _ _ _ f h₀₂ h₁₃ (by cat_disch)]
  simp

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'_inv_whiskerRight_mapComp'** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Pseudofunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫ (F.mapComp' f₀₂ f₂₃ f).inv =
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫
      (F.mapComp' f₀₁ f₁₃ f).inv := by
  rw [whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv _ _ _ _ _ _ f h₀₂ h₁₃,
    Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₁₃_inv (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).inv =
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫ (α_ _ _ _).inv ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫ (F.mapComp' f₀₂ f₂₃ f).inv := by
  simp [← whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv _ _ _ _ _ _ f h₀₂ h₁₃ hf]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₁₃_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).hom =
    (F.mapComp' f₀₂ f₂₃ f).hom ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv := by
  rw [← cancel_epi (F.mapComp' f₀₁ f₁₃ f).inv, Iso.inv_hom_id]
  simp [mapComp'₀₁₃_inv _ _ _ _ _ _ f h₀₂ h₁₃ hf]

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₂₃_hom (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).hom =
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ := by
  simp [← mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_assoc _ _ _ _ _ _ f h₀₂ h₁₃ hf]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₂₃_inv (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).inv =
    (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom ≫
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫ (F.mapComp' f₀₁ f₁₃ f).inv := by
  rw [← cancel_epi (F.mapComp' f₀₂ f₂₃ f).hom, Iso.hom_inv_id]
  simp [mapComp'₀₂₃_hom _ _ _ _ _ _ f h₀₂ h₁₃ hf]

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).inv ≫ (F.mapComp' f₀₁ f₁₃ f).hom =
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom ≫
      F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv := by
  simp [mapComp'₀₂₃_inv _ _ _ _ _ _ _ h₀₂ h₁₃ hf]

end associativity

section CommSq

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : B}

section

variable {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b)

/-- Given a commutative square `CommSq t l r b` in a strict bicategory `B` and
a pseudofunctor from `B`, this is the isomorphism
`F.map t ≫ F.map r ≅ F.map l ≫ F.map b`. -/
/-
**CategoryTheory.Pseudofunctor.isoMapOfCommSq** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：isoMapOfCommSq : F.map t ≫ F.map r ≅ F.map l ≫ F.map b
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…

--- 原说明 ---
Given a commutative square `CommSq t l r b` in a strict bicategory `B` and
a pseudofunctor from `B`, this is the isomorphism
`F.map t ≫ F.map r ≅ F.map l ≫ F.map b`.
-/
def isoMapOfCommSq : F.map t ≫ F.map r ≅ F.map l ≫ F.map b :=
  (F.mapComp t r).symm ≪≫ F.mapComp' _ _ _ (by rw [sq.w])
/-
**CategoryTheory.Pseudofunctor.isoMapOfCommSq_eq** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Pseudofunctor`。
形式化陈述：isoMapOfCommSq_eq (φ : X₁ ⟶ Y₂) (hφ : t ≫ r = φ) : F.isoMapOfCommSq sq = (
F.mapComp' t r φ (by rw [hφ])).symm ≪≫ F.mapComp' l b φ (by rw [← hφ, sq.w])
参数：φ : X₁ ⟶ Y₂；hφ : t ≫ r = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp`：∀ {B : Type u₁} [inst 
: CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory
 C]   (F : CategoryTheory.Pseudofuncto…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoMapOfCommSq_eq (φ : X₁ ⟶ Y₂) (hφ : t ≫ r = φ) :
    F.isoMapOfCommSq sq = (F.mapComp' t r φ (by rw [hφ])).symm ≪≫
      F.mapComp' l b φ (by rw [← hφ, sq.w]) := by
  subst hφ
  simp [isoMapOfCommSq, mapComp'_eq_mapComp]

end

/-- Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both vertical maps of the square are the same and horizontal maps are identities. -/
/-
**CategoryTheory.Pseudofunctor.isoMapOfCommSq_horiz_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：isoMapOfCommSq_horiz_id (f : X₁ ⟶ X₂) : F.isoMapOfCommSq (t
参数：f : X₁ ⟶ X₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Pseudofunctor.isoMapOfCommSq_eq`：isoMapOfCommSq_eq (φ : X
₁ ⟶ Y₂) (hφ : t ≫ r = φ) : F.isoMapOfCommSq sq = (F.mapComp' t r φ (by rw [hφ]))
.symm ≪≫ F.mapComp' l b φ (by rw [← …
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_comp_id`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_id_comp`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…

--- 原说明 ---
Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both vertical maps of the square are the same and horizontal maps are identities
.
-/
lemma isoMapOfCommSq_horiz_id (f : X₁ ⟶ X₂) :
    F.isoMapOfCommSq (t := 𝟙 _) (l := f) (r := f) (b := 𝟙 _) ⟨by simp⟩ =
      whiskerRightIso (F.mapId X₁) (F.map f) ≪≫ λ_ _ ≪≫ (ρ_ _).symm ≪≫
        (whiskerLeftIso (F.map f) (F.mapId X₂)).symm := by
  ext
  rw [isoMapOfCommSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

/-- Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both horizontal maps of the square are the same and vertical maps are identities. -/
/-
**CategoryTheory.Pseudofunctor.isoMapOfCommSq_vert_id** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：isoMapOfCommSq_vert_id (f : X₁ ⟶ X₂) : F.isoMapOfCommSq (t
参数：f : X₁ ⟶ X₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Pseudofunctor.isoMapOfCommSq_eq`：isoMapOfCommSq_eq (φ : X
₁ ⟶ Y₂) (hφ : t ≫ r = φ) : F.isoMapOfCommSq sq = (F.mapComp' t r φ (by rw [hφ]))
.symm ≪≫ F.mapComp' l b φ (by rw [← …
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_comp_id`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_id_comp`：∀ {B : Type u₁} {C : Type
 u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.St
rict B]   [inst_2 : CategoryTheory.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…

--- 原说明 ---
Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both horizontal maps of the square are the same and vertical maps are identities
.
-/
lemma isoMapOfCommSq_vert_id (f : X₁ ⟶ X₂) :
    F.isoMapOfCommSq (t := f) (l := 𝟙 _) (r := 𝟙 _) (b := f) ⟨by simp⟩ =
      whiskerLeftIso (F.map f) (F.mapId X₂) ≪≫ ρ_ _ ≪≫ (λ_ _).symm ≪≫
        (whiskerRightIso (F.mapId X₁) (F.map f)).symm := by
  ext
  rw [isoMapOfCommSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

end CommSq

end Pseudofunctor

namespace LaxFunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᴸ C)

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

@[reassoc]
/-
**CategoryTheory.LaxFunctor.whiskerLeft_mapComp'_comp_mapComp'** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.LaxFunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.LaxFunctor B C) {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)   (f₁₂ : b
₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)   (h₀₂ : C
ategoryTheory.CategoryStruct.comp f₀₁ f₁₂ = f₀₂) (h₁₃ : CategoryTheory.CategoryS
truct.comp f₁₂ f₂₃ = f₁₃)   (hf : CategoryTheory.CategoryStruct.comp f₀₁ f₁₃ = f
),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Bicategory.whiskerLeft (
F.map f₀₁) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃))       (F.mapComp' f₀₁ f₁₃ f hf) =     C
ategoryTheory.CategoryStruct.comp (CategoryTheory.Bicategory.associator (F.map f
₀₁) (F.map f₁₂) (F.map f₂₃)).inv       (CategoryTheory.CategoryStruct.comp      
   (CategoryTheory.Bicategory.whiskerRight (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f
₂₃)) (F.mapComp' f₀₂ f₂₃ f ⋯))
参数：F : CategoryTheory.LaxFunctor B C；f₀₁ : b₀ ⟶ b₁；f₁₂ : b₁ ⟶ b₂；f₂₃ : b₂ ⟶ b₃；f
₀₂ : b₀ ⟶ b₂；f₁₃ : b₁ ⟶ b₃；f : b₀ ⟶ b₃；h₀₂ : CategoryTheory.CategoryStruct.comp 
f₀₁ f₁₂ = f₀₂；h₁₃ : CategoryTheory.CategoryStruct.comp f₁₂ f₂₃ = f₁₃；hf : Catego
ryTheory.CategoryStruct.comp f₀₁ f₁₃ = f；CategoryTheory.Bicategory.whiskerLeft (
F.map f₀₁) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃)；F.mapComp' f₀₁ f₁₃ f hf；CategoryTheory.B
icategory.associator (F.map f₀₁) (F.map f₁₂) (F.map f₂₃)；CategoryTheory.Category
Struct.comp         (CategoryTheory.Bicategory.whiskerRight (F.mapComp' f₀₁ f₁₂ 
f₀₂ h₀₂) (F.map f₂₃)) (F.mapComp' f₀₂ f₂₃ f ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LaxFunctor.map₂_associator`：∀ {B : Type u₁} [inst : Categ
oryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (
self : CategoryTheory.LaxFuncto…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.Strict.assoc`：∀ {B : Type u} {inst : CategoryT
heory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b c d : B}   
(f : a ⟶ b) (g : b ⟶ c) (h :…
· 使用定理 `CategoryTheory.Bicategory.Strict.associator_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b c d : B}   (f : a ⟶ b) (g : b ⟶ c) (h :…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_mapComp'_comp_mapComp' (hf : f₀₁ ≫ f₁₃ = f) :
    F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫ F.mapComp' f₀₁ f₁₃ f hf =
    (α_ _ _ _).inv ≫ F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ ≫
      F.mapComp' f₀₂ f₂₃ f := by
  subst hf h₀₂ h₁₃
  have := F.map₂_associator f₀₁ f₁₂ f₂₃
  simp only [Strict.associator_eqToIso, eqToIso.hom] at this
  simp [LaxFunctor.mapComp', this]

@[reassoc]
/-
**CategoryTheory.LaxFunctor.mapComp'_whiskerRight_comp_mapComp'** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.LaxFunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.LaxFunctor B C) {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)   (f₁₂ : b
₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)   (h₀₂ : C
ategoryTheory.CategoryStruct.comp f₀₁ f₁₂ = f₀₂) (h₁₃ : CategoryTheory.CategoryS
truct.comp f₁₂ f₂₃ = f₁₃)   (hf : CategoryTheory.CategoryStruct.comp f₀₂ f₂₃ = f
),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Bicategory.whiskerRight 
(F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f₂₃))       (F.mapComp' f₀₂ f₂₃ f ⋯) =     C
ategoryTheory.CategoryStruct.comp (CategoryTheory.Bicategory.associator (F.map f
₀₁) (F.map f₁₂) (F.map f₂₃)).hom       (CategoryTheory.CategoryStruct.comp      
   (CategoryTheory.Bicategory.whiskerLeft (F.map f₀₁) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁
₃)) (F.mapComp' f₀₁ f₁₃ f ⋯))
参数：F : CategoryTheory.LaxFunctor B C；f₀₁ : b₀ ⟶ b₁；f₁₂ : b₁ ⟶ b₂；f₂₃ : b₂ ⟶ b₃；f
₀₂ : b₀ ⟶ b₂；f₁₃ : b₁ ⟶ b₃；f : b₀ ⟶ b₃；h₀₂ : CategoryTheory.CategoryStruct.comp 
f₀₁ f₁₂ = f₀₂；h₁₃ : CategoryTheory.CategoryStruct.comp f₁₂ f₂₃ = f₁₃；hf : Catego
ryTheory.CategoryStruct.comp f₀₂ f₂₃ = f；CategoryTheory.Bicategory.whiskerRight 
(F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f₂₃)；F.mapComp' f₀₂ f₂₃ f ⋯；CategoryTheory.B
icategory.associator (F.map f₀₁) (F.map f₁₂) (F.map f₂₃)；CategoryTheory.Category
Struct.comp         (CategoryTheory.Bicategory.whiskerLeft (F.map f₀₁) (F.mapCom
p' f₁₂ f₂₃ f₁₃ h₁₃)) (F.mapComp' f₀₁ f₁₃ f ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.LaxFunctor.whiskerLeft_mapComp'_comp_mapComp'`：∀ {B : Typ
e u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheor
y.Bicategory.Strict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapComp'_whiskerRight_comp_mapComp' (hf : f₀₂ ≫ f₂₃ = f) :
    F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ ≫ F.mapComp' f₀₂ f₂₃ f =
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫
      F.mapComp' f₀₁ f₁₃ f := by
  rw [whiskerLeft_mapComp'_comp_mapComp' _ _ _ _ _ _ f h₀₂ h₁₃,
    Iso.hom_inv_id_assoc]

end associativity

end LaxFunctor

namespace OplaxFunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᵒᵖᴸ C)

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

@[reassoc]
/-
**CategoryTheory.OplaxFunctor.mapComp'_comp_whiskerLeft_mapComp'** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.OplaxFunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.OplaxFunctor B C) {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)   (f₁₂ :
 b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)   (h₀₂ :
 CategoryTheory.CategoryStruct.comp f₀₁ f₁₂ = f₀₂) (h₁₃ : CategoryTheory.Categor
yStruct.comp f₁₂ f₂₃ = f₁₃)   (hf : CategoryTheory.CategoryStruct.comp f₀₁ f₁₃ =
 f),   CategoryTheory.CategoryStruct.comp (F.mapComp' f₀₁ f₁₃ f ⋯)       (Catego
ryTheory.Bicategory.whiskerLeft (F.map f₀₁) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃)) =     
CategoryTheory.CategoryStruct.comp (F.mapComp' f₀₂ f₂₃ f ⋯)       (CategoryTheor
y.CategoryStruct.comp         (CategoryTheory.Bicategory.whiskerRight (F.mapComp
' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f₂₃))         (CategoryTheory.Bicategory.associator (F
.map f₀₁) (F.map f₁₂) (F.map f₂₃)).hom)
参数：F : CategoryTheory.OplaxFunctor B C；f₀₁ : b₀ ⟶ b₁；f₁₂ : b₁ ⟶ b₂；f₂₃ : b₂ ⟶ b₃
；f₀₂ : b₀ ⟶ b₂；f₁₃ : b₁ ⟶ b₃；f : b₀ ⟶ b₃；h₀₂ : CategoryTheory.CategoryStruct.com
p f₀₁ f₁₂ = f₀₂；h₁₃ : CategoryTheory.CategoryStruct.comp f₁₂ f₂₃ = f₁₃；hf : Cate
goryTheory.CategoryStruct.comp f₀₁ f₁₃ = f；F.mapComp' f₀₁ f₁₃ f ⋯；CategoryTheory
.Bicategory.whiskerLeft (F.map f₀₁) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃)；F.mapComp' f₀₂ 
f₂₃ f ⋯；CategoryTheory.CategoryStruct.comp         (CategoryTheory.Bicategory.wh
iskerRight (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f₂₃))         (CategoryTheory.Bic
ategory.associator (F.map f₀₁) (F.map f₁₂) (F.map f₂₃)).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.OplaxFunctor.map₂_associator`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (self : CategoryTheory.OplaxFunc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.PrelaxFunctor.map₂_eqToHom`：map₂_eqToHom {x y : B} (f g :
 x ⟶ y) (hfg : f = g) : F.map₂ (eqToHom hfg) = eqToHom (by rw [← hfg])
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.Strict.assoc`：∀ {B : Type u} {inst : CategoryT
heory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a b c d : B}   
(f : a ⟶ b) (g : b ⟶ c) (h :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.Strict.associator_eqToIso`：∀ {B : Type u} {ins
t : CategoryTheory.Bicategory B} [self : CategoryTheory.Bicategory.Strict B] {a 
b c d : B}   (f : a ⟶ b) (g : b ⟶ c) (h :…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp'_comp_whiskerLeft_mapComp' (hf : f₀₁ ≫ f₁₃ = f) :
    F.mapComp' f₀₁ f₁₃ f ≫ F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ =
    F.mapComp' f₀₂ f₂₃ f ≫
      F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ ≫ (α_ _ _ _).hom := by
  subst h₀₂ h₁₃ hf
  have := F.map₂_associator f₀₁ f₁₂ f₂₃
  simp only [Strict.associator_eqToIso, eqToIso.hom] at this
  simp [OplaxFunctor.mapComp', ← this, PrelaxFunctor.map₂_eqToHom]


@[reassoc]
/-
**CategoryTheory.OplaxFunctor.mapComp'_comp_mapComp'_whiskerRight** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.OplaxFunctor`。
形式化陈述：∀ {B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1
 : CategoryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.Bicategory C] 
(F : CategoryTheory.OplaxFunctor B C) {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)   (f₁₂ :
 b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)   (h₀₂ :
 CategoryTheory.CategoryStruct.comp f₀₁ f₁₂ = f₀₂) (h₁₃ : CategoryTheory.Categor
yStruct.comp f₁₂ f₂₃ = f₁₃)   (hf : CategoryTheory.CategoryStruct.comp f₀₂ f₂₃ =
 f),   CategoryTheory.CategoryStruct.comp (F.mapComp' f₀₂ f₂₃ f ⋯)       (Catego
ryTheory.Bicategory.whiskerRight (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f₂₃)) =    
 CategoryTheory.CategoryStruct.comp (F.mapComp' f₀₁ f₁₃ f ⋯)       (CategoryTheo
ry.CategoryStruct.comp         (CategoryTheory.Bicategory.whiskerLeft (F.map f₀₁
) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃))         (CategoryTheory.Bicategory.associator (F
.map f₀₁) (F.map f₁₂) (F.map f₂₃)).inv)
参数：F : CategoryTheory.OplaxFunctor B C；f₀₁ : b₀ ⟶ b₁；f₁₂ : b₁ ⟶ b₂；f₂₃ : b₂ ⟶ b₃
；f₀₂ : b₀ ⟶ b₂；f₁₃ : b₁ ⟶ b₃；f : b₀ ⟶ b₃；h₀₂ : CategoryTheory.CategoryStruct.com
p f₀₁ f₁₂ = f₀₂；h₁₃ : CategoryTheory.CategoryStruct.comp f₁₂ f₂₃ = f₁₃；hf : Cate
goryTheory.CategoryStruct.comp f₀₂ f₂₃ = f；F.mapComp' f₀₂ f₂₃ f ⋯；CategoryTheory
.Bicategory.whiskerRight (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂) (F.map f₂₃)；F.mapComp' f₀₁
 f₁₃ f ⋯；CategoryTheory.CategoryStruct.comp         (CategoryTheory.Bicategory.w
hiskerLeft (F.map f₀₁) (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃))         (CategoryTheory.Bic
ategory.associator (F.map f₀₁) (F.map f₁₂) (F.map f₂₃)).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.OplaxFunctor.mapComp'_comp_whiskerLeft_mapComp'_assoc`：∀ 
{B : Type u₁} {C : Type u₂} [inst : CategoryTheory.Bicategory B] [inst_1 : Categ
oryTheory.Bicategory.Strict B]   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mapComp'_comp_mapComp'_whiskerRight (hf : f₀₂ ≫ f₂₃ = f) :
    F.mapComp' f₀₂ f₂₃ f ≫ F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ =
    F.mapComp' f₀₁ f₁₃ f ≫ F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫
      (α_ _ _ _).inv := by
  rw [F.mapComp'_comp_whiskerLeft_mapComp'_assoc _ _ _ _ _ f h₀₂ h₁₃ (by cat_disch)]
  simp

end associativity

end OplaxFunctor

end CategoryTheory

