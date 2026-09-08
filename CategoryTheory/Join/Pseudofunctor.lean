/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctoriality of categorical joins

In this file, we promote the join construction to two pseudofunctors
`Join.pseudofunctorLeft` and `Join.pseudofunctorRight`, expressing its pseudofunctoriality in
each variable.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Join

open Bicategory CategoryTheory.Functor

-- The proof gets too slow if we put it in a single `pseudofunctor` constructor,
-- so we break down the component proofs for the pseudofunctors over several lemmas.

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]


variable (A) in
/-- The structural isomorphism for composition of `pseudofunctorRight`. -/
/-
**CategoryTheory.Join.mapCompRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：mapCompRight (F : B ⥤ C) (G : C ⥤ D) : mapPair (𝟭 A) (F ⋙ G) ≅ mapPair (𝟭 
A) F ⋙ mapPair (𝟭 A) G
参数：F : B ⥤ C；G : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structural isomorphism for composition of `pseudofunctorRight`.
-/
def mapCompRight (F : B ⥤ C) (G : C ⥤ D) :
    mapPair (𝟭 A) (F ⋙ G) ≅ mapPair (𝟭 A) F ⋙ mapPair (𝟭 A) G :=
  mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

variable (D) in
/-- The structural isomorphism for composition of `pseudofunctorLeft`. -/
/-
**CategoryTheory.Join.mapCompLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join
`。
形式化陈述：mapCompLeft (F : A ⥤ B) (G : B ⥤ C) : mapPair (F ⋙ G) (𝟭 D) ≅ mapPair F (𝟭
 D) ⋙ mapPair G (𝟭 D)
参数：F : A ⥤ B；G : B ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structural isomorphism for composition of `pseudofunctorLeft`.
-/
def mapCompLeft (F : A ⥤ B) (G : B ⥤ C) :
    mapPair (F ⋙ G) (𝟭 D) ≅ mapPair F (𝟭 D) ⋙ mapPair G (𝟭 D) :=
  mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

#adaptation_note
/--
`mapIsoWhiskerRight`'s `simps` theorems were formulated in simp normal form under
`respectTransparency.types true`. We use `respectTransparency.types false` here because these
lemmas fail to match without this annotation.
Suggested way forward: Decide what the correct signatures of the `mapIsoWhiskerRight` lemmas
are, then update this proof accordingly.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (A) in
@[reassoc]
/-
**CategoryTheory.Join.mapWhiskerLeft_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Join`。
形式化陈述：mapWhiskerLeft_whiskerLeft (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H) : mapWhis
kerLeft _ (whiskerLeft F η) = (mapCompRight A F G).hom ≫ whiskerLeft (mapPair (𝟭
 A) F) (mapWhiskerLeft _ η) ≫ (mapCompRight A F H).inv
参数：F : B ⥤ C；η : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_hom_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_left`：mapPairComp_inv_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_inv_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_right`：mapPairComp_inv_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mapWhiskerLeft_whiskerLeft (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H) :
    mapWhiskerLeft _ (whiskerLeft F η) =
    (mapCompRight A F G).hom ≫ whiskerLeft (mapPair (𝟭 A) F) (mapWhiskerLeft _ η) ≫
      (mapCompRight A F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

#adaptation_note
/--
`mapIsoWhiskerLeft`'s `simps` theorems were formulated in simp normal form under
`respectTransparency.types true`. We use `respectTransparency.types false` here because these
lemmas fail to match without this annotation.
Suggested way forward: Decide what the correct signatures of the `mapIsoWhiskerLeft` lemmas
are, then update this proof accordingly.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (D) in
@[reassoc]
/-
**CategoryTheory.Join.mapWhiskerRight_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：mapWhiskerRight_whiskerLeft (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H) : mapWhi
skerRight (whiskerLeft F η) (𝟭 D) = (mapCompLeft D F G).hom ≫ whiskerLeft (mapPa
ir F (𝟭 D)) (mapWhiskerRight η _) ≫ (mapCompLeft D F H).inv
参数：F : A ⥤ B；η : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_hom_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_left`：mapPairComp_inv_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_inv_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_right`：mapPairComp_inv_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerRight_whiskerLeft (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H) :
    mapWhiskerRight (whiskerLeft F η) (𝟭 D) =
    (mapCompLeft D F G).hom ≫ whiskerLeft (mapPair F (𝟭 D)) (mapWhiskerRight η _) ≫
      (mapCompLeft D F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (A) in
@[reassoc]
/-
**CategoryTheory.Join.mapWhiskerLeft_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Join`。
形式化陈述：mapWhiskerLeft_whiskerRight {F G : B ⥤ C} (η : F ⟶ G) (H : C ⥤ D) : mapWhi
skerLeft _ (whiskerRight η H) = (mapCompRight A F H).hom ≫ whiskerRight (mapWhis
kerLeft _ η) (mapPair (𝟭 A) H) ≫ (mapCompRight A G H).inv
参数：η : F ⟶ G；H : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_hom_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_left`：mapPairComp_inv_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_inv_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_right`：mapPairComp_inv_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mapWhiskerLeft_whiskerRight {F G : B ⥤ C} (η : F ⟶ G) (H : C ⥤ D) :
    mapWhiskerLeft _ (whiskerRight η H) =
    (mapCompRight A F H).hom ≫ whiskerRight (mapWhiskerLeft _ η) (mapPair (𝟭 A) H) ≫
      (mapCompRight A G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (D) in
@[reassoc]
/-
**CategoryTheory.Join.mapWhiskerRight_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Join`。
形式化陈述：mapWhiskerRight_whiskerRight {F G : A ⥤ B} (η : F ⟶ G) (H : B ⥤ C) : mapWh
iskerRight (whiskerRight η H) _ = (mapCompLeft D F H).hom ≫ whiskerRight (mapWhi
skerRight η _) (mapPair H (𝟭 D)) ≫ (mapCompLeft D G H).inv
参数：η : F ⟶ G；H : B ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_hom_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_left`：mapPairComp_inv_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_inv_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_right`：mapPairComp_inv_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerRight_whiskerRight {F G : A ⥤ B} (η : F ⟶ G) (H : B ⥤ C) :
    mapWhiskerRight (whiskerRight η H) _ =
    (mapCompLeft D F H).hom ≫ whiskerRight (mapWhiskerRight η _) (mapPair H (𝟭 D)) ≫
      (mapCompLeft D G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

variable {E : Type*} [Category* E]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
@[reassoc]
/-
**CategoryTheory.Join.mapWhiskerLeft_associator_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Join`。
形式化陈述：mapWhiskerLeft_associator_hom (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) : mapWhi
skerLeft _ (F.associator G H).hom = (mapCompRight A (F ⋙ G) H).hom ≫ whiskerRigh
t (mapCompRight A F G).hom (mapPair (𝟭 A) H) ≫ ((mapPair (𝟭 A) F).associator (ma
pPair (𝟭 A) G) (mapPair (𝟭 A) H)).hom ≫ whiskerLeft (mapPair (𝟭 A) F) (mapCompRi
ght A G H).inv ≫ (mapCompRight A F (G ⋙ H)).inv
参数：F : B ⥤ C；G : C ⥤ D；H : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_hom_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_left`：mapPairComp_inv_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_inv_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_right`：mapPairComp_inv_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerLeft_associator_hom (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    mapWhiskerLeft _ (F.associator G H).hom =
      (mapCompRight A (F ⋙ G) H).hom ≫ whiskerRight (mapCompRight A F G).hom (mapPair (𝟭 A) H) ≫
      ((mapPair (𝟭 A) F).associator (mapPair (𝟭 A) G) (mapPair (𝟭 A) H)).hom ≫
      whiskerLeft (mapPair (𝟭 A) F) (mapCompRight A G H).inv ≫ (mapCompRight A F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (E) in
/-
**CategoryTheory.Join.mapWhiskerRight_associator_hom** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Join`。
形式化陈述：mapWhiskerRight_associator_hom (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : mapWh
iskerRight (F.associator G H).hom _ = (mapCompLeft E (F ⋙ G) H).hom ≫ whiskerRig
ht (mapCompLeft E F G).hom (mapPair H (𝟭 E)) ≫ ((mapPair F (𝟭 E)).associator (ma
pPair G (𝟭 E)) (mapPair H (𝟭 E))).hom ≫ whiskerLeft (mapPair F (𝟭 E)) (mapCompLe
ft E G H).inv ≫ (mapCompLeft E F (G ⋙ H)).inv
参数：F : A ⥤ B；G : B ⥤ C；H : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_hom_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_left`：mapPairComp_inv_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_inv_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
· 使用引理 `CategoryTheory.Join.mapPairComp_inv_app_right`：mapPairComp_inv_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerRight_associator_hom (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    mapWhiskerRight (F.associator G H).hom _ =
    (mapCompLeft E (F ⋙ G) H).hom ≫ whiskerRight (mapCompLeft E F G).hom (mapPair H (𝟭 E)) ≫
      ((mapPair F (𝟭 E)).associator (mapPair G (𝟭 E)) (mapPair H (𝟭 E))).hom ≫
      whiskerLeft (mapPair F (𝟭 E)) (mapCompLeft E G H).inv ≫ (mapCompLeft E F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
/-
**CategoryTheory.Join.mapWhiskerLeft_leftUnitor_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Join`。
形式化陈述：mapWhiskerLeft_leftUnitor_hom (F : B ⥤ C) : mapWhiskerLeft _ F.leftUnitor.
hom = (mapCompRight A (𝟭 _) F).hom ≫ whiskerRight mapPairId.hom (mapPair _ F) ≫ 
(mapPair _ F).leftUnitor.hom
参数：F : B ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_hom_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Join.mapPairId_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (x : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerLeft_leftUnitor_hom (F : B ⥤ C) :
    mapWhiskerLeft _ F.leftUnitor.hom =
    (mapCompRight A (𝟭 _) F).hom ≫ whiskerRight mapPairId.hom (mapPair _ F) ≫
      (mapPair _ F).leftUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-
**CategoryTheory.Join.mapWhiskerRight_leftUnitor_hom** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Join`。
形式化陈述：mapWhiskerRight_leftUnitor_hom (F : A ⥤ B) : mapWhiskerRight F.leftUnitor.
hom (𝟭 C) = (mapCompLeft C (𝟭 A) F).hom ≫ whiskerRight mapPairId.hom (mapPair F 
(𝟭 C)) ≫ (mapPair F (𝟭 C)).leftUnitor.hom
参数：F : A ⥤ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_hom_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Join.mapPairId_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (x : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerRight_leftUnitor_hom (F : A ⥤ B) :
    mapWhiskerRight F.leftUnitor.hom (𝟭 C) =
    (mapCompLeft C (𝟭 A) F).hom ≫ whiskerRight mapPairId.hom (mapPair F (𝟭 C)) ≫
      (mapPair F (𝟭 C)).leftUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
/-
**CategoryTheory.Join.mapWhiskerLeft_rightUnitor_hom** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Join`。
形式化陈述：mapWhiskerLeft_rightUnitor_hom (F : B ⥤ C) : mapWhiskerLeft _ F.rightUnito
r.hom = (mapCompRight A F (𝟭 C)).hom ≫ whiskerLeft (mapPair _ F) mapPairId.hom ≫
 (mapPair (𝟭 A) _).rightUnitor.hom
参数：F : B ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerRight_hom_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapPairId_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (x : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerLeft_rightUnitor_hom (F : B ⥤ C) :
    mapWhiskerLeft _ F.rightUnitor.hom =
    (mapCompRight A F (𝟭 C)).hom ≫ whiskerLeft (mapPair _ F) mapPairId.hom ≫
      (mapPair (𝟭 A) _).rightUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-
**CategoryTheory.Join.mapWhiskerRight_rightUnitor_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Join`。
形式化陈述：mapWhiskerRight_rightUnitor_hom (F : A ⥤ B) : mapWhiskerRight F.rightUnito
r.hom _ = (mapCompLeft C F (𝟭 B)).hom ≫ whiskerLeft (mapPair F _) mapPairId.hom 
≫ (mapPair _ (𝟭 C)).rightUnitor.hom
参数：F : A ⥤ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
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
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Join.mapIsoWhiskerLeft_hom_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_left`：mapPairComp_hom_app_left (
c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)
))
· 使用定理 `CategoryTheory.Join.mapPairId_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (x : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Join.mapPairComp_hom_app_right`：mapPairComp_hom_app_right
 (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.ob
j d)))
-/
lemma mapWhiskerRight_rightUnitor_hom (F : A ⥤ B) :
    mapWhiskerRight F.rightUnitor.hom _ =
    (mapCompLeft C F (𝟭 B)).hom ≫ whiskerLeft (mapPair F _) mapPairId.hom ≫
      (mapPair _ (𝟭 C)).rightUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

end

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The pseudofunctor sending `D` to `C ⋆ D`. -/
@[simps!]
/-
**CategoryTheory.Join.pseudofunctorRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Join`。
形式化陈述：pseudofunctorRight (C : Type u₁) [Category.{v₁} C] : Pseudofunctor Cat.{v₂
, u₂} Cat.{max v₁ v₂, max u₁ u₂} where obj D
参数：C : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudofunctor sending `D` to `C ⋆ D`.
-/
def pseudofunctorRight (C : Type u₁) [Category.{v₁} C] :
    Pseudofunctor Cat.{v₂, u₂} Cat.{max v₁ v₂, max u₁ u₂} where
  obj D := Cat.of (C ⋆ D)
  map F := (mapPair (𝟭 C) F.toFunctor).toCatHom
  map₂ f := (mapWhiskerLeft (𝟭 C) f.toNatTrans).toCatHom₂
  mapId D := Cat.Hom.isoMk mapPairId
  mapComp F G := Cat.Hom.isoMk <| mapCompRight C F.toFunctor G.toFunctor
  map₂_whisker_left := by intros; exact congr($(mapWhiskerLeft_whiskerLeft C _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerLeft_whiskerRight C _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerLeft_associator_hom C _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerLeft_leftUnitor_hom C _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerLeft_rightUnitor_hom C _).toCatHom₂)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The pseudofunctor sending `C` to `C ⋆ D`. -/
@[simps!]
/-
**CategoryTheory.Join.pseudofunctorLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：pseudofunctorLeft (D : Type u₂) [Category.{v₂} D] : Pseudofunctor Cat.{v₁,
 u₁} Cat.{max v₁ v₂, max u₁ u₂} where obj C
参数：D : Type u₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudofunctor sending `C` to `C ⋆ D`.
-/
def pseudofunctorLeft (D : Type u₂) [Category.{v₂} D] :
    Pseudofunctor Cat.{v₁, u₁} Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (C ⋆ D)
  map F := (mapPair F.toFunctor (𝟭 D)).toCatHom
  map₂ := (mapWhiskerRight ·.toNatTrans _ |>.toCatHom₂)
  mapId D := Cat.Hom.isoMk <| mapPairId
  mapComp _ _ := Cat.Hom.isoMk <| mapCompLeft D _ _
  map₂_whisker_left := by intros; exact congr($(mapWhiskerRight_whiskerLeft D _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerRight_whiskerRight D _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerRight_associator_hom D _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerRight_leftUnitor_hom D _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerRight_rightUnitor_hom D _).toCatHom₂)

end CategoryTheory.Join

