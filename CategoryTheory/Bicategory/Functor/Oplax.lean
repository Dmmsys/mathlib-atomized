/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Oplax functors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.mapComp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.OplaxFunctor B C` : an oplax functor between bicategories `B` and `C`, which we
  denote by `B ⥤ᵒᵖᴸ C`.
* `CategoryTheory.OplaxFunctor.comp F G` : the composition of oplax functors

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- An oplax functor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute with composition,
and does not need to strictly preserve the identity. Instead, there are specified 2-morphisms
`F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

`F.map₂` strictly commutes with compositions and preserves the identity. It also preserves the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
/-
**CategoryTheory.OplaxFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：OplaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicatego
ry.{w₂, v₂} C] extends PrelaxFunctor B C where /-- The 2-morphism underlying the
 oplax unity constraint. -/ mapId (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a) /-- The 2-morp
hism underlying the oplax functoriality constraint. -/ mapComp {a b c : B} (f : 
a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g /-- Naturality of the oplax fun
ctoriality constraint, on the left. -/ mapComp_naturality_left : forall {a b c :
 B} {f f' : a ⟶ b} (η : f 
参数：B : Type u₁；C : Type u₂；a : B。
继承自：PrelaxFunctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oplax functor `F` between bicategories `B` and `C` consists of a function bet
ween objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphi
sms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute wi
th composition,
and does not need to strictly preserve the identity. Instead, there are specifie
d 2-morphisms
`F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

`F.map₂` strictly commutes with compositions and preserves the identity. It also
 preserves the
associator, the left unitor, and the right unitor modulo some adjustments of dom
ains and codomains
of 2-morphisms.
-/
structure OplaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  /-- The 2-morphism underlying the oplax unity constraint. -/
  mapId (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a)
  /-- The 2-morphism underlying the oplax functoriality constraint. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g
  /-- Naturality of the oplax functoriality constraint, on the left. -/
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g := by
    cat_disch
  /-- Naturality of the oplax functoriality constraint, on the right. -/
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η := by
    cat_disch
  /-- Oplax associativity. -/
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
      mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
    cat_disch
  /-- Oplax left unity. -/
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (λ_ (map f)).hom := by
    cat_disch
  /-- Oplax right unity. -/
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom := by
    cat_disch

/-- Notation for an oplax functor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᵒᵖᴸ " => OplaxFunctor -- type as \func\op\^L

initialize_simps_projections OplaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace OplaxFunctor

attribute [to_app (attr := reassoc (attr := simp))]
  mapComp_naturality_left mapComp_naturality_right map₂_associator
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [simp, to_app (attr := reassoc)] map₂_leftUnitor map₂_rightUnitor

section

/-- The underlying prelax functor. -/
add_decl_doc OplaxFunctor.toPrelaxFunctor

variable (F : B ⥤ᵒᵖᴸ C)

@[to_app (attr := reassoc)]
/-
**CategoryTheory.OplaxFunctor.mapComp_assoc_right** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.OplaxFunctor`。
形式化陈述：mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.
mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h = F.map₂ (α_ f g h).inv ≫ F.mapComp 
(f ≫ g) h ≫ F.mapComp f g ▷ F.map h ≫ (α_ (F.map f) (F.map g) (F.map h)).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.OplaxFunctor.map₂_associator`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (self : CategoryTheory.OplaxFunc…
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_comp_assoc`：∀ {B : Type u₁} [inst : Ca
tegoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C] 
  (self : CategoryTheory.PrelaxFun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h = F.map₂ (α_ f g h).inv ≫
    F.mapComp (f ≫ g) h ≫ F.mapComp f g ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom := by
  rw [← F.map₂_associator, ← F.map₂_comp_assoc]
  simp

@[to_app (attr := reassoc)]
/-
**CategoryTheory.OplaxFunctor.mapComp_assoc_left** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.OplaxFunctor`。
形式化陈述：mapComp_assoc_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.m
apComp (f ≫ g) h ≫ F.mapComp f g ▷ F.map h = F.map₂ (α_ f g h).hom ≫ F.mapComp f
 (g ≫ h) ≫ F.map f ◁ F.mapComp g h ≫ (α_ (F.map f) (F.map g) (F.map h)).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.OplaxFunctor.map₂_associator_assoc`：∀ {B : Type u₁} [inst
 : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategor
y C]   (self : CategoryTheory.OplaxFunc…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp_assoc_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp (f ≫ g) h ≫ F.mapComp f g ▷ F.map h =
    F.map₂ (α_ f g h).hom ≫ F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h
    ≫ (α_ (F.map f) (F.map g) (F.map h)).inv := by
  simp

@[reassoc]
/-
**CategoryTheory.OplaxFunctor.mapComp_id_left** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.OplaxFunctor`。
形式化陈述：mapComp_id_left {a b : B} (f : a ⟶ b) : F.mapComp (𝟙 a) f ≫ F.mapId a ▷ F.
map f = F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.OplaxFunctor.map₂_leftUnitor`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (self : CategoryTheory.OplaxFunc…
-/
theorem mapComp_id_left {a b : B} (f : a ⟶ b) :
    F.mapComp (𝟙 a) f ≫ F.mapId a ▷ F.map f = F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_leftUnitor]

@[reassoc]
/-
**CategoryTheory.OplaxFunctor.mapComp_id_right** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.OplaxFunctor`。
形式化陈述：mapComp_id_right {a b : B} (f : a ⟶ b) : F.mapComp f (𝟙 b) ≫ F.map f ◁ F.m
apId b = F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.OplaxFunctor.map₂_rightUnitor`：∀ {B : Type u₁} [inst : Ca
tegoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C] 
  (self : CategoryTheory.OplaxFunc…
-/
theorem mapComp_id_right {a b : B} (f : a ⟶ b) :
    F.mapComp f (𝟙 b) ≫ F.map f ◁ F.mapId b = F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_rightUnitor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity oplax functor. -/
@[simps]
/-
**CategoryTheory.OplaxFunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Oplax
Functor`。
形式化陈述：id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵒᵖᴸ B where toPrelaxFunctor
参数：B : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity oplax functor.
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵒᵖᴸ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)
/-
**CategoryTheory.OplaxFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.OplaxFu
nctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (B ⥤ᵒᵖᴸ B) :=
  ⟨id B⟩

/-- More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
/-
**CategoryTheory.OplaxFunctor.mapId'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
plaxFunctor`。
形式化陈述：mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b
参数：f : b ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.)
-/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.map f ⟶ 𝟙 (F.obj b) :=
  F.map₂ (eqToHom (by rw [hf])) ≫ F.mapId _
/-
**CategoryTheory.OplaxFunctor.mapId'_eq_mapId** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.OplaxFunctor`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.OplaxFunctor B C) (b : B),
 F.mapId' (CategoryTheory.CategoryStruct.id b) ⋯ = F.mapId b
参数：F : CategoryTheory.OplaxFunctor B C；b : B；CategoryTheory.CategoryStruct.id b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/-- More flexible variant of `mapComp`. (See `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
/-
**CategoryTheory.OplaxFunctor.mapComp'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.OplaxFunctor`。
形式化陈述：mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂) (h : f 
≫ g = fg
参数：f : b₀ ⟶ b₁；g : b₁ ⟶ b₂；fg : b₀ ⟶ b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More flexible variant of `mapComp`. (See `Bicategory.Functor.Strict`
for applications to strict bicategories.)
-/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.map fg ⟶ F.map f ≫ F.map g :=
  F.map₂ (eqToHom (by rw [h])) ≫ F.mapComp f g
/-
**CategoryTheory.OplaxFunctor.mapComp'_eq_mapComp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.OplaxFunctor`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.OplaxFunctor B C) {b₀ b₁ b
₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂),   F.mapComp' f g (CategoryTheory.CategoryStr
uct.comp f g) ⋯ = F.mapComp f g
参数：F : CategoryTheory.OplaxFunctor B C；f : b₀ ⟶ b₁；g : b₁ ⟶ b₂；CategoryTheory.Ca
tegoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of oplax functors. -/
--@[simps]
/-
**CategoryTheory.OplaxFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Opl
axFunctor`。
形式化陈述：comp (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D) : B ⥤ᵒᵖᴸ D where toPrelaxFunctor
参数：F : B ⥤ᵒᵖᴸ C；G : C ⥤ᵒᵖᴸ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comp (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D) : B ⥤ᵒᵖᴸ D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [← G.map₂_comp_assoc, mapComp_naturality_left, G.map₂_comp_assoc, mapComp_naturality_left,
      assoc]
  mapComp_naturality_right := fun η => by
    dsimp
    intros
    rw [← G.map₂_comp_assoc, mapComp_naturality_right, G.map₂_comp_assoc,
      mapComp_naturality_right, assoc]
  map₂_associator := fun f g h => by
    dsimp
    simp only [map₂_associator, ← PrelaxFunctor.map₂_comp_assoc, ← mapComp_naturality_right_assoc,
      whiskerLeft_comp, assoc]
    simp only [map₂_associator, PrelaxFunctor.map₂_comp, mapComp_naturality_left_assoc,
      comp_whiskerRight, assoc]
  map₂_leftUnitor := fun f => by
    dsimp
    simp only [map₂_leftUnitor, PrelaxFunctor.map₂_comp, mapComp_naturality_left_assoc,
      comp_whiskerRight, assoc]
  map₂_rightUnitor := fun f => by
    dsimp
    simp only [map₂_rightUnitor, PrelaxFunctor.map₂_comp, mapComp_naturality_right_assoc,
      whiskerLeft_comp, assoc]

/-- A structure on an oplax functor that promotes an oplax functor to a pseudofunctor.

See `Pseudofunctor.mkOfOplax`. -/
/-
**CategoryTheory.OplaxFunctor.PseudoCore** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry.OplaxFunctor`。
形式化陈述：PseudoCore (F : B ⥤ᵒᵖᴸ C) where /-- The isomorphism giving rise to the opl
ax unity constraint -/ mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a) /-- The isom
orphism giving rise to the oplax functoriality constraint -/ mapCompIso {a b c :
 B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g /-- `mapIdIso` g
ives rise to the oplax unity constraint -/ mapIdIso_hom : forall {a : B}, (mapId
Iso a).hom = F.mapId a
参数：F : B ⥤ᵒᵖᴸ C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure on an oplax functor that promotes an oplax functor to a pseudofuncto
r.

See `Pseudofunctor.mkOfOplax`.
-/
structure PseudoCore (F : B ⥤ᵒᵖᴸ C) where
  /-- The isomorphism giving rise to the oplax unity constraint -/
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  /-- The isomorphism giving rise to the oplax functoriality constraint -/
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  /-- `mapIdIso` gives rise to the oplax unity constraint -/
  mapIdIso_hom : ∀ {a : B}, (mapIdIso a).hom = F.mapId a := by cat_disch
  /-- `mapCompIso` gives rise to the oplax functoriality constraint -/
  mapCompIso_hom :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g := by cat_disch

attribute [simp] PseudoCore.mapIdIso_hom PseudoCore.mapCompIso_hom

end

end OplaxFunctor

end

end CategoryTheory

