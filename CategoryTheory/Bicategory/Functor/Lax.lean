/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Lax functors

A lax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : 𝟙 (F.obj a) ⟶ F.map (𝟙 a)`,
* a family of 2-morphisms `F.mapComp f g : F.map f ≫ F.map g ⟶ F.map (f ≫ g)`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.LaxFunctor B C` : a lax functor between bicategories `B` and `C`, which we
  denote by `B ⥤ᴸ C`.
* `CategoryTheory.LaxFunctor.comp F G` : the composition of lax functors
* `CategoryTheory.LaxFunctor.PseudoCore` : a structure on a lax functor that promotes a
  lax functor to a pseudofunctor

## Future work

Some constructions in the bicategory library have only been done in terms of oplax functors,
since lax functors had not yet been added (e.g `FunctorBicategory.lean`). A possible project would
be to mirror these constructions for lax functors.

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

/-- A lax functor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute with composition,
and does not need to strictly preserve the identity. Instead, there are specified 2-morphisms
`𝟙 (F.obj a) ⟶ F.map (𝟙 a)` and `F.map f ≫ F.map g ⟶ F.map (f ≫ g)`.

`F.map₂` strictly commutes with composition and preserves the identity. It also preserves the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
/-
**CategoryTheory.LaxFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：LaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory
.{w₂, v₂} C] extends PrelaxFunctor B C where /-- The 2-morphism underlying the l
ax unity constraint. -/ mapId (a : B) : 𝟙 (obj a) ⟶ map (𝟙 a) /-- The 2-morphism
 underlying the lax functoriality constraint. -/ mapComp {a b c : B} (f : a ⟶ b)
 (g : b ⟶ c) : map f ≫ map g ⟶ map (f ≫ g) /-- Naturality of the lax functoriali
ty constraint, on the left. -/ mapComp_naturality_left : forall {a b c : B} {f f
' : a ⟶ b} (η : f ⟶ f') (g
参数：B : Type u₁；C : Type u₂；a : B。
继承自：PrelaxFunctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lax functor `F` between bicategories `B` and `C` consists of a function betwee
n objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphi
sms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute wi
th composition,
and does not need to strictly preserve the identity. Instead, there are specifie
d 2-morphisms
`𝟙 (F.obj a) ⟶ F.map (𝟙 a)` and `F.map f ≫ F.map g ⟶ F.map (f ≫ g)`.

`F.map₂` strictly commutes with composition and preserves the identity. It also 
preserves the
associator, the left unitor, and the right unitor modulo some adjustments of dom
ains and codomains
of 2-morphisms.
-/
structure LaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends PrelaxFunctor B C where
  /-- The 2-morphism underlying the lax unity constraint. -/
  mapId (a : B) : 𝟙 (obj a) ⟶ map (𝟙 a)
  /-- The 2-morphism underlying the lax functoriality constraint. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map f ≫ map g ⟶ map (f ≫ g)
  /-- Naturality of the lax functoriality constraint, on the left. -/
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g := by cat_disch
  /-- Naturality of the lax functoriality constraint, on the right. -/
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
     mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g' := by cat_disch
  /-- Lax associativity. -/
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom =
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h) := by cat_disch
  /-- Lax left unity. -/
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).inv = (λ_ (map f)).inv ≫ mapId a ▷ map f ≫ mapComp (𝟙 a) f := by cat_disch
  /-- Lax right unity. -/
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ map f ◁ mapId b ≫ mapComp f (𝟙 b) := by cat_disch

/-- Notation for a lax functor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᴸ " => LaxFunctor -- type as \func\^L

initialize_simps_projections LaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace LaxFunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

attribute [to_app (attr := reassoc (attr := simp))]
  mapComp_naturality_left mapComp_naturality_right map₂_associator
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [simp, to_app (attr := reassoc)] map₂_leftUnitor map₂_rightUnitor

/-- The underlying prelax functor. -/
add_decl_doc LaxFunctor.toPrelaxFunctor

variable (F : B ⥤ᴸ C)

@[to_app (attr := reassoc)]
/-
**CategoryTheory.LaxFunctor.mapComp_assoc_left** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.LaxFunctor`。
形式化陈述：mapComp_assoc_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.m
apComp f g ▷ F.map h ≫ F.mapComp (f ≫ g) h = (α_ (F.map f) (F.map g) (F.map h)).
hom ≫ F.map f ◁ F.mapComp g h ≫ F.mapComp f (g ≫ h) ≫ F.map₂ (α_ f g h).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.LaxFunctor.map₂_associator_assoc`：∀ {B : Type u₁} [inst :
 CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory 
C]   (self : CategoryTheory.LaxFuncto…
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_comp`：∀ {B : Type u₁} [inst : Category
Theory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (sel
f : CategoryTheory.PrelaxFun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_id`：∀ {B : Type u₁} [inst : CategoryTh
eory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (self 
: CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp_assoc_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f g ▷ F.map h ≫ F.mapComp (f ≫ g) h = (α_ (F.map f) (F.map g) (F.map h)).hom ≫
      F.map f ◁ F.mapComp g h ≫ F.mapComp f (g ≫ h) ≫ F.map₂ (α_ f g h).inv := by
  rw [← F.map₂_associator_assoc, ← F.map₂_comp]
  simp only [Iso.hom_inv_id, PrelaxFunctor.map₂_id, comp_id]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.LaxFunctor.mapComp_assoc_right** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.LaxFunctor`。
形式化陈述：mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.
map f ◁ F.mapComp g h ≫ F.mapComp f (g ≫ h) = (α_ (F.map f) (F.map g) (F.map h))
.inv ≫ F.mapComp f g ▷ F.map h ≫ F.mapComp (f ≫ g) h ≫ F.map₂ (α_ f g h).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.LaxFunctor.map₂_associator`：∀ {B : Type u₁} [inst : Categ
oryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (
self : CategoryTheory.LaxFuncto…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ F.mapComp g h ≫ F.mapComp f (g ≫ h) =
      (α_ (F.map f) (F.map g) (F.map h)).inv ≫ F.mapComp f g ▷ F.map h ≫
        F.mapComp (f ≫ g) h ≫ F.map₂ (α_ f g h).hom := by
  simp only [map₂_associator, Iso.inv_hom_id_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.LaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LaxFun
ctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma map₂_leftUnitor_hom {a b : B} (f : a ⟶ b) :
    (λ_ (F.map f)).hom = F.mapId a ▷ F.map f ≫ F.mapComp (𝟙 a) f ≫ F.map₂ (λ_ f).hom := by
  rw [← PrelaxFunctor.map₂Iso_hom, ← assoc, ← Iso.comp_inv_eq, ← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_leftUnitor]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.LaxFunctor.map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LaxFun
ctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma map₂_rightUnitor_hom {a b : B} (f : a ⟶ b) :
    (ρ_ (F.map f)).hom = F.map f ◁ F.mapId b ≫ F.mapComp f (𝟙 b) ≫ F.map₂ (ρ_ f).hom := by
  rw [← PrelaxFunctor.map₂Iso_hom, ← assoc, ← Iso.comp_inv_eq, ← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_rightUnitor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity lax functor. -/
@[simps]
/-
**CategoryTheory.LaxFunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.LaxFunc
tor`。
形式化陈述：id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᴸ B where toPrelaxFunctor
参数：B : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity lax functor.
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᴸ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)
/-
**CategoryTheory.LaxFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.LaxFuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (B ⥤ᴸ B) :=
  ⟨id B⟩

/-- More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
/-
**CategoryTheory.LaxFunctor.mapId'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lax
Functor`。
形式化陈述：mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b
参数：f : b ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.)
-/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    𝟙 (F.obj b) ⟶ F.map f :=
  F.mapId _ ≫ F.map₂ (eqToHom (by rw [hf]))
/-
**CategoryTheory.LaxFunctor.mapId'_eq_mapId** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.LaxFunctor`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.LaxFunctor B C) (b : B), F
.mapId' (CategoryTheory.CategoryStruct.id b) ⋯ = F.mapId b
参数：F : CategoryTheory.LaxFunctor B C；b : B；CategoryTheory.CategoryStruct.id b。
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
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/-- More flexible variant of `mapComp`. (See `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
/-
**CategoryTheory.LaxFunctor.mapComp'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
axFunctor`。
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
    F.map f ≫ F.map g ⟶ F.map fg :=
  F.mapComp f g ≫ F.map₂ (eqToHom (by rw [h]))
/-
**CategoryTheory.LaxFunctor.mapComp'_eq_mapComp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.LaxFunctor`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.LaxFunctor B C) {b₀ b₁ b₂ 
: B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂),   F.mapComp' f g (CategoryTheory.CategoryStruc
t.comp f g) ⋯ = F.mapComp f g
参数：F : CategoryTheory.LaxFunctor B C；f : b₀ ⟶ b₁；g : b₁ ⟶ b₂；CategoryTheory.Cate
goryStruct.comp f g。
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
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of lax functors. -/
@[simps]
/-
**CategoryTheory.LaxFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.LaxFu
nctor`。
形式化陈述：comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D) : B ⥤
ᴸ D where toPrelaxFunctor
参数：F : B ⥤ᴸ C；G : C ⥤ᴸ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of lax functors.
-/
def comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D) :
    B ⥤ᴸ D where
  toPrelaxFunctor := PrelaxFunctor.comp F.toPrelaxFunctor G.toPrelaxFunctor
  mapId := fun a => G.mapId (F.obj a) ≫ G.map₂ (F.mapId a)
  mapComp := fun f g => G.mapComp (F.map f) (F.map g) ≫ G.map₂ (F.mapComp f g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [assoc, ← G.map₂_comp, mapComp_naturality_left, G.map₂_comp, mapComp_naturality_left_assoc]
  mapComp_naturality_right := fun f _ _ η => by
    dsimp
    rw [assoc, ← G.map₂_comp, mapComp_naturality_right, G.map₂_comp, mapComp_naturality_right_assoc]
  map₂_associator := fun f g h => by
    dsimp
    slice_rhs 1 3 =>
      rw [Bicategory.whiskerLeft_comp, assoc, ← mapComp_naturality_right, ← map₂_associator_assoc]
    slice_rhs 3 5 =>
      rw [← G.map₂_comp, ← G.map₂_comp, ← F.map₂_associator, G.map₂_comp, G.map₂_comp]
    slice_lhs 1 3 =>
      rw [comp_whiskerRight, assoc, ← G.mapComp_naturality_left_assoc]
    simp only [assoc]
  map₂_leftUnitor := fun f => by
    dsimp
    simp only [map₂_leftUnitor, PrelaxFunctor.map₂_comp, assoc, mapComp_naturality_left_assoc,
      comp_whiskerRight]
  map₂_rightUnitor := fun f => by
    dsimp
    simp only [map₂_rightUnitor, PrelaxFunctor.map₂_comp, assoc, mapComp_naturality_right_assoc,
      Bicategory.whiskerLeft_comp]

/-- A structure on a lax functor that promotes a lax functor to a pseudofunctor.

See `Pseudofunctor.mkOfLax`. -/
/-
**CategoryTheory.LaxFunctor.PseudoCore** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.LaxFunctor`。
形式化陈述：PseudoCore (F : B ⥤ᴸ C) where /-- The isomorphism giving rise to the lax u
nity constraint -/ mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a) /-- The isomorph
ism giving rise to the lax functoriality constraint -/ mapCompIso {a b c : B} (f
 : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g /-- `mapIdIso` gives r
ise to the lax unity constraint -/ mapIdIso_inv {a : B} : (mapIdIso a).inv = F.m
apId a
参数：F : B ⥤ᴸ C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure on a lax functor that promotes a lax functor to a pseudofunctor.

See `Pseudofunctor.mkOfLax`.
-/
structure PseudoCore (F : B ⥤ᴸ C) where
  /-- The isomorphism giving rise to the lax unity constraint -/
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  /-- The isomorphism giving rise to the lax functoriality constraint -/
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  /-- `mapIdIso` gives rise to the lax unity constraint -/
  mapIdIso_inv {a : B} : (mapIdIso a).inv = F.mapId a := by cat_disch
  /-- `mapCompIso` gives rise to the lax functoriality constraint -/
  mapCompIso_inv {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : (mapCompIso f g).inv = F.mapComp f g := by
    cat_disch

attribute [simp] PseudoCore.mapIdIso_inv PseudoCore.mapCompIso_inv

end LaxFunctor

end CategoryTheory

