/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
public import Mathlib.CategoryTheory.Bicategory.Functor.Lax
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Pseudofunctors

A pseudofunctor is an oplax (or lax) functor whose `mapId` and `mapComp` are isomorphisms.
We provide several constructors for pseudofunctors:
* `Pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `mapComp`.

* `Pseudofunctor.mkOfOplax` : construct a pseudofunctor from an oplax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfOplax'` : similar to `mkOfOplax`, but uses `IsIso` to describe isomorphisms.

* `Pseudofunctor.mkOfLax` : construct a pseudofunctor from a lax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfLax'` : similar to `mkOfLax`, but uses `IsIso` to describe isomorphisms.

## Main definitions

* `CategoryTheory.Pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`, which we
  denote by `B ⥤ᵖ C`.
* `CategoryTheory.Pseudofunctor.comp F G` : the composition of pseudofunctors

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- A pseudofunctor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute with composition,
and does not need to strictly preserve the identity. Instead, there are specified 2-isomorphisms
`F.map (𝟙 a) ≅ 𝟙 (F.obj a)` and `F.map (f ≫ g) ≅ F.map f ≫ F.map g`.

`F.map₂` strictly commutes with compositions and preserves the identity. It also preserves the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
/-
**CategoryTheory.Pseudofunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicateg
ory.{w₂, v₂} C] extends PrelaxFunctor B C where mapId (a : B) : map (𝟙 a) ≅ 𝟙 (o
bj a) mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g 
map₂_whisker_left : forall {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), ma
p₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv
参数：B : Type u₁；C : Type u₂；a : B。
继承自：PrelaxFunctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudofunctor `F` between bicategories `B` and `C` consists of a function betw
een objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphi
sms `F.map₂`.

Unlike functors between categories, `F.map` does not need to strictly commute wi
th composition,
and does not need to strictly preserve the identity. Instead, there are specifie
d 2-isomorphisms
`F.map (𝟙 a) ≅ 𝟙 (F.obj a)` and `F.map (f ≫ g) ≅ F.map f ≫ F.map g`.

`F.map₂` strictly commutes with compositions and preserves the identity. It also
 preserves the
associator, the left unitor, and the right unitor modulo some adjustments of dom
ains and codomains
of 2-morphisms.
-/
structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    cat_disch
  map₂_whisker_right :
    ∀ {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    cat_disch
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    cat_disch
  map₂_left_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (λ_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    cat_disch

/-- Notation for a pseudofunctor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᵖ " => Pseudofunctor -- type as \func\^p

initialize_simps_projections Pseudofunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace Pseudofunctor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [simp, to_app (attr := reassoc)]
  map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

section

open Iso

/-- The underlying prelax functor. -/
add_decl_doc Pseudofunctor.toPrelaxFunctor


attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId
  CategoryTheory.Pseudofunctor.mapComp
  CategoryTheory.Pseudofunctor.map₂_whisker_left
  CategoryTheory.Pseudofunctor.map₂_whisker_right
  CategoryTheory.Pseudofunctor.map₂_associator
  CategoryTheory.Pseudofunctor.map₂_left_unitor
  CategoryTheory.Pseudofunctor.map₂_right_unitor

variable (F : B ⥤ᵖ C)

/-- The oplax functor associated with a pseudofunctor. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.toOplax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Pseudofunctor`。
形式化陈述：toOplax : B ⥤ᵒᵖᴸ C where toPrelaxFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oplax functor associated with a pseudofunctor.
-/
def toOplax : B ⥤ᵒᵖᴸ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom
/-
**CategoryTheory.Pseudofunctor.hasCoeToOplax** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Pseudofunctor`。
形式化陈述：hasCoeToOplax : Coe (B ⥤ᵖ C) (B ⥤ᵒᵖᴸ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToOplax : Coe (B ⥤ᵖ C) (B ⥤ᵒᵖᴸ C) :=
  ⟨toOplax⟩

/-- The lax functor associated with a pseudofunctor. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.toLax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
seudofunctor`。
形式化陈述：toLax : B ⥤ᴸ C where toPrelaxFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lax functor associated with a pseudofunctor.
-/
def toLax : B ⥤ᴸ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv, eq_inv_comp, comp_inv_eq]
    simp
/-
**CategoryTheory.Pseudofunctor.hasCoeToLax** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pseudofunctor`。
形式化陈述：hasCoeToLax : Coe (B ⥤ᵖ C) (B ⥤ᴸ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToLax : Coe (B ⥤ᵖ C) (B ⥤ᴸ C) :=
  ⟨toLax⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity pseudofunctor. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pseu
dofunctor`。
形式化陈述：id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵖ B where toPrelaxFunctor
参数：B : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity pseudofunctor.
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵖ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)
/-
**CategoryTheory.Pseudofunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pseudo
functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (B ⥤ᵖ B) :=
  ⟨id B⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of pseudofunctors. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ps
eudofunctor`。
形式化陈述：comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) : B ⥤ᵖ D where toPrelaxFunctor
参数：F : B ⥤ᵖ C；G : C ⥤ᵖ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of pseudofunctors.
-/
def comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) : B ⥤ᵖ D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)

section

variable (F : B ⥤ᵖ C) {a b : B}

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_assoc_right_hom** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：mapComp_assoc_right_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (F
.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom = F.map₂ (α_ f g h).inv 
≫ (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h ≫ (α_ (F.map f) (F.m
ap g) (F.map h)).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.OplaxFunctor.mapComp_assoc_right`：mapComp_assoc_right {a 
b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.mapComp f (g ≫ h) ≫ F.map f ◁
 F.mapComp g h = F.map₂ (α_ f g h).in…
-/
lemma mapComp_assoc_right_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom = F.map₂ (α_ f g h).inv ≫
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom :=
  F.toOplax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_assoc_left_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：mapComp_assoc_left_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (F.
mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h = F.map₂ (α_ f g h).hom ≫
 (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom ≫ (α_ (F.map f) (F.ma
p g) (F.map h)).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.OplaxFunctor.mapComp_assoc_left`：mapComp_assoc_left {a b 
c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.mapComp (f ≫ g) h ≫ F.mapComp f
 g ▷ F.map h = F.map₂ (α_ f g h).hom…
-/
lemma mapComp_assoc_left_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h =
    F.map₂ (α_ f g h).hom ≫ (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom
    ≫ (α_ (F.map f) (F.map g) (F.map h)).inv :=
  F.toOplax.mapComp_assoc_left _ _ _

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_assoc_right_inv** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：mapComp_assoc_right_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.
map f ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv = (α_ (F.map f) (F.map g
) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv ≫ F
.map₂ (α_ f g h).hom
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LaxFunctor.mapComp_assoc_right`：mapComp_assoc_right {a b 
c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.map f ◁ F.mapComp g h ≫ F.mapCo
mp f (g ≫ h) = (α_ (F.map f) (F.map…
-/
lemma mapComp_assoc_right_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv =
    (α_ (F.map f) (F.map g) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫
    (F.mapComp (f ≫ g) h).inv ≫ F.map₂ (α_ f g h).hom :=
  F.toLax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_assoc_left_inv** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：mapComp_assoc_left_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (F.
mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv = (α_ (F.map f) (F.map g)
 (F.map h)).hom ≫ F.map f ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv ≫ F.
map₂ (α_ f g h).inv
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LaxFunctor.mapComp_assoc_left`：mapComp_assoc_left {a b c 
d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : F.mapComp f g ▷ F.map h ≫ F.mapComp
 (f ≫ g) h = (α_ (F.map f) (F.map …
-/
lemma mapComp_assoc_left_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv =
    (α_ (F.map f) (F.map g) (F.map h)).hom ≫ F.map f ◁ (F.mapComp g h).inv ≫
    (F.mapComp f (g ≫ h)).inv ≫ F.map₂ (α_ f g h).inv :=
  F.toLax.mapComp_assoc_left _ _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_id_left_hom** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Pseudofunctor`。
形式化陈述：mapComp_id_left_hom (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom = F.map₂ (fun_ f
).hom ≫ (fun_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_left_unitor`：∀ {B : Type u₁} [inst : C
ategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]
   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Bicategory.hom_inv_whiskerRight`：hom_inv_whiskerRight {f 
g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c) : η.hom ▷ h ≫ η.inv ▷ h = 𝟙 (f ≫ h)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp_id_left_hom (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom =
    F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f := by
  simp
/-
**CategoryTheory.Pseudofunctor.mapComp_id_left** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Pseudofunctor`。
形式化陈述：mapComp_id_left (f : a ⟶ b) : (F.mapComp (𝟙 a) f) = F.map₂Iso (fun_ f) ≪≫ 
(fun_ (F.map f)).symm ≪≫ (whiskerRightIso (F.mapId a) (F.map f)).symm
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_left_hom`：mapComp_id_left_hom (f
 : a ⟶ b) : (F.mapComp (𝟙 a) f).hom = F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv
 ≫ (F.mapId a).inv ▷ F.map f
-/
lemma mapComp_id_left (f : a ⟶ b) : (F.mapComp (𝟙 a) f) = F.map₂Iso (λ_ f) ≪≫
    (λ_ (F.map f)).symm ≪≫ (whiskerRightIso (F.mapId a) (F.map f)).symm :=
  Iso.ext <| F.mapComp_id_left_hom f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_id_left_inv** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Pseudofunctor`。
形式化陈述：mapComp_id_left_inv (f : a ⟶ b) : (F.mapComp (𝟙 a) f).inv = (F.mapId a).ho
m ▷ F.map f ≫ (fun_ (F.map f)).hom ≫ F.map₂ (fun_ f).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_left`：mapComp_id_left (f : a ⟶ b
) : (F.mapComp (𝟙 a) f) = F.map₂Iso (fun_ f) ≪≫ (fun_ (F.map f)).symm ≪≫ (whiske
rRightIso (F.mapId a) (F.map f)).s…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.PrelaxFunctor.mapFunctor_map`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (F : CategoryTheory.PrelaxFuncto…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp_id_left_inv (f : a ⟶ b) : (F.mapComp (𝟙 a) f).inv =
    (F.mapId a).hom ▷ F.map f ≫ (λ_ (F.map f)).hom ≫ F.map₂ (λ_ f).inv := by
  simp [mapComp_id_left]
/-
**CategoryTheory.Pseudofunctor.whiskerRightIso_mapId** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：whiskerRightIso_mapId (f : a ⟶ b) : whiskerRightIso (F.mapId a) (F.map f) 
= (F.mapComp (𝟙 a) f).symm ≪≫ F.map₂Iso (fun_ f) ≪≫ (fun_ (F.map f)).symm
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_left`：mapComp_id_left (f : a ⟶ b
) : (F.mapComp (𝟙 a) f) = F.map₂Iso (fun_ f) ≪≫ (fun_ (F.map f)).symm ≪≫ (whiske
rRightIso (F.mapId a) (F.map f)).s…
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Iso.symm_self_id_assoc`：symm_self_id_assoc (α : X ≅ Y) (β
 : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β
· 使用定理 `CategoryTheory.Iso.self_symm_id`：self_symm_id (α : X ≅ Y) : α ≪≫ α.symm 
= Iso.refl X
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRightIso_mapId (f : a ⟶ b) : whiskerRightIso (F.mapId a) (F.map f) =
    (F.mapComp (𝟙 a) f).symm ≪≫ F.map₂Iso (λ_ f) ≪≫ (λ_ (F.map f)).symm := by
  simp [mapComp_id_left]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.whiskerRight_mapId_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：whiskerRight_mapId_hom (f : a ⟶ b) : (F.mapId a).hom ▷ F.map f = (F.mapCom
p (𝟙 a) f).inv ≫ F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_left_unitor`：∀ {B : Type u₁} [inst : C
ategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]
   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma whiskerRight_mapId_hom (f : a ⟶ b) : (F.mapId a).hom ▷ F.map f =
    (F.mapComp (𝟙 a) f).inv ≫ F.map₂ (λ_ f).hom ≫ (λ_ (F.map f)).inv := by
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.whiskerRight_mapId_inv** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：whiskerRight_mapId_inv (f : a ⟶ b) : (F.mapId a).inv ▷ F.map f = (fun_ (F.
map f)).hom ≫ F.map₂ (fun_ f).inv ≫ (F.mapComp (𝟙 a) f).hom
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.PrelaxFunctor.mapFunctor_map`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (F : CategoryTheory.PrelaxFuncto…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Pseudofunctor.whiskerRightIso_mapId`：whiskerRightIso_mapI
d (f : a ⟶ b) : whiskerRightIso (F.mapId a) (F.map f) = (F.mapComp (𝟙 a) f).symm
 ≪≫ F.map₂Iso (fun_ f) ≪≫ (fun_ (F.map f…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma whiskerRight_mapId_inv (f : a ⟶ b) : (F.mapId a).inv ▷ F.map f =
    (λ_ (F.map f)).hom ≫ F.map₂ (λ_ f).inv ≫ (F.mapComp (𝟙 a) f).hom := by
  simpa using congrArg (·.inv) (F.whiskerRightIso_mapId f)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_id_right_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：mapComp_id_right_hom (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom = F.map₂ (ρ_ f)
.hom ≫ (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_right_unitor`：∀ {B : Type u₁} [inst : 
CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C
]   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_hom_inv`：whiskerLeft_hom_inv (f : 
a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) : f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp_id_right_hom (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom =
    F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv := by
  simp
/-
**CategoryTheory.Pseudofunctor.mapComp_id_right** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Pseudofunctor`。
形式化陈述：mapComp_id_right (f : a ⟶ b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫ (
ρ_ (F.map f)).symm ≪≫ (whiskerLeftIso (F.map f) (F.mapId b)).symm
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_right_hom`：mapComp_id_right_hom 
(f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom = F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv ≫
 F.map f ◁ (F.mapId b).inv
-/
lemma mapComp_id_right (f : a ⟶ b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫
    (ρ_ (F.map f)).symm ≪≫ (whiskerLeftIso (F.map f) (F.mapId b)).symm :=
  Iso.ext <| F.mapComp_id_right_hom f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.mapComp_id_right_inv** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：mapComp_id_right_inv (f : a ⟶ b) : (F.mapComp f (𝟙 b)).inv = F.map f ◁ (F.
mapId b).hom ≫ (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_right`：mapComp_id_right (f : a ⟶
 b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm ≪≫ (whiskerL
eftIso (F.map f) (F.mapId b)).symm
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.PrelaxFunctor.mapFunctor_map`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (F : CategoryTheory.PrelaxFuncto…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp_id_right_inv (f : a ⟶ b) : (F.mapComp f (𝟙 b)).inv =
    F.map f ◁ (F.mapId b).hom ≫ (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv := by
  simp [mapComp_id_right]
/-
**CategoryTheory.Pseudofunctor.whiskerLeftIso_mapId** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor`。
形式化陈述：whiskerLeftIso_mapId (f : a ⟶ b) : whiskerLeftIso (F.map f) (F.mapId b) = 
(F.mapComp f (𝟙 b)).symm ≪≫ F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp_id_right`：mapComp_id_right (f : a ⟶
 b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm ≪≫ (whiskerL
eftIso (F.map f) (F.mapId b)).symm
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Iso.symm_self_id_assoc`：symm_self_id_assoc (α : X ≅ Y) (β
 : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β
· 使用定理 `CategoryTheory.Iso.self_symm_id`：self_symm_id (α : X ≅ Y) : α ≪≫ α.symm 
= Iso.refl X
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeftIso_mapId (f : a ⟶ b) : whiskerLeftIso (F.map f) (F.mapId b) =
    (F.mapComp f (𝟙 b)).symm ≪≫ F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm := by
  simp [mapComp_id_right]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.whiskerLeft_mapId_hom** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：whiskerLeft_mapId_hom (f : a ⟶ b) : F.map f ◁ (F.mapId b).hom = (F.mapComp
 f (𝟙 b)).inv ≫ F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_right_unitor`：∀ {B : Type u₁} [inst : 
CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C
]   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma whiskerLeft_mapId_hom (f : a ⟶ b) : F.map f ◁ (F.mapId b).hom =
    (F.mapComp f (𝟙 b)).inv ≫ F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv := by
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.whiskerLeft_mapId_inv** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：whiskerLeft_mapId_inv (f : a ⟶ b) : F.map f ◁ (F.mapId b).inv = (ρ_ (F.map
 f)).hom ≫ F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.PrelaxFunctor.mapFunctor_map`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (F : CategoryTheory.PrelaxFuncto…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Pseudofunctor.whiskerLeftIso_mapId`：whiskerLeftIso_mapId 
(f : a ⟶ b) : whiskerLeftIso (F.map f) (F.mapId b) = (F.mapComp f (𝟙 b)).symm ≪≫
 F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).sym…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma whiskerLeft_mapId_inv (f : a ⟶ b) : F.map f ◁ (F.mapId b).inv =
    (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom := by
  simpa using congrArg (·.inv) (F.whiskerLeftIso_mapId f)

/-- More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
/-
**CategoryTheory.Pseudofunctor.mapId'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Pseudofunctor`。
形式化陈述：mapId'_hom_naturality : (F.map f).toFunctor.map a ≫ (F.mapId' f hf).hom.to
NatTrans.app Y = (F.mapId' f hf).hom.toNatTrans.app X ≫ a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More flexible variant of `mapId`. (See the file `Bicategory.Functor.Strict`
for applications to strict bicategories.)
-/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.map f ≅ 𝟙 (F.obj b) :=
  F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pseudofunctor.mapId'_eq_mapId** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.Pseudofunctor B C) (b : B)
, F.mapId' (CategoryTheory.CategoryStruct.id b) ⋯ = F.mapId b
参数：F : CategoryTheory.Pseudofunctor B C；b : B；CategoryTheory.CategoryStruct.id b
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pseudofunctor.mapId'`：mapId'_hom_naturality : (F.map f).t
oFunctor.map a ≫ (F.mapId' f hf).hom.toNatTrans.app Y = (F.mapId' f hf).hom.toNa
tTrans.app X ≫ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

@[simp]
/-
**CategoryTheory.Pseudofunctor.toLax_mapId'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Pseudofunctor`。
形式化陈述：toLax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b
参数：f : b ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.toLax.mapId' f hf = (F.mapId' f hf).inv :=
  rfl

@[simp]
/-
**CategoryTheory.Pseudofunctor.toOplax_mapId'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：toOplax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b
参数：f : b ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toOplax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.toOplax.mapId' f hf = (F.mapId' f hf).hom :=
  rfl

/-- More flexible variant of `mapComp`. (See `Bicategory.Functor.Strict`
for applications to strict bicategories.) -/
/-
**CategoryTheory.Pseudofunctor.mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mapComp'_hom_naturality : (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg 
hfg).hom.toNatTrans.app Y = (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.ma
p g).toFunctor.map ((F.map f).toFunctor.map a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More flexible variant of `mapComp`. (See `Bicategory.Functor.Strict`
for applications to strict bicategories.)
-/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.map fg ≅ F.map f ≫ F.map g :=
  F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.Pseudofunctor B C) {b₀ b₁ 
b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂),   F.mapComp' f g (CategoryTheory.CategorySt
ruct.comp f g) ⋯ = F.mapComp f g
参数：F : CategoryTheory.Pseudofunctor B C；f : b₀ ⟶ b₁；g : b₁ ⟶ b₂；CategoryTheory.C
ategoryStruct.comp f g。
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
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

@[simp]
/-
**CategoryTheory.Pseudofunctor.toLax_mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：toLax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂) (
h : f ≫ g = fg
参数：f : b₀ ⟶ b₁；g : b₁ ⟶ b₂；fg : b₀ ⟶ b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.toLax.mapComp' f g fg h = (F.mapComp' f g fg h).inv :=
  rfl

@[simp]
/-
**CategoryTheory.Pseudofunctor.toOplax_mapComp'** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Pseudofunctor`。
形式化陈述：toOplax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
 (h : f ≫ g = fg
参数：f : b₀ ⟶ b₁；g : b₁ ⟶ b₂；fg : b₀ ⟶ b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toOplax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.toOplax.mapComp' f g fg h = (F.mapComp' f g fg h).hom :=
  rfl

end

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.mkOfOplax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Pseudofunctor`。
形式化陈述：mkOfOplax (F : B ⥤ᵒᵖᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where toPrelaxFuncto
r
参数：F : B ⥤ᵒᵖᴸ C；F' : F.PseudoCore。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are 
isomorphisms.
-/
def mkOfOplax (F : B ⥤ᵒᵖᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left := fun f g h η => by
    rw [F'.mapCompIso_hom f g, ← F.mapComp_naturality_right_assoc, ← F'.mapCompIso_hom f h,
      hom_inv_id, comp_id]
  map₂_whisker_right := fun η h => by
    rw [F'.mapCompIso_hom _ h, ← F.mapComp_naturality_left_assoc, ← F'.mapCompIso_hom _ h,
      hom_inv_id, comp_id]
  map₂_associator := fun f g h => by
    rw [F'.mapCompIso_hom (f ≫ g) h, F'.mapCompIso_hom f g, ← F.map₂_associator_assoc, ←
      F'.mapCompIso_hom f (g ≫ h), ← F'.mapCompIso_hom g h, whiskerLeft_hom_inv_assoc,
      hom_inv_id, comp_id]

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.mkOfOplax'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Pseudofunctor`。
形式化陈述：mkOfOplax' (F : B ⥤ᵒᵖᴸ C) [forall a, IsIso (F.mapId a)] [forall {a b c} (f
 : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C where toPrelaxFunctor
参数：F : B ⥤ᵒᵖᴸ C；F.mapId a；f : a ⟶ b；g : b ⟶ c；F.mapComp f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are 
isomorphisms.
-/
noncomputable def mkOfOplax' (F : B ⥤ᵒᵖᴸ C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => asIso (F.mapId a)
  mapComp := fun f g => asIso (F.mapComp f g)
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_right]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [← assoc, IsIso.eq_comp_inv, F.mapComp_naturality_left]
  map₂_associator := fun f g h => by
    dsimp
    simp only [← assoc]
    rw [IsIso.eq_comp_inv, ← Bicategory.inv_whiskerLeft, IsIso.eq_comp_inv]
    simp only [assoc, F.map₂_associator]

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.mkOfLax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Pseudofunctor`。
形式化陈述：mkOfLax (F : B ⥤ᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where toPrelaxFunctor
参数：F : B ⥤ᴸ C；F' : F.PseudoCore。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are iso
morphisms.
-/
def mkOfLax (F : B ⥤ᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_right, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv, ← LaxFunctor.mapComp_naturality_left, ← F'.mapCompIso_inv,
      hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv, F'.mapCompIso_inv, ← inv_comp_eq, ← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.mkOfLax'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：mkOfLax' (F : B ⥤ᴸ C) [forall a, IsIso (F.mapId a)] [forall {a b c} (f : a
 ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C
参数：F : B ⥤ᴸ C；F.mapId a；f : a ⟶ b；g : b ⟶ c；F.mapComp f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are iso
morphisms.
-/
noncomputable def mkOfLax' (F : B ⥤ᴸ C) [∀ a, IsIso (F.mapId a)]
    [∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C :=
  mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }

end

end Pseudofunctor

end CategoryTheory

