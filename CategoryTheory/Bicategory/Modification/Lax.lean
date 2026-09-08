/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax

/-!
# Modifications between transformations of lax functors

In this file we define modifications of lax and oplax transformations of lax functors.

A modification `Γ` between lax transformations `η` and `θ` (of lax functors) consists of a family
of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which for all 1-morphisms `f : a ⟶ b`
satisfies the equation `app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b`.

Modifications between oplax transformations are defined similarly.

## Main definitions

Given two lax functors `F` and `G`, we define:

* `LaxTrans.Modification η θ`: modifications between lax transformations `η` and `θ` between
  `F` and `G`.
* `LaxTrans.homCategory F G`: the category structure on the lax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this is a
  scoped instance in the `Lax.LaxTrans` namespace, so you need to run
  `open scoped Lax.LaxTrans` to access it.

* `OplaxTrans.Modification η θ`: modifications between oplax transformations `η` and `θ`
  between `F` and `G`.
* `OplaxTrans.homCategory F G`: the category structure on the oplax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this is a
  scoped instance in the `Lax.OplaxTrans` namespace, so you need to run
  `open scoped Lax.OplaxTrans` to access it.
-/

@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂
variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᴸ C}

namespace LaxTrans

open scoped Lax.LaxTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between lax natural transformations `η` and `θ` (between lax functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(app a ▷ G.map f) ≫ θ.naturality f = η.naturality f ≫ (F.map f ◁ app b)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
/-
**CategoryTheory.Lax.LaxTrans.Modification** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Lax.LaxTrans`。
形式化陈述：Modification where /-- The underlying family of 2-morphisms. -/ app (a : B
) : η.app a ⟶ θ.app a /-- The naturality condition. -/ naturality : forall {a b 
: B} (f : a ⟶ b), app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ 
app b
参数：a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification `Γ` between lax natural transformations `η` and `θ` (between lax 
functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfi
es the equation
`(app a ▷ G.map f) ≫ θ.naturality f = η.naturality f ≫ (F.map f ◁ app b)`
for each 1-morphism `f : a ⟶ b`.
-/
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b := by
    cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (η) in
/-- The identity modification. -/
@[simps]
/-
**CategoryTheory.Lax.LaxTrans.Modification.id** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Lax.LaxTrans.Modification`。
形式化陈述：id : Modification η η where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity modification.
-/
def id : Modification η η where
  app a := 𝟙 (η.app a)
/-
**CategoryTheory.Lax.LaxTrans.Modification.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Lax.LaxTrans.Modification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/-
**CategoryTheory.Lax.LaxTrans.Modification.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Lax.LaxTrans.Modification`。
形式化陈述：vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modifica
tion η ι where app a
参数：Γ : Modification η θ；Δ : Modification θ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of modifications.
-/
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between lax transformations of lax functors. This is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with lax
transformations. -/
@[ext]
/-
**CategoryTheory.Lax.LaxTrans.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.La
x.LaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
LaxFunctor B C} → (F ⟶ G) → (F ⟶ G) → Type (max u₁ w₂)
参数：F ⟶ G；F ⟶ G；max u₁ w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type-alias for modifications between lax transformations of lax functors. This i
s the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with lax
transformations.
-/
structure Hom where
  of ::
  /-- The underlying modification of lax transformations. -/
  as : Modification η θ

/-- Category structure on the lax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.LaxTrans` namespace. -/
@[simps!]
/-
**CategoryTheory.Lax.LaxTrans.homCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Lax.LaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
LaxFunctor B C} → CategoryTheory.Category.{max u₁ w₂, max (max (max u₁ v₁) v₂) w
₂} (F ⟶ G)
参数：max (max u₁ v₁) v₂；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on the lax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.LaxTrans` namespace.
-/
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩
/-
**CategoryTheory.Lax.LaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.Lax
Trans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/-
**CategoryTheory.Lax.LaxTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Lax.LaxTrans.homCategory`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   {F G : CategoryTheory.LaxFunctor B C} {η θ : F
 ⟶ G} {Γ Δ : η ⟶ θ}, (∀ (a : B), Γ.as.app a = Δ.as.app a) → Γ = Δ
参数：∀ (a : B), Γ.as.app a = Δ.as.app a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Lax.LaxTrans.Hom.ext`：∀ {B : Type u₁} {inst : CategoryThe
ory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C}   {F G : 
CategoryTheory.LaxFunctor…
· 使用定理 `CategoryTheory.Lax.LaxTrans.Modification.ext`：∀ {B : Type u₁} {inst : Ca
tegoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C} 
  {F G : CategoryTheory.LaxFunctor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma homCategory.ext {Γ Δ : η ⟶ θ} (h : ∀ a, Γ.as.app a = Δ.as.app a) : Γ = Δ :=
  Hom.ext <| Modification.ext <| funext h

/-- Construct a modification isomorphism between lax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Lax.LaxTrans.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.La
x.LaxTrans`。
形式化陈述：isoMk (app : forall a, η.app a ≅ θ.app a) (naturality : forall {a b} (f : 
a ⟶ b), (app a).hom ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ (app
 b).hom
参数：app : forall a, η.app a ≅ θ.app a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a modification isomorphism between lax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward
 direction.
-/
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        (app a).hom ▷ G.map f ≫ θ.naturality f =
          η.naturality f ≫ F.map f ◁ (app b).hom := by cat_disch) :
    η ≅ θ where
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using (app a).inv ▷ G.map f ≫= (naturality f).symm =≫ F.map f ◁ (app b).inv

end LaxTrans

namespace OplaxTrans

open scoped Lax.OplaxTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between oplax natural transformations `η` and `θ` (between lax functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
/-
**CategoryTheory.Lax.OplaxTrans.Modification** 是 Mathlib 中的一个结构，位于命名空间 `Category
Theory.Lax.OplaxTrans`。
形式化陈述：Modification where /-- The underlying family of 2-morphisms. -/ app (a : B
) : η.app a ⟶ θ.app a /-- The naturality condition. -/ naturality : forall {a b 
: B} (f : a ⟶ b), F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.
map f
参数：a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification `Γ` between oplax natural transformations `η` and `θ` (between la
x functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfi
es the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    ∀ {a b : B} (f : a ⟶ b),
      F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f := by
    cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (η) in
/-- The identity modification. -/
@[simps]
/-
**CategoryTheory.Lax.OplaxTrans.Modification.id** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Lax.OplaxTrans.Modification`。
形式化陈述：id : Modification η η where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity modification.
-/
def id : Modification η η where
  app a := 𝟙 (η.app a)
/-
**CategoryTheory.Lax.OplaxTrans.Modification.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Lax.OplaxTrans.Modification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/-
**CategoryTheory.Lax.OplaxTrans.Modification.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Lax.OplaxTrans.Modification`。
形式化陈述：vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modifica
tion η ι where app a
参数：Γ : Modification η θ；Δ : Modification θ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of modifications.
-/
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) :
    Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between oplax transformations of lax functors. This is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with oplax
transformations. -/
@[ext]
/-
**CategoryTheory.Lax.OplaxTrans.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Lax.OplaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
LaxFunctor B C} → (F ⟶ G) → (F ⟶ G) → Type (max u₁ w₂)
参数：F ⟶ G；F ⟶ G；max u₁ w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type-alias for modifications between oplax transformations of lax functors. This
 is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with opl
ax
transformations.
-/
structure Hom where
  of ::
  /-- The underlying modification of oplax transformations. -/
  as : Modification η θ

/-- Category structure on the oplax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.OplaxTrans` namespace. -/
@[simps!]
/-
**CategoryTheory.Lax.OplaxTrans.homCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Lax.OplaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
LaxFunctor B C} → CategoryTheory.Category.{max u₁ w₂, max (max (max u₁ v₁) v₂) w
₂} (F ⟶ G)
参数：max (max u₁ v₁) v₂；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on the oplax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.OplaxTrans` namespace.
-/
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩
/-
**CategoryTheory.Lax.OplaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.O
plaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/-
**CategoryTheory.Lax.OplaxTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Lax.OplaxTrans.homCategory`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   {F G : CategoryTheory.LaxFunctor B C} {η θ : F
 ⟶ G} {Γ Δ : η ⟶ θ}, (∀ (a : B), Γ.as.app a = Δ.as.app a) → Γ = Δ
参数：∀ (a : B), Γ.as.app a = Δ.as.app a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Lax.OplaxTrans.Hom.ext`：∀ {B : Type u₁} {inst : CategoryT
heory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C}   {F G 
: CategoryTheory.LaxFunctor…
· 使用定理 `CategoryTheory.Lax.OplaxTrans.Modification.ext`：∀ {B : Type u₁} {inst : 
CategoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C
}   {F G : CategoryTheory.LaxFunctor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma homCategory.ext {Γ Δ : η ⟶ θ} (h : ∀ a, Γ.as.app a = Δ.as.app a) : Γ = Δ :=
  Hom.ext <| Modification.ext <| funext h

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Lax.OplaxTrans.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Lax.OplaxTrans`。
形式化陈述：isoMk (app : forall a, η.app a ≅ θ.app a) (naturality : forall {a b} (f : 
a ⟶ b), F.map f ◁ (app b).hom ≫ θ.naturality f = η.naturality f ≫ (app a).hom ▷ 
G.map f
参数：app : forall a, η.app a ≅ θ.app a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward
 direction.
-/
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality :
      ∀ {a b} (f : a ⟶ b),
        F.map f ◁ (app b).hom ≫ θ.naturality f =
          η.naturality f ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using F.map f ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ G.map f

end OplaxTrans

end CategoryTheory.Lax

