/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# Modifications between transformations of oplax functors

In this file we define modifications of lax, oplax, and strong transformations of oplax functors.

A modification `Γ` between oplax transformations `η` and `θ` (of oplax functors) consists of a
family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which for all 1-morphisms `f : a ⟶ b`
satisfies the equation `(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`.

Modifications between lax and strong transformations are defined similarly.

## Main definitions

Given two oplax functors `F` and `G`, we define:

* `LaxTrans.Modification η θ`: modifications between lax transformations `η` and `θ` between
  `F` and `G`.
* `LaxTrans.homCategory F G`: the category structure on the lax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this a scoped
  instance in the `Oplax.LaxTrans` namespace, so you need to run `open scoped Oplax.LaxTrans`
  to access it.

* `OplaxTrans.Modification η θ`: modifications between oplax transformations `η` and `θ` between
  `F` and `G`.
* `OplaxTrans.homCategory F G`: the category structure on the oplax transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this a scoped
  instance in the `Oplax.OplaxTrans` namespace, so you need to run `open scoped Oplax.OplaxTrans`
  to access it.

* `StrongTrans.Modification η θ`: modifications between strong transformations `η` and `θ` between
  `F` and `G`.
* `StrongTrans.homCategory F G`: the category structure on the strong transformations
  between `F` and `G`, where composition is given by vertical composition. Note that this a scoped
  instance in the `Oplax.StrongTrans` namespace, so you need to run `open scoped Oplax.StrongTrans`
  to access it.

-/

@[expose] public section

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᵒᵖᴸ C}

namespace LaxTrans

open scoped Oplax.LaxTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between lax natural transformations `η` and `θ` (between oplax functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(app a ▷ G.map f) ≫ θ.naturality f = η.naturality f ≫ (F.map f ◁ app b)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
/-
**CategoryTheory.Oplax.LaxTrans.Modification** 是 Mathlib 中的一个结构，位于命名空间 `Category
Theory.Oplax.LaxTrans`。
形式化陈述：Modification where /-- The underlying family of 2-morphisms. -/ app (a : B
) : η.app a ⟶ θ.app a /-- The naturality condition. -/ naturality : forall {a b 
: B} (f : a ⟶ b), app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ 
app b
参数：a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification `Γ` between lax natural transformations `η` and `θ` (between opla
x functors)
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

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.LaxTrans.Modification.whiskerLeft_naturality** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Oplax.LaxTrans.Modification`。
形式化陈述：whiskerLeft_naturality (f : a' ⟶ F.obj a) (g : a ⟶ b) : f ◁ Γ.app a ▷ G.ma
p g ≫ f ◁ θ.naturality g = f ◁ η.naturality g ≫ f ◁ F.map g ◁ Γ.app b
参数：f : a' ⟶ F.obj a；g : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Oplax.LaxTrans.Modification.naturality`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj a) (g : a ⟶ b) :
    f ◁ Γ.app a ▷ G.map g ≫ f ◁ θ.naturality g =
      f ◁ η.naturality g ≫ f ◁ F.map g ◁ Γ.app b := by
  simp_rw [← whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.LaxTrans.Modification.whiskerRight_naturality** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Oplax.LaxTrans.Modification`。
形式化陈述：whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') : Γ.app a ▷ G.map f
 ▷ g ≫ θ.naturality f ▷ g = η.naturality f ▷ g ≫ (F.map f ◁ Γ.app b) ▷ g
参数：f : a ⟶ b；g : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Oplax.LaxTrans.Modification.naturality`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    Γ.app a ▷ G.map f ▷ g ≫ θ.naturality f ▷ g =
      η.naturality f ▷ g ≫ (F.map f ◁ Γ.app b) ▷ g := by
  simp_rw [← comp_whiskerRight, naturality]

end

variable (η) in
/-- The identity modification. -/
@[simps]
/-
**CategoryTheory.Oplax.LaxTrans.Modification.id** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Oplax.LaxTrans.Modification`。
形式化陈述：id : Modification η η where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity modification.
-/
def id : Modification η η where
  app a := 𝟙 (η.app a)
/-
**CategoryTheory.Oplax.LaxTrans.Modification.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Oplax.LaxTrans.Modification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/-
**CategoryTheory.Oplax.LaxTrans.Modification.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Oplax.LaxTrans.Modification`。
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
/-- Type-alias for modifications between lax transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with lax
transformations. -/
@[ext]
/-
**CategoryTheory.Oplax.LaxTrans.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Oplax.LaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} → (F ⟶ G) → (F ⟶ G) → Type (max u₁ w₂)
参数：F ⟶ G；F ⟶ G；max u₁ w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type-alias for modifications between lax transformations of oplax functors. This
 is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with l
ax
transformations.
-/
structure Hom where
  of ::
  /-- The underlying modification of lax transformations. -/
  as : Modification η θ

/-- Category structure on the lax natural transformations between oplax functors.

Note that this is a scoped instance in the `Oplax.LaxTrans` namespace. -/
@[simps!]
/-
**CategoryTheory.Oplax.LaxTrans.homCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Oplax.LaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} →           CategoryTheory.Category.{max u₁ w₂, max (max (max 
u₁ v₁) v₂) w₂} (F ⟶ G)
参数：max (max u₁ v₁) v₂；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on the lax natural transformations between oplax functors.

Note that this is a scoped instance in the `Oplax.LaxTrans` namespace.
-/
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩
/-
**CategoryTheory.Oplax.LaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Oplax
.LaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/-
**CategoryTheory.Oplax.LaxTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Oplax.LaxTrans.homCategory`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   {F G : CategoryTheory.OplaxFunctor B C} {η θ :
 F ⟶ G} {m n : η ⟶ θ}, (∀ (a : B), m.as.app a = n.as.app a) → m = n
参数：∀ (a : B), m.as.app a = n.as.app a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.LaxTrans.Hom.ext`：∀ {B : Type u₁} {inst : CategoryT
heory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C}   {F G 
: CategoryTheory.OplaxFunct…
· 使用定理 `CategoryTheory.Oplax.LaxTrans.Modification.ext`：∀ {B : Type u₁} {inst : 
CategoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C
}   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma homCategory.ext {m n : η ⟶ θ} (h : ∀ a, m.as.app a = n.as.app a) : m = n :=
  Hom.ext <| Modification.ext <| funext h

/-- Construct a modification isomorphism between lax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Oplax.LaxTrans.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Oplax.LaxTrans`。
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

variable (η θ : F ⟶ G)

/-- A modification `Γ` between oplax natural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ θ.naturality f = η.naturality f ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
/-
**CategoryTheory.Oplax.OplaxTrans.Modification** 是 Mathlib 中的一个结构，位于命名空间 `Catego
ryTheory.Oplax.OplaxTrans`。
形式化陈述：Modification where /-- The underlying family of 2-morphisms. -/ app (a : B
) : η.app a ⟶ θ.app a /-- The naturality condition. -/ naturality : forall {a b 
: B} (f : a ⟶ b), F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.
map f
参数：a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification `Γ` between oplax natural transformations `η` and `θ` consists of
 a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
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

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.Modification.whiskerLeft_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Oplax.OplaxTrans.Modification`。
形式化陈述：whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) : f ◁ F.map g ◁ Γ.ap
p c ≫ f ◁ θ.naturality g = f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.map g
参数：f : a' ⟶ F.obj b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.Modification.naturality`：∀ {B : Type u₁}
 [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bic
ategory C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ θ.naturality g =
      f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.map g := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.Modification.whiskerRight_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Oplax.OplaxTrans.Modification`。
形式化陈述：whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') : F.map f ◁ Γ.app b
 ▷ g ≫ (α_ _ _ _).inv ≫ θ.naturality f ▷ g = (α_ _ _ _).inv ≫ η.naturality f ▷ g
 ≫ Γ.app a ▷ G.map f ▷ g
参数：f : a ⟶ b；g : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.associator_inv_naturality_middle_assoc`：∀ {B :
 Type u} [inst : CategoryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : 
b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)   {Z : a ⟶ d} (h_1 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.Modification.naturality`：∀ {B : Type u₁}
 [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bic
ategory C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ θ.naturality f ▷ g =
      (α_ _ _ _).inv ≫ η.naturality f ▷ g ≫ Γ.app a ▷ G.map f ▷ g := by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]

end

variable (η) in
/-- The identity modification. -/
@[simps]
/-
**CategoryTheory.Oplax.OplaxTrans.Modification.id** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Oplax.OplaxTrans.Modification`。
形式化陈述：id : Modification η η where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity modification.
-/
def id : Modification η η where app a := 𝟙 (η.app a)
/-
**CategoryTheory.Oplax.OplaxTrans.Modification.** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Oplax.OplaxTrans.Modification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/-
**CategoryTheory.Oplax.OplaxTrans.Modification.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Oplax.OplaxTrans.Modification`。
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
/-- Type-alias for modifications between oplax transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with oplax
transformations. -/
@[ext]
/-
**CategoryTheory.Oplax.OplaxTrans.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Oplax.OplaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} → (F ⟶ G) → (F ⟶ G) → Type (max u₁ w₂)
参数：F ⟶ G；F ⟶ G；max u₁ w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type-alias for modifications between oplax transformations of oplax functors. Th
is is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with o
plax
transformations.
-/
structure Hom where
  of ::
  /-- The underlying modification of oplax transformations. -/
  as : Modification η θ

/-- Category structure on the oplax natural transformations between OplaxFunctors.

Note that this a scoped instance in the `Oplax.OplaxTrans` namespace. -/
@[simps!]
/-
**CategoryTheory.Oplax.OplaxTrans.homCategory** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Oplax.OplaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} →           CategoryTheory.Category.{max u₁ w₂, max (max (max 
u₁ v₁) v₂) w₂} (F ⟶ G)
参数：max (max u₁ v₁) v₂；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on the oplax natural transformations between OplaxFunctors.

Note that this a scoped instance in the `Oplax.OplaxTrans` namespace.
-/
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩
/-
**CategoryTheory.Oplax.OplaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Opl
ax.OplaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/-
**CategoryTheory.Oplax.OplaxTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Oplax.OplaxTrans.homCategory`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   {F G : CategoryTheory.OplaxFunctor B C} {η θ :
 F ⟶ G} {m n : η ⟶ θ}, (∀ (b : B), m.as.app b = n.as.app b) → m = n
参数：∀ (b : B), m.as.app b = n.as.app b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.Hom.ext`：∀ {B : Type u₁} {inst : Categor
yTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C}   {F 
G : CategoryTheory.OplaxFunct…
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.Modification.ext`：∀ {B : Type u₁} {inst 
: CategoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory
 C}   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.as.app b = n.as.app b) : m = n :=
  Hom.ext <| Modification.ext <| funext w

/-- Construct a modification isomorphism between oplax natural transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Oplax.OplaxTrans.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Oplax.OplaxTrans`。
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
    simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _

end OplaxTrans

namespace StrongTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between strong natural transformations `η` and `θ` (between oplax functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
/-
**CategoryTheory.Oplax.StrongTrans.Modification** 是 Mathlib 中的一个结构，位于命名空间 `Categ
oryTheory.Oplax.StrongTrans`。
形式化陈述：Modification where /-- The underlying family of 2-morphisms. -/ app (a : B
) : η.app a ⟶ θ.app a /-- The naturality condition. -/ naturality {a b : B} (f :
 a ⟶ b) : F.map f ◁ app b ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ app a 
▷ G.map f
参数：a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification `Γ` between strong natural transformations `η` and `θ` (between o
plax functors)
consists of a family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfi
es the equation
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.ma
p f)`
for each 1-morphism `f : a ⟶ b`.
-/
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality {a b : B} (f : a ⟶ b) :
    F.map f ◁ app b ≫ (θ.naturality f).hom =
      (η.naturality f).hom ≫ app a ▷ G.map f := by cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (Γ : Modification η θ)

set_option backward.defeqAttrib.useBackward true in
/-- The modification between the underlying strong transformations of oplax functors -/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.toOplax** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：toOplax : OplaxTrans.Modification η.toOplax θ.toOplax where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modification between the underlying strong transformations of oplax functors
-/
def toOplax : OplaxTrans.Modification η.toOplax θ.toOplax where
  app a := Γ.app a
/-
**CategoryTheory.Oplax.StrongTrans.Modification.hasCoeToOplax** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：hasCoeToOplax : Coe (Modification η θ) (OplaxTrans.Modification η.toOplax 
θ.toOplax)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToOplax :
    Coe (Modification η θ) (OplaxTrans.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of oplax functors associated to a modification
between the underlying oplax transformations. -/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.mkOfOplax** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：mkOfOplax (Γ : OplaxTrans.Modification η.toOplax θ.toOplax) : Modification
 η θ where app a
参数：Γ : OplaxTrans.Modification η.toOplax θ.toOplax。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modification between strong transformations of oplax functors associated to 
a modification
between the underlying oplax transformations.
-/
def mkOfOplax (Γ : OplaxTrans.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := by simpa using! Γ.naturality f

/-- Modifications between strong transformations of oplax functors are equivalent to modifications
between the underlying oplax transformations. -/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.equivOplax** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：equivOplax : (OplaxTrans.Modification η.toOplax θ.toOplax) ≃ Modification 
η θ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Modifications between strong transformations of oplax functors are equivalent to
 modifications
between the underlying oplax transformations.
-/
def equivOplax : (OplaxTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  toFun := mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.whiskerLeft_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) : f ◁ F.map g ◁ Γ.ap
p c ≫ f ◁ (θ.naturality g).hom = f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map 
g
参数：f : a' ⟶ F.obj b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.Modification.whiskerLeft_naturality`：whi
skerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) : f ◁ F.map g ◁ Γ.app c ≫ f ◁
 θ.naturality g = f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.ma…
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g :=
  OplaxTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.whiskerRight_naturality** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') : F.map f ◁ Γ.app b
 ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g = (α_ _ _ _).inv ≫ (η.naturalit
y f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g
参数：f : a ⟶ b；g : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.Modification.whiskerRight_naturality`：wh
iskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') : F.map f ◁ Γ.app b ▷ g ≫ (
α_ _ _ _).inv ≫ θ.naturality f ▷ g = (α_ _ _ _).inv ≫ η.na…
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g :=
  OplaxTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

end

variable (η) in
/-- The identity modification. -/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.id** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Oplax.StrongTrans.Modification`。
形式化陈述：id : Modification η η where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity modification.
-/
def id : Modification η η where app a := 𝟙 (η.app a)
/-
**CategoryTheory.Oplax.StrongTrans.Modification.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Oplax.StrongTrans.Modification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.Modification.vcomp** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Oplax.StrongTrans.Modification`。
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
/-- Type-alias for modifications between strong transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with strong
transformations. -/
@[ext]
/-
**CategoryTheory.Oplax.StrongTrans.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Oplax.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} → (F ⟶ G) → (F ⟶ G) → Type (max u₁ w₂)
参数：F ⟶ G；F ⟶ G；max u₁ w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type-alias for modifications between strong transformations of oplax functors. T
his is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with s
trong
transformations.
-/
structure Hom where
  of ::
  /-- The underlying modification of strong transformations. -/
  as : Modification η θ

/-- Category structure on the strong natural transformations between oplax functors.

Note that this a scoped instance in the `Oplax.StrongTrans` namespace. -/
@[simps!]
/-
**CategoryTheory.Oplax.StrongTrans.homCategory** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Oplax.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} →           CategoryTheory.Category.{max u₁ w₂, max (max (max 
u₁ v₁) v₂) w₂} (F ⟶ G)
参数：max (max u₁ v₁) v₂；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on the strong natural transformations between oplax functors.

Note that this a scoped instance in the `Oplax.StrongTrans` namespace.
-/
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩
/-
**CategoryTheory.Oplax.StrongTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Op
lax.StrongTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/-
**CategoryTheory.Oplax.StrongTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Oplax.StrongTrans.homCategory`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   {F G : CategoryTheory.OplaxFunctor B C} {η θ :
 F ⟶ G} {m n : η ⟶ θ}, (∀ (b : B), m.as.app b = n.as.app b) → m = n
参数：∀ (b : B), m.as.app b = n.as.app b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.Hom.ext`：∀ {B : Type u₁} {inst : Catego
ryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory C}   {F
 G : CategoryTheory.OplaxFunct…
· 使用定理 `CategoryTheory.Oplax.StrongTrans.Modification.ext`：∀ {B : Type u₁} {inst
 : CategoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategor
y C}   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.as.app b = n.as.app b) : m = n :=
  Hom.ext <| Modification.ext <| funext w

/-- Construct a modification isomorphism between strong natural transformations (of oplax functors)
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Oplax.StrongTrans`。
形式化陈述：isoMk (app : forall a, η.app a ≅ θ.app a) (naturality : forall {a b} (f : 
a ⟶ b), F.map f ◁ (app b).hom ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (a
pp a).hom ▷ G.map f
参数：app : forall a, η.app a ≅ θ.app a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a modification isomorphism between strong natural transformations (of 
oplax functors)
by giving object level isomorphisms, and checking naturality only in the forward
 direction.
-/
def isoMk (app : ∀ a, η.app a ≅ θ.app a)
    (naturality : ∀ {a b} (f : a ⟶ b),
      F.map f ◁ (app b).hom ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _

end StrongTrans

end CategoryTheory.Oplax

