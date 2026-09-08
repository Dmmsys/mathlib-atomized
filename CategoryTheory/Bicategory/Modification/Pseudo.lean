/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Modification.Oplax

/-!
# Modifications between transformations of pseudofunctors

In this file we define modifications of strong transformations of pseudofunctors. They are defined
similarly to modifications of transformations of oplax functors.

## Main definitions

Given two pseudofunctors `F` and `G`, we define:

* `Pseudofunctor.StrongTrans.Modification η θ` : modifications between strong transformations
  `η` and `θ` (between `F` and `G`).
* `Pseudofunctor.StrongTrans.homCategory F G` : the category structure on strong transformations
  between `F` and `G`, where the morphisms are modifications, and composition is given by vertical
  composition of modifications. Note that this a scoped instance in the `Pseudofunctor.StrongTrans`
  namespace, so you need to run `open scoped Pseudofunctor.StrongTrans` to access it.

-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : Pseudofunctor B C}

namespace StrongTrans

variable (η θ : F ⟶ G)

/-- A modification `Γ` between strong transformations (of pseudofunctors) `η` and `θ` consists of a
family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.map f)`
for each 1-morphism `f : a ⟶ b`.
-/
@[ext]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification** 是 Mathlib 中的一个结构，位于命名空
间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：Modification where /-- The underlying family of 2-morphism. -/ app (a : B)
 : η.app a ⟶ θ.app a /-- The naturality condition. -/ naturality {a b : B} (f : 
a ⟶ b) : F.map f ◁ app b ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ app a ▷
 G.map f
参数：a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification `Γ` between strong transformations (of pseudofunctors) `η` and `θ
` consists of a
family of 2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equatio
n
`(F.map f ◁ app b) ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a ▷ G.ma
p f)`
for each 1-morphism `f : a ⟶ b`.
-/
structure Modification where
  /-- The underlying family of 2-morphism. -/
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
set_option backward.isDefEq.respectTransparency false in
/-- The modification between the corresponding strong transformation of the underlying oplax
functors. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.toOplax** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
形式化陈述：toOplax : Oplax.StrongTrans.Modification η.toOplax θ.toOplax where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modification between the corresponding strong transformation of the underlyi
ng oplax
functors.
-/
def toOplax : Oplax.StrongTrans.Modification η.toOplax θ.toOplax where
  app a := Γ.app a
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.hasCoeToOplax** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
形式化陈述：hasCoeToOplax : Coe (Modification η θ) (Oplax.StrongTrans.Modification η.t
oOplax θ.toOplax)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToOplax :
    Coe (Modification η θ) (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of pseudofunctors associated to a modification
between the underlying strong transformations of oplax functors. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.mkOfOplax** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
形式化陈述：mkOfOplax (Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax) : Modif
ication η θ where app a
参数：Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modification between strong transformations of pseudofunctors associated to 
a modification
between the underlying strong transformations of oplax functors.
-/
def mkOfOplax (Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := Γ.naturality f

/-- Modifications between strong transformations of pseudofunctors are equivalent to modifications
between the underlying strong transformations of oplax functors. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.equivOplax** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
形式化陈述：equivOplax : (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) ≃ Modifi
cation η θ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Modifications between strong transformations of pseudofunctors are equivalent to
 modifications
between the underlying strong transformations of oplax functors.
-/
def equivOplax : (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  toFun := mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.whiskerLeft_naturality**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`
。
形式化陈述：whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) : f ◁ F.map g ◁ Γ.ap
p c ≫ f ◁ (θ.naturality g).hom = f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map 
g
参数：f : a' ⟶ F.obj b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.Modification.whiskerLeft_naturality`：wh
iskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) : f ◁ F.map g ◁ Γ.app c ≫ f 
◁ (θ.naturality g).hom = f ◁ (η.naturality g).hom ≫ f ◁ Γ.…
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g :=
  Oplax.StrongTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.whiskerRight_naturality*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification
`。
形式化陈述：whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') : F.map f ◁ Γ.app b
 ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g = (α_ _ _ _).inv ≫ (η.naturalit
y f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g
参数：f : a ⟶ b；g : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.Modification.whiskerRight_naturality`：w
hiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') : F.map f ◁ Γ.app b ▷ g ≫ 
(α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g = (α_ _ _ _).inv …
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g :=
  Oplax.StrongTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

end

variable (η) in
/-- The identity modification. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.id** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
形式化陈述：id : Modification η η where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity modification.
-/
def id : Modification η η where app a := 𝟙 (η.app a)
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Modification.vcomp** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.Modification`。
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
/-- Type-alias for modifications between strong transformations of pseudofunctors. This is the type
used for the 2-homomorphisms in the bicategory of pseudofunctors. -/
@[ext]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
Pseudofunctor B C} → (F ⟶ G) → (F ⟶ G) → Type (max u₁ w₂)
参数：F ⟶ G；F ⟶ G；max u₁ w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type-alias for modifications between strong transformations of pseudofunctors. T
his is the type
used for the 2-homomorphisms in the bicategory of pseudofunctors.
-/
structure Hom where
  of ::
  /-- The underlying modification of strong transformations. -/
  as : Modification η θ

/-- Category structure on the strong transformations between pseudofunctors.

Note that this a scoped instance in the `Pseudofunctor.StrongTrans` namespace. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.homCategory** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
Pseudofunctor B C} →           CategoryTheory.Category.{max u₁ w₂, max (max (max
 u₁ v₁) v₂) w₂} (F ⟶ G)
参数：max (max u₁ v₁) v₂；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category structure on the strong transformations between pseudofunctors.

Note that this a scoped instance in the `Pseudofunctor.StrongTrans` namespace.
-/
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩
/-
**CategoryTheory.Pseudofunctor.StrongTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.StrongTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.homCategory.ext** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Pseudofunctor.StrongTrans.homCategory`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   {F G : CategoryTheory.Pseudofunctor B C} {η θ 
: F ⟶ G} {m n : η ⟶ θ}, (∀ (b : B), m.as.app b = n.as.app b) → m = n
参数：∀ (b : B), m.as.app b = n.as.app b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.StrongTrans.Hom.ext`：∀ {B : Type u₁} {inst 
: CategoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.Bicategory
 C}   {F G : CategoryTheory.Pseudofunc…
· 使用定理 `CategoryTheory.Pseudofunctor.StrongTrans.Modification.ext`：∀ {B : Type u
₁} {inst : CategoryTheory.Bicategory B} {C : Type u₂} {inst_1 : CategoryTheory.B
icategory C}   {F G : CategoryTheory.Pseudofunc…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma homCategory.ext {m n : η ⟶ θ} (w : ∀ b, m.as.app b = n.as.app b) : m = n :=
  Hom.ext <| Modification.ext <| funext w

/-- Construct a modification isomorphism between strong transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：isoMk (app : forall a, η.app a ≅ θ.app a) (naturality : forall {a b} (f : 
a ⟶ b), F.map f ◁ (app b).hom ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (a
pp a).hom ▷ G.map f
参数：app : forall a, η.app a ≅ θ.app a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a modification isomorphism between strong transformations
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

end CategoryTheory.Pseudofunctor

