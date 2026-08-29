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
/--
Definition of `Modification` / `Modification` 的定义

English:
structure Modification
  parameters: where
  axioms and operations (2):
    - app((a : B)) : η.app a ⟶ θ.app a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ◁ app b ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ app a ▷ G.map f  [default: by cat_disch]

中文:
结构 Modification
  参数: where
  公理与运算 (2 个):
    - app((a : B)) : η.app a ⟶ θ.app a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ◁ app b ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ app a ▷ G.map f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: : Oplax.StrongTrans.Modification η.toOplax θ.toOplax where
  body: Γ.app a

中文:
定义 toOplax
  签名: : Oplax.StrongTrans.Modification η.toOplax θ.toOplax where
  定义体: Γ.app a
-/
def toOplax : Oplax.StrongTrans.Modification η.toOplax θ.toOplax where
  app a := Γ.app a

/--
Instance `hasCoeToOplax` / 实例 `hasCoeToOplax`

English:
instance hasCoeToOplax
  signature: :
  body: ⟨toOplax⟩

中文:
实例 hasCoeToOplax
  签名: :
  定义体: ⟨toOplax⟩

Depends on / 依赖: toOplax
-/
instance hasCoeToOplax :
    Coe (Modification η θ) (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of pseudofunctors associated to a modification
between the underlying strong transformations of oplax functors. -/
@[simps]
/--
Definition of `mkOfOplax` / `mkOfOplax` 的定义

English:
definition mkOfOplax
  signature: (Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax)
  body: Γ.app a
  naturality f := Γ.naturality f

中文:
定义 mkOfOplax
  签名: (Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax)
  定义体: Γ.app a
  naturality f := Γ.naturality f
-/
def mkOfOplax (Γ : Oplax.StrongTrans.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := Γ.naturality f

/-- Modifications between strong transformations of pseudofunctors are equivalent to modifications
between the underlying strong transformations of oplax functors. -/
@[simps]
/--
Definition of `equivOplax` / `equivOplax` 的定义

English:
definition equivOplax
  signature: : (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  body: mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equivOplax
  签名: : (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  定义体: mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: HasColimit, comp_hasColimit, mkOfOplax
-/
def equivOplax : (Oplax.StrongTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  toFun := mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality` / 定理 `whiskerLeft_naturality`

English:
theorem whiskerLeft_naturality
  given: (f : a' ⟶ F.obj b) (g : b ⟶ c)
  proof: Oplax.StrongTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality
  条件: (f : a' ⟶ F.obj b) (g : b ⟶ c)
  证明: Oplax.StrongTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Modification, Oplax.StrongTrans.Modification.whiskerLeft_naturality, StrongTrans, comp_preservesColimit, toOplax, whiskerLeft_naturality
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g :=
  Oplax.StrongTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality` / 定理 `whiskerRight_naturality`

English:
theorem whiskerRight_naturality
  given: (f : a ⟶ b) (g : G.obj b ⟶ a')
  proof: Oplax.StrongTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

中文:
定理 whiskerRight_naturality
  条件: (f : a ⟶ b) (g : G.obj b ⟶ a')
  证明: Oplax.StrongTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

Depends on / 依赖: Category, Modification, Oplax.StrongTrans.Modification.whiskerRight_naturality, StrongTrans, comp_reflectsColimit, toOplax, whiskerRight_naturality
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g :=
  Oplax.StrongTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

end

variable (η) in
/-- The identity modification. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Modification η η where app a
  body: 𝟙 (η.app a)

中文:
定义 id
  签名: : Modification η η where app a
  定义体: 𝟙 (η.app a)

Depends on / 依赖: Category, compCreatesColimit
-/
def id : Modification η η where app a := 𝟙 (η.app a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Modification η η)
  body: ⟨Modification.id η⟩

中文:
实例 :
  签名: Inhabited (Modification η η)
  定义体: ⟨Modification.id η⟩

Depends on / 依赖: Modification, Modification.id
-/
instance : Inhabited (Modification η η) :=
  ⟨Modification.id η⟩

/-- Vertical composition of modifications. -/
@[simps]
/--
Definition of `vcomp` / `vcomp` 的定义

English:
definition vcomp
  signature: {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι)
  body: Γ.app a ≫ Δ.app a

中文:
定义 vcomp
  签名: {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι)
  定义体: Γ.app a ≫ Δ.app a
-/
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) : Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between strong transformations of pseudofunctors. This is the type
used for the 2-homomorphisms in the bicategory of pseudofunctors. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (2):
    - of : :
    - as : Modification η θ

中文:
结构 Hom
  参数: where
  公理与运算 (2 个):
    - of : :
    - as : Modification η θ
-/
structure Hom where
  of ::
  /-- The underlying modification of strong transformations. -/
  as : Modification η θ

/-- Category structure on the strong transformations between pseudofunctors.

Note that this a scoped instance in the `Pseudofunctor.StrongTrans` namespace. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id Γ := ⟨Modification.id Γ⟩
  comp Γ Δ := ⟨Modification.vcomp Γ.as Δ.as⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (η ⟶ η)
  body: ⟨𝟙 η⟩

@[ext]

中文:
实例 :
  签名: Inhabited (η ⟶ η)
  定义体: ⟨𝟙 η⟩

@[ext]
-/
instance : Inhabited (η ⟶ η) :=
  ⟨𝟙 η⟩

@[ext]
/--
lemma `homCategory.ext` / 引理 `homCategory.ext`

English:
lemma homCategory.ext
  given: {m n : η ⟶ θ} (w : forall b, m.as.app b = n.as.app b)
  statement: m = n
  proof: Hom.ext Modification.ext funext w

中文:
引理 homCategory.ext
  条件: {m n : η ⟶ θ} (w : 对任意 b, m.as.app b = n.as.app b)
  结论: m = n
  证明: Hom.ext Modification.ext funext w
-/
lemma homCategory.ext {m n : η ⟶ θ} (w : forall b, m.as.app b = n.as.app b) : m = n :=
Hom.ext Modification.ext funext w

/-- Construct a modification isomorphism between strong transformations
by giving object level isomorphisms, and checking naturality only in the forward direction.
-/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (app : forall a, η.app a ≅ θ.app a)
  body: (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _

中文:
定义 isoMk
  签名: (app : 对任意 a, η.app a ≅ θ.app a)
  定义体: (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _

Depends on / 依赖: cat_disch, hom.as.app, inv.as.app, inv.as.naturality, naturality
-/
def isoMk (app : forall a, η.app a ≅ θ.app a)
    (naturality : forall {a b} (f : a ⟶ b),
      F.map f ◁ (app b).hom ≫ (θ.naturality f).hom =
        (η.naturality f).hom ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using _ ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ _

end StrongTrans

end CategoryTheory.Pseudofunctor
