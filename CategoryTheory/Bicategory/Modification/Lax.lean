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
/--
Definition of `Modification` / `Modification` 的定义

English:
structure Modification
  parameters: where
  axioms and operations (2):
    - app((a : B)) : η.app a ⟶ θ.app a
    - naturality : forall {a b : B} (f : a ⟶ b), app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b  [default: by cat_disch]

中文:
结构 Modification
  参数: where
  公理与运算 (2 个):
    - app((a : B)) : η.app a ⟶ θ.app a
    - naturality : 对任意 {a b : B} (f : a ⟶ b), app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    forall {a b : B} (f : a ⟶ b),
      app a ▷ G.map f ≫ θ.naturality f = η.naturality f ≫ F.map f ◁ app b := by
    cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (η) in
/-- The identity modification. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Modification η η where
  body: 𝟙 (η.app a)

中文:
定义 id
  签名: : Modification η η where
  定义体: 𝟙 (η.app a)
-/
def id : Modification η η where
  app a := 𝟙 (η.app a)

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
/-- Type-alias for modifications between lax transformations of lax functors. This is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with lax
transformations. -/
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
  /-- The underlying modification of lax transformations. -/
  as : Modification η θ

/-- Category structure on the lax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.LaxTrans` namespace. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
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
  given: {Γ Δ : η ⟶ θ} (h : forall a, Γ.as.app a = Δ.as.app a)
  statement: Γ = Δ
  proof: Hom.ext Modification.ext funext h

中文:
引理 homCategory.ext
  条件: {Γ Δ : η ⟶ θ} (h : 对任意 a, Γ.as.app a = Δ.as.app a)
  结论: Γ = Δ
  证明: Hom.ext Modification.ext funext h

Depends on / 依赖: Hom.ext, Modification, Modification.ext
-/
lemma homCategory.ext {Γ Δ : η ⟶ θ} (h : forall a, Γ.as.app a = Δ.as.app a) : Γ = Δ :=
Hom.ext Modification.ext funext h

/-- Construct a modification isomorphism between lax natural transformations
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
    simpa using (app a).inv ▷ G.map f ≫= (naturality f).symm =≫ F.map f ◁ (app b).inv

中文:
定义 isoMk
  签名: (app : 对任意 a, η.app a ≅ θ.app a)
  定义体: (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using (app a).inv ▷ G.map f ≫= (naturality f).symm =≫ F.map f ◁ (app b).inv

Depends on / 依赖: F.map, G.map, cat_disch, hom.as.app, inv.as.app, inv.as.naturality, naturality
-/
def isoMk (app : forall a, η.app a ≅ θ.app a)
    (naturality :
      forall {a b} (f : a ⟶ b),
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
/--
Definition of `Modification` / `Modification` 的定义

English:
structure Modification
  parameters: where
  axioms and operations (2):
    - app((a : B)) : η.app a ⟶ θ.app a
    - naturality : forall {a b : B} (f : a ⟶ b), F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f  [default: by cat_disch]

中文:
结构 Modification
  参数: where
  公理与运算 (2 个):
    - app((a : B)) : η.app a ⟶ θ.app a
    - naturality : 对任意 {a b : B} (f : a ⟶ b), F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Modification where
  /-- The underlying family of 2-morphisms. -/
  app (a : B) : η.app a ⟶ θ.app a
  /-- The naturality condition. -/
  naturality :
    forall {a b : B} (f : a ⟶ b),
      F.map f ◁ app b ≫ θ.naturality f = η.naturality f ≫ app a ▷ G.map f := by
    cat_disch

attribute [reassoc (attr := simp)] Modification.naturality

variable {η θ}

namespace Modification

variable (η) in
/-- The identity modification. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Modification η η where
  body: 𝟙 (η.app a)

中文:
定义 id
  签名: : Modification η η where
  定义体: 𝟙 (η.app a)
-/
def id : Modification η η where
  app a := 𝟙 (η.app a)

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
def vcomp {ι : F ⟶ G} (Γ : Modification η θ) (Δ : Modification θ ι) :
    Modification η ι where
  app a := Γ.app a ≫ Δ.app a

end Modification

variable (η θ) in
/-- Type-alias for modifications between oplax transformations of lax functors. This is the type
used for the 2-homomorphisms in the bicategory of lax functors equipped with oplax
transformations. -/
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
  /-- The underlying modification of oplax transformations. -/
  as : Modification η θ

/-- Category structure on the oplax natural transformations between lax functors.

Note that this is a scoped instance in the `Lax.OplaxTrans` namespace. -/
@[simps!]
scoped instance homCategory : Category (F ⟶ G) where
  Hom := Hom
  id η := ⟨Modification.id η⟩
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
  given: {Γ Δ : η ⟶ θ} (h : forall a, Γ.as.app a = Δ.as.app a)
  statement: Γ = Δ
  proof: Hom.ext Modification.ext funext h

中文:
引理 homCategory.ext
  条件: {Γ Δ : η ⟶ θ} (h : 对任意 a, Γ.as.app a = Δ.as.app a)
  结论: Γ = Δ
  证明: Hom.ext Modification.ext funext h
-/
lemma homCategory.ext {Γ Δ : η ⟶ θ} (h : forall a, Γ.as.app a = Δ.as.app a) : Γ = Δ :=
Hom.ext Modification.ext funext h

/-- Construct a modification isomorphism between oplax natural transformations
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
    simpa using F.map f ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ G.map f

中文:
定义 isoMk
  签名: (app : 对任意 a, η.app a ≅ θ.app a)
  定义体: (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using F.map f ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ G.map f

Depends on / 依赖: F.map, G.map, cat_disch, hom.as.app, inv.as.app, inv.as.naturality, naturality
-/
def isoMk (app : forall a, η.app a ≅ θ.app a)
    (naturality :
      forall {a b} (f : a ⟶ b),
        F.map f ◁ (app b).hom ≫ θ.naturality f =
          η.naturality f ≫ (app a).hom ▷ G.map f := by cat_disch) :
    η ≅ θ where
  hom.as.app a := (app a).hom
  inv.as.app a := (app a).inv
  inv.as.naturality {a b} f := by
    simpa using F.map f ◁ (app b).inv ≫= (naturality f).symm =≫ (app a).inv ▷ G.map f

end OplaxTrans

end CategoryTheory.Lax
