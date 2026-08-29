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

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality` / 定理 `whiskerLeft_naturality`

English:
theorem whiskerLeft_naturality
  given: (f : a' ⟶ F.obj a) (g : a ⟶ b)
  proof: by
  simp_rw [← whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality
  条件: (f : a' ⟶ F.obj a) (g : a ⟶ b)
  证明: by
  simp_rw [← whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]

Depends on / 依赖: naturality, simp_rw, whiskerLeft_comp
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj a) (g : a ⟶ b) :
    f ◁ Γ.app a ▷ G.map g ≫ f ◁ θ.naturality g =
      f ◁ η.naturality g ≫ f ◁ F.map g ◁ Γ.app b := by
  simp_rw [← whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality` / 定理 `whiskerRight_naturality`

English:
theorem whiskerRight_naturality
  given: (f : a ⟶ b) (g : G.obj b ⟶ a')
  proof: by
  simp_rw [← comp_whiskerRight, naturality]

中文:
定理 whiskerRight_naturality
  条件: (f : a ⟶ b) (g : G.obj b ⟶ a')
  证明: by
  simp_rw [← comp_whiskerRight, naturality]

Depends on / 依赖: comp_whiskerRight, naturality, simp_rw
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    Γ.app a ▷ G.map f ▷ g ≫ θ.naturality f ▷ g =
      η.naturality f ▷ g ≫ (F.map f ◁ Γ.app b) ▷ g := by
  simp_rw [← comp_whiskerRight, naturality]

end

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
  签名: 可居 (Modification η η)
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
/-- Type-alias for modifications between lax transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with lax
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
结构 态射
  参数: where
  公理与运算 (2 个):
    - of : :
    - as : Modification η θ
-/
structure Hom where
  of ::
  /-- The underlying modification of lax transformations. -/
  as : Modification η θ

/-- Category structure on the lax natural transformations between oplax functors.

Note that this is a scoped instance in the `Oplax.LaxTrans` namespace. -/
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
  签名: 可居 (η ⟶ η)
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
  given: {m n : η ⟶ θ} (h : forall a, m.as.app a = n.as.app a)
  statement: m = n
  proof: Hom.ext Modification.ext funext h

中文:
引理 homCategory.ext
  条件: {m n : η ⟶ θ} (h : 对任意 a, m.as.app a = n.as.app a)
  结论: m = n
  证明: Hom.ext Modification.ext funext h
-/
lemma homCategory.ext {m n : η ⟶ θ} (h : forall a, m.as.app a = n.as.app a) : m = n :=
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

variable (η θ : F ⟶ G)

/-- A modification `Γ` between oplax natural transformations `η` and `θ` consists of a family of
2-morphisms `Γ.app a : η.app a ⟶ θ.app a`, which satisfies the equation
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

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality` / 定理 `whiskerLeft_naturality`

English:
theorem whiskerLeft_naturality
  given: (f : a' ⟶ F.obj b) (g : b ⟶ c)
  proof: by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality
  条件: (f : a' ⟶ F.obj b) (g : b ⟶ c)
  证明: by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]

Depends on / 依赖: Bicategory, Bicategory.whiskerLeft_comp, naturality, simp_rw, whiskerLeft_comp
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ θ.naturality g =
      f ◁ η.naturality g ≫ f ◁ Γ.app b ▷ G.map g := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality]

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality` / 定理 `whiskerRight_naturality`

English:
theorem whiskerRight_naturality
  given: (f : a ⟶ b) (g : G.obj b ⟶ a')
  proof: by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]

中文:
定理 whiskerRight_naturality
  条件: (f : a ⟶ b) (g : G.obj b ⟶ a')
  证明: by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]

Depends on / 依赖: associator_inv_naturality_middle_assoc, comp_whiskerRight, naturality, simp_rw
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ θ.naturality f ▷ g =
      (α_ _ _ _).inv ≫ η.naturality f ▷ g ≫ Γ.app a ▷ G.map f ▷ g := by
  simp_rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, naturality]

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
  签名: 可居 (Modification η η)
  定义体: ⟨Modification.id η⟩

Depends on / 依赖: IsColimit, IsColimit.equivOfNatIsoOfIso, IsIPCOfShape, IsIPCOfShape.nonempty_isColimit, Modification, Modification.id, equivOfNatIsoOfIso, evaluationCoconePointwiseProductIso, evaluationJointlyReflectsColimits, isColimitOfPreserves, nonempty_isColimit, pointwiseProductCompEvaluation
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
/-- Type-alias for modifications between oplax transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with oplax
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
结构 态射
  参数: where
  公理与运算 (2 个):
    - of : :
    - as : Modification η θ
-/
structure Hom where
  of ::
  /-- The underlying modification of oplax transformations. -/
  as : Modification η θ

/-- Category structure on the oplax natural transformations between OplaxFunctors.

Note that this a scoped instance in the `Oplax.OplaxTrans` namespace. -/
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
  签名: 可居 (η ⟶ η)
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
    (naturality :
      forall {a b} (f : a ⟶ b),
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
/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: : OplaxTrans.Modification η.toOplax θ.toOplax where
  body: Γ.app a

中文:
定义 toOplax
  签名: : OplaxTrans.Modification η.toOplax θ.toOplax where
  定义体: Γ.app a

Depends on / 依赖: IsRightAdjoint, final_of_isRightAdjoint
-/
def toOplax : OplaxTrans.Modification η.toOplax θ.toOplax where
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

Depends on / 依赖: Initial, IsLeftAdjoint, initial_of_isLeftAdjoint, toOplax
-/
instance hasCoeToOplax :
    Coe (Modification η θ) (OplaxTrans.Modification η.toOplax θ.toOplax) :=
  ⟨toOplax⟩

/-- The modification between strong transformations of oplax functors associated to a modification
between the underlying oplax transformations. -/
@[simps]
/--
Definition of `mkOfOplax` / `mkOfOplax` 的定义

English:
definition mkOfOplax
  signature: (Γ : OplaxTrans.Modification η.toOplax θ.toOplax)
  body: Γ.app a
  naturality f := by simpa using! Γ.naturality f

中文:
定义 mkOfOplax
  签名: (Γ : OplaxTrans.Modification η.toOplax θ.toOplax)
  定义体: Γ.app a
  naturality f := by simpa using! Γ.naturality f
-/
def mkOfOplax (Γ : OplaxTrans.Modification η.toOplax θ.toOplax) : Modification η θ where
  app a := Γ.app a
  naturality f := by simpa using! Γ.naturality f

/-- Modifications between strong transformations of oplax functors are equivalent to modifications
between the underlying oplax transformations. -/
@[simps]
/--
Definition of `equivOplax` / `equivOplax` 的定义

English:
definition equivOplax
  signature: : (OplaxTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  body: mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equivOplax
  签名: : (OplaxTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  定义体: mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: mkOfOplax
-/
def equivOplax : (OplaxTrans.Modification η.toOplax θ.toOplax) ≃ Modification η θ where
  toFun := mkOfOplax
  invFun := toOplax
  left_inv _ := rfl
  right_inv _ := rfl

section

variable (Γ : Modification η θ) {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality` / 定理 `whiskerLeft_naturality`

English:
theorem whiskerLeft_naturality
  given: (f : a' ⟶ F.obj b) (g : b ⟶ c)
  proof: OplaxTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality
  条件: (f : a' ⟶ F.obj b) (g : b ⟶ c)
  证明: OplaxTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Modification, OplaxTrans, OplaxTrans.Modification.whiskerLeft_naturality, toOplax, whiskerLeft_naturality
-/
theorem whiskerLeft_naturality (f : a' ⟶ F.obj b) (g : b ⟶ c) :
    f ◁ F.map g ◁ Γ.app c ≫ f ◁ (θ.naturality g).hom =
      f ◁ (η.naturality g).hom ≫ f ◁ Γ.app b ▷ G.map g :=
  OplaxTrans.Modification.whiskerLeft_naturality Γ.toOplax _ _

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality` / 定理 `whiskerRight_naturality`

English:
theorem whiskerRight_naturality
  given: (f : a ⟶ b) (g : G.obj b ⟶ a')
  proof: OplaxTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

中文:
定理 whiskerRight_naturality
  条件: (f : a ⟶ b) (g : G.obj b ⟶ a')
  证明: OplaxTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

Depends on / 依赖: Modification, OplaxTrans, OplaxTrans.Modification.whiskerRight_naturality, toOplax, whiskerRight_naturality
-/
theorem whiskerRight_naturality (f : a ⟶ b) (g : G.obj b ⟶ a') :
    F.map f ◁ Γ.app b ▷ g ≫ (α_ _ _ _).inv ≫ (θ.naturality f).hom ▷ g =
      (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ g ≫ Γ.app a ▷ G.map f ▷ g :=
  OplaxTrans.Modification.whiskerRight_naturality Γ.toOplax _ _

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

Depends on / 依赖: IsConnected, IsConnected.is_nonempty, is_nonempty
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
  签名: 可居 (Modification η η)
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
/-- Type-alias for modifications between strong transformations of oplax functors. This is the type
used for the 2-homomorphisms in the bicategory of oplax functors equipped with strong
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
结构 态射
  参数: where
  公理与运算 (2 个):
    - of : :
    - as : Modification η θ
-/
structure Hom where
  of ::
  /-- The underlying modification of strong transformations. -/
  as : Modification η θ

/-- Category structure on the strong natural transformations between oplax functors.

Note that this a scoped instance in the `Oplax.StrongTrans` namespace. -/
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
  签名: 可居 (η ⟶ η)
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

/-- Construct a modification isomorphism between strong natural transformations (of oplax functors)
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

end CategoryTheory.Oplax
