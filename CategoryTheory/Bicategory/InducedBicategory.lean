/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!

# Induced bicategories

In this file we develop API for constructing a full sub-bicategory of a bicategory `C`, given a
map `F : B → C`. The objects of the induced bicategory are the objects of `B`, while the
1-morphisms and 2-morphisms are taken as all corresponding morphisms in `C`.

## TODO

One might also want to develop "locally induced" bicategories, which should allow for a sub-class
of 1-morphisms as well. However, this needs more thought. If one tries the naive approach of simply
replacing the map `F` below with a "functor" (between `CategoryStruct`s), one runs into the issue
that `map_comp` and `map_id` might not be definitional equalities (which they should be in
practice). Hence one needs to carefully carry these around, or specify `F` in a way that ensures
they are def-eqs, perhaps constructing it from specified `MorphismProperty`s.
-/

@[expose] public section

namespace CategoryTheory.Bicategory

variable {B : Type*} (C : Type*) [Bicategory C] (F : B -> C)

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`. This is given
a bicategory structure where the 1-morphisms `X ⟶ Y` are the 1-morphisms in `C` from `F X` to
`F Y`, and the 2-morphisms `f ⟶ g` are also the 2-morphisms in `C` from `f` to `g`.
-/
@[nolint unusedArguments]
/--
Definition of `InducedBicategory` / `InducedBicategory` 的定义

English:
definition InducedBicategory
  signature: (_F : B -> C)
  body: B

中文:
定义 InducedBicategory
  签名: (_F : B -> C)
  定义体: B
-/
def InducedBicategory (_F : B -> C) :=
  B

namespace InducedBicategory

variable {C F}

/--
Instance `hasCoeToSort` / 实例 `hasCoeToSort`

English:
instance hasCoeToSort
  signature: {α : Sort*} [CoeSort C α]
  body: ⟨fun c => F c⟩

中文:
实例 hasCoeToSort
  签名: {α : Sort*} [CoeSort C α]
  定义体: ⟨fun c => F c⟩
-/
instance hasCoeToSort {α : Sort*} [CoeSort C α] : CoeSort (InducedBicategory C F) α :=
  ⟨fun c => F c⟩

/-- `InducedBicategory.Hom X Y` is a type-alias for morphisms between `X Y : B` viewed as objects
of `B` with the induced bicategory structure. This is given a `CategoryStruct` instance below,
where the identity and composition is induced from `C`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : InducedBicategory C F)
  axioms and operations (2):
    - private(mk) : :
    - hom : F X ⟶ F Y

中文:
结构 Hom
  参数: (X Y : InducedBicategory C F)
  公理与运算 (2 个):
    - private(mk) : :
    - hom : F X ⟶ F Y
-/
structure Hom (X Y : InducedBicategory C F) where
  private mk ::
  /-- The morphism in `C` underlying the morphism in `InducedBicategory C F`. -/
  hom : F X ⟶ F Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simps id_hom comp_hom]
/--
Instance `categoryStruct` / 实例 `categoryStruct`

English:
instance categoryStruct
  signature: : CategoryStruct (InducedBicategory C F) where
  body: Hom X Y
  id X := ⟨𝟙 (F X)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

中文:
实例 categoryStruct
  签名: : CategoryStruct (InducedBicategory C F) where
  定义体: Hom X Y
  id X := ⟨𝟙 (F X)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩
-/
instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `mkHom` / `mkHom` 的定义

English:
abbreviation mkHom
  signature: {X Y : InducedBicategory C F} (f : F X ⟶ F Y)
  body: ⟨f⟩

@[ext]

中文:
缩写 mkHom
  签名: {X Y : InducedBicategory C F} (f : F X ⟶ F Y)
  定义体: ⟨f⟩

@[ext]
-/
abbrev mkHom {X Y : InducedBicategory C F} (f : F X ⟶ F Y) : X ⟶ Y :=
  ⟨f⟩

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- `InducedBicategory.Hom₂ f g` is a type-alias for 2-morphisms between `f g : X ⟶ Y`, where
`f` and `g` are 1-morphisms for the induced bicategory structure on `B`.

This is given a `Category` instance below, induced from the corresponding one in `C`. -/
@[ext]
/--
Definition of `Hom₂` / `Hom₂` 的定义

English:
structure Hom₂
  parameters: {X Y : InducedBicategory C F} (f g : X ⟶ Y)
  axioms and operations (1):
    - hom : f.hom ⟶ g.hom

中文:
结构 Hom₂
  参数: {X Y : InducedBicategory C F} (f g : X ⟶ Y)
  公理与运算 (1 个):
    - hom : f.hom ⟶ g.hom
-/
structure Hom₂ {X Y : InducedBicategory C F} (f g : X ⟶ Y) where
  /-- The 2-morphism in `C` underlying the 2-morphism in `InducedBicategory C F`. -/
  hom : f.hom ⟶ g.hom

@[simps!]
/--
Instance `Hom.category` / 实例 `Hom.category`

English:
instance Hom.category
  signature: (X Y : InducedBicategory C F)
  body: Hom₂ f g
  id f := ⟨𝟙 f.hom⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[ext]

中文:
实例 Hom.category
  签名: (X Y : InducedBicategory C F)
  定义体: Hom₂ f g
  id f := ⟨𝟙 f.hom⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[ext]
-/
instance Hom.category (X Y : InducedBicategory C F) : Category (X ⟶ Y) where
  Hom f g := Hom₂ f g
  id f := ⟨𝟙 f.hom⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[ext]
/--
lemma `hom₂_ext` / 引理 `hom₂_ext`

English:
lemma hom₂_ext
  given: {X Y : InducedBicategory C F} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom)
  proof: Hom₂.ext h

中文:
引理 hom₂_ext
  条件: {X Y : InducedBicategory C F} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom)
  证明: Hom₂.ext h
-/
lemma hom₂_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom) :
    η = θ :=
  Hom₂.ext h

/--
Definition of `mkHom₂` / `mkHom₂` 的定义

English:
abbreviation mkHom₂
  signature: {a b : InducedBicategory C F} {f g : F a ⟶ F b} (η : f ⟶ g)
  body: Hom₂.mk η

中文:
缩写 mkHom₂
  签名: {a b : InducedBicategory C F} {f g : F a ⟶ F b} (η : f ⟶ g)
  定义体: Hom₂.mk η
-/
abbrev mkHom₂ {a b : InducedBicategory C F} {f g : F a ⟶ F b} (η : f ⟶ g) : mkHom f ⟶ mkHom g :=
  Hom₂.mk η

/-- Constructor for 2-isomorphisms in the induced bicategory. -/
@[simps!]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom)
  body: ⟨φ.hom⟩
  inv := ⟨φ.inv⟩

@[simps!]

中文:
定义 isoMk
  签名: {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom)
  定义体: ⟨φ.hom⟩
  inv := ⟨φ.inv⟩

@[simps!]
-/
def isoMk {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom) : f ≅ g where
  hom := ⟨φ.hom⟩
  inv := ⟨φ.inv⟩

@[simps!]
/--
Instance `bicategory` / 实例 `bicategory`

English:
instance bicategory
  signature: : Bicategory (InducedBicategory C F) where
  body: mkHom₂ h.hom ◁ Hom₂.hom η
whiskerRight {_ _ _} {_ _} η h := mkHom₂ (Hom₂.hom η) ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (fun_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange {_ _ _ _ _ _ _} η θ := by ext; simpa using whisker_exchange _ _

中文:
实例 bicategory
  签名: : Bicategory (InducedBicategory C F) where
  定义体: mkHom₂ h.hom ◁ Hom₂.hom η
whiskerRight {_ _ _} {_ _} η h := mkHom₂ (Hom₂.hom η) ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (fun_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange {_ _ _ _ _ _ _} η θ := by ext; simpa using whisker_exchange _ _

Depends on / 依赖: h.hom
-/
instance bicategory : Bicategory (InducedBicategory C F) where
whiskerLeft {_ _ _} h {_ _} η := mkHom₂ h.hom ◁ Hom₂.hom η
whiskerRight {_ _ _} {_ _} η h := mkHom₂ (Hom₂.hom η) ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (fun_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange {_ _ _ _ _ _ _} η θ := by ext; simpa using whisker_exchange _ _

attribute [-simp] bicategory_comp_hom bicategory_Hom

section

/-- The forgetful (strict) pseudofunctor from an induced bicategory to the original bicategory,
forgetting the extra data.
-/
@[simps!]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : StrictPseudofunctor (InducedBicategory C F) C
  body: StrictPseudofunctor.mk' {
    obj X := F X
    map f := f.hom
    map₂ η := η.hom }

中文:
定义 forget
  签名: : StrictPseudofunctor (InducedBicategory C F) C
  定义体: StrictPseudofunctor.mk' {
    obj X := F X
    map f := f.hom
    map₂ η := η.hom }

Depends on / 依赖: StrictPseudofunctor, StrictPseudofunctor.mk, f.hom
-/
def forget : StrictPseudofunctor (InducedBicategory C F) C :=
  StrictPseudofunctor.mk' {
    obj X := F X
    map f := f.hom
    map₂ η := η.hom }

end

section

@[simp]
/--
lemma `eqToHom_hom` / 引理 `eqToHom_hom`

English:
lemma eqToHom_hom
  given: {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f = g)
  proof: by
  subst h; simp only [eqToHom_refl, Hom.category_id_hom]

@[simp]

中文:
引理 eqToHom_hom
  条件: {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f = g)
  证明: by
  subst h; simp only [eqToHom_refl, Hom.category_id_hom]

@[simp]

Depends on / 依赖: Hom.category_id_hom, category_id_hom, eqToHom_refl
-/
lemma eqToHom_hom {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom h).hom = eqToHom (h ▸ rfl) := by
  subst h; simp only [eqToHom_refl, Hom.category_id_hom]

@[simp]
/--
lemma `mkHom_eqToHom` / 引理 `mkHom_eqToHom`

English:
lemma mkHom_eqToHom
  given: {X Y : InducedBicategory C F} {f g : F X ⟶ F Y} (h : f = g)
  proof: by
  ext; subst h; simp only [eqToHom_refl, Hom.category_id_hom]

中文:
引理 mkHom_eqToHom
  条件: {X Y : InducedBicategory C F} {f g : F X ⟶ F Y} (h : f = g)
  证明: by
  ext; subst h; simp only [eqToHom_refl, Hom.category_id_hom]

Depends on / 依赖: Hom.category_id_hom, category_id_hom, eqToHom_refl
-/
lemma mkHom_eqToHom {X Y : InducedBicategory C F} {f g : F X ⟶ F Y} (h : f = g) :
    mkHom₂ (eqToHom h) = eqToHom (h ▸ rfl) := by
  ext; subst h; simp only [eqToHom_refl, Hom.category_id_hom]

variable [Strict C]

attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Strict (InducedBicategory C F)

中文:
实例 :
  签名: Strict (InducedBicategory C F)
-/
instance : Strict (InducedBicategory C F) where

end

end InducedBicategory

end CategoryTheory.Bicategory
