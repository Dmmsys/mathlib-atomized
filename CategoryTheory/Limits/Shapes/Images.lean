/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main definitions

* A `MonoFactorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism
* `IsImage F` means that a given mono factorisation `F` has the universal property of the image.
* `HasImage f` means that there is some image factorization for the morphism `f : X ⟶ Y`.
  * In this case, `image f` is some image object (selected with choice), `image.ι f : image f ⟶ Y`
    is the monomorphism `m` of the factorisation and `factorThruImage f : X ⟶ image f` is the
    morphism `e`.
* `HasImages C` means that every morphism in `C` has an image.
* Let `f : X ⟶ Y` and `g : P ⟶ Q` be morphisms in `C`, which we will represent as objects of the
  arrow category `Arrow C`. Then `sq : f ⟶ g` is a commutative square in `C`. If `f` and `g` have
  images, then `HasImageMap sq` represents the fact that there is a morphism
  `i : image f ⟶ image g` making the diagram

  X ----→ image f ----→ Y
  | | |
  | | |
  ↓ ↓ ↓
  P ----→ image g ----→ Q

  commute, where the top row is the image factorisation of `f`, the bottom row is the image
  factorisation of `g`, and the outer rectangle is the commutative square `sq`.
* If a category `HasImages`, then `HasImageMaps` means that every commutative square admits an
  image map.
* If a category `HasImages`, then `HasStrongEpiImages` means that the morphism to the image is
  always a strong epimorphism.

## Main statements

* When `C` has equalizers, the morphism `e` appearing in an image factorisation is an epimorphism.
* When `C` has strong epi images, then these images admit image maps.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing work in the group theory and ring theory libraries.

-/

@[expose] public section


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)

/--
Definition of `MonoFactorisation` / `MonoFactorisation` 的定义

English:
structure MonoFactorisation
  parameters: (f : X ⟶ Y)
  axioms and operations (5):
    - I : C
    - m : I ⟶ Y
    - [m_mono : Mono m]
    - e : X ⟶ I
    - fac : e ≫ m = f  [default: by cat_disch]

中文:
结构 单态射分解
  参数: (f : X ⟶ Y)
  公理与运算 (5 个):
    - I : C
    - m : I ⟶ Y
    - [m_mono : 单态射 m]
    - e : X ⟶ I
    - fac : e ≫ m = f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure MonoFactorisation (f : X ⟶ Y) where
  I : C
  m : I ⟶ Y
  [m_mono : Mono m]
  e : X ⟶ I
  fac : e ≫ m = f := by cat_disch

attribute [inherit_doc MonoFactorisation] MonoFactorisation.I MonoFactorisation.m
  MonoFactorisation.m_mono MonoFactorisation.e MonoFactorisation.fac

attribute [reassoc (attr := simp)] MonoFactorisation.fac

attribute [instance] MonoFactorisation.m_mono

namespace MonoFactorisation

/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: [Mono f]
  body: X
  m := f
  e := 𝟙 X

中文:
定义 self
  签名: [单态射 f]
  定义体: X
  m := f
  e := 𝟙 X
-/
def self [Mono f] : MonoFactorisation f where
  I := X
  m := f
  e := 𝟙 X

-- I'm not sure we really need this, but the linter says that an inhabited instance
-- ought to exist...
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Inhabited (MonoFactorisation f)
  body: ⟨self f⟩

中文:
实例 [单态射
  签名: f] : 可居 (单态射分解 f)
  定义体: ⟨self f⟩
-/
instance [Mono f] : Inhabited (MonoFactorisation f) := ⟨self f⟩

variable {f}

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely
determined. -/
@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {F F' : MonoFactorisation f} (hI : F.I = F'.I)
  proof: by
  obtain ⟨_, Fm, _, Ffac⟩ := F; obtain ⟨_, Fm', _, Ffac'⟩ := F'
  cases hI
  replace hm : Fm = Fm' := by simpa using hm
  congr
  apply (cancel_mono Fm).1
  rw [Ffac]; rw [hm]; rw [Ffac']

中文:
定理 ext
  结论: {F F' : 单态射分解 f} (hI : F.I = F'.I)
  证明: by
  obtain ⟨_, Fm, _, Ffac⟩ := F; obtain ⟨_, Fm', _, Ffac'⟩ := F'
  cases hI
  replace hm : Fm = Fm' := by simpa using hm
  congr
  apply (cancel_mono Fm).1
  rw [Ffac]; rw [hm]; rw [Ffac']

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, cancel_mono, isIso_of_isIso_app, prodComparisonNatTrans, replace
-/
theorem ext {F F' : MonoFactorisation f} (hI : F.I = F'.I)
    (hm : F.m = eqToHom hI ≫ F'.m) : F = F' := by
  obtain ⟨_, Fm, _, Ffac⟩ := F; obtain ⟨_, Fm', _, Ffac'⟩ := F'
  cases hI
  replace hm : Fm = Fm' := by simpa using hm
  congr
  apply (cancel_mono Fm).1
  rw [Ffac]; rw [hm]; rw [Ffac']

/-- Any mono factorisation of `f` gives a mono factorisation of `f ≫ g` when `g` is a mono. -/
@[simps]
/--
Definition of `compMono` / `compMono` 的定义

English:
definition compMono
  signature: (F : MonoFactorisation f) {Y' : C} (g : Y ⟶ Y') [Mono g]
  body: F.I
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e

中文:
定义 compMono
  签名: (F : 单态射分解 f) {Y' : C} (g : Y ⟶ Y') [单态射 g]
  定义体: F.I
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e
-/
def compMono (F : MonoFactorisation f) {Y' : C} (g : Y ⟶ Y') [Mono g] :
    MonoFactorisation (f ≫ g) where
  I := F.I
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e

/-- A mono factorisation of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
/--
Definition of `ofCompIso` / `ofCompIso` 的定义

English:
definition ofCompIso
  signature: {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorisation (f ≫ g))
  body: F.I
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e

中文:
定义 ofCompIso
  签名: {Y' : C} {g : Y ⟶ Y'} [是同构 g] (F : 单态射分解 (f ≫ g))
  定义体: F.I
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e
-/
def ofCompIso {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorisation (f ≫ g)) :
    MonoFactorisation f where
  I := F.I
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e

/-- Any mono factorisation of `f` gives a mono factorisation of `g ≫ f`. -/
@[simps]
/--
Definition of `isoComp` / `isoComp` 的定义

English:
definition isoComp
  signature: (F : MonoFactorisation f) {X' : C} (g : X' ⟶ X)
  body: F.I
  m := F.m
  e := g ≫ F.e

中文:
定义 isoComp
  签名: (F : 单态射分解 f) {X' : C} (g : X' ⟶ X)
  定义体: F.I
  m := F.m
  e := g ≫ F.e
-/
def isoComp (F : MonoFactorisation f) {X' : C} (g : X' ⟶ X) : MonoFactorisation (g ≫ f) where
  I := F.I
  m := F.m
  e := g ≫ F.e

/-- A mono factorisation of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
/--
Definition of `ofIsoComp` / `ofIsoComp` 的定义

English:
definition ofIsoComp
  signature: {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorisation (g ≫ f))
  body: F.I
  m := F.m
  e := inv g ≫ F.e

中文:
定义 ofIsoComp
  签名: {X' : C} (g : X' ⟶ X) [是同构 g] (F : 单态射分解 (g ≫ f))
  定义体: F.I
  m := F.m
  e := inv g ≫ F.e
-/
def ofIsoComp {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorisation (g ≫ f)) :
    MonoFactorisation f where
  I := F.I
  m := F.m
  e := inv g ≫ F.e

/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f`
gives a mono factorisation of `g` -/
@[simps]
/--
Definition of `ofArrowIso` / `ofArrowIso` 的定义

English:
definition ofArrowIso
  signature: {f g : Arrow C} (F : MonoFactorisation f.hom) (sq : f ⟶ g) [IsIso sq]
  body: F.I
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, Arrow.w, IsIso.inv_comp_eq, Category.assoc]

中文:
定义 ofArrowIso
  签名: {f g : 箭头 C} (F : 单态射分解 f.hom) (sq : f ⟶ g) [是同构 sq]
  定义体: F.I
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, Arrow.w, IsIso.inv_comp_eq, Category.assoc]
-/
def ofArrowIso {f g : Arrow C} (F : MonoFactorisation f.hom) (sq : f ⟶ g) [IsIso sq] :
    MonoFactorisation g.hom where
  I := F.I
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, Arrow.w, IsIso.inv_comp_eq, Category.assoc]

/--
Given a mono factorisation `X ⟶ I ⟶ Y` of an arrow `f`, an isomorphism `I ≅ I'` gives a new mono
factorisation `X ⟶ I' ⟶ Y` of `f`.
-/
@[simps]
/--
Definition of `ofIsoI` / `ofIsoI` 的定义

English:
definition ofIsoI
  signature: (F : MonoFactorisation f) {I'} (e : F.I ≅ I')
  body: I'
  m := e.inv ≫ F.m
  e := F.e ≫ e.hom

中文:
定义 ofIsoI
  签名: (F : 单态射分解 f) {I'} (e : F.I ≅ I')
  定义体: I'
  m := e.inv ≫ F.m
  e := F.e ≫ e.hom
-/
def ofIsoI (F : MonoFactorisation f) {I'} (e : F.I ≅ I') :
    MonoFactorisation f where
  I := I'
  m := e.inv ≫ F.m
  e := F.e ≫ e.hom

/--
Copying a mono factorisation to another mono factorisation with propositionally equal
`m` and `e` fields.
-/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (F : MonoFactorisation f) (m : F.I ⟶ Y) (e : X ⟶ F.I)
  body: F.I
  m := m
  e := e
  m_mono := by rw [hm]; infer_instance

@[simp]

中文:
定义 copy
  签名: (F : 单态射分解 f) (m : F.I ⟶ Y) (e : X ⟶ F.I)
  定义体: F.I
  m := m
  e := e
  m_mono := by rw [hm]; infer_instance

@[simp]

Depends on / 依赖: MonoFactorisation, cat_disch, infer_instance, m_mono
-/
def copy (F : MonoFactorisation f) (m : F.I ⟶ Y) (e : X ⟶ F.I)
    (hm : m = F.m := by cat_disch) (he : e = F.e := by cat_disch) :
    MonoFactorisation f where
  I := F.I
  m := m
  e := e
  m_mono := by rw [hm]; infer_instance

@[simp]
/--
lemma `fac_apply` / 引理 `fac_apply`

English:
lemma fac_apply
  statement: {F G : C ⥤ Type w} {f : F ⟶ G} {X : C}
  proof: by
  simp [← comp_apply, ← NatTrans.comp_app]

中文:
引理 fac_apply
  结论: {F G : C ⥤ 类型 w} {f : F ⟶ G} {X : C}
  证明: by
  simp [← comp_apply, ← NatTrans.comp_app]

Depends on / 依赖: NatTrans, NatTrans.comp_app, comp_app, comp_apply
-/
lemma fac_apply {F G : C ⥤ Type w} {f : F ⟶ G} {X : C}
    (H : MonoFactorisation f) (x : F.obj X) : H.m.app X (H.e.app X x) = f.app X x := by
  simp [← comp_apply, ← NatTrans.comp_app]

end MonoFactorisation

variable {f}

/--
Definition of `IsImage` / `IsImage` 的定义

English:
structure IsImage
  parameters: (F : MonoFactorisation f)
  axioms and operations (2):
    - lift : forall F' : MonoFactorisation f, F.I ⟶ F'.I
    - lift_fac : forall F' : MonoFactorisation f, lift F' ≫ F'.m = F.m  [default: by cat_disch]

中文:
结构 是像
  参数: (F : 单态射分解 f)
  公理与运算 (2 个):
    - lift : 对任意 F' : 单态射分解 f, F.I ⟶ F'.I
    - lift_fac : 对任意 F' : 单态射分解 f, lift F' ≫ F'.m = F.m  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure IsImage (F : MonoFactorisation f) where
  lift : forall F' : MonoFactorisation f, F.I ⟶ F'.I
  lift_fac : forall F' : MonoFactorisation f, lift F' ≫ F'.m = F.m := by cat_disch

attribute [inherit_doc IsImage] IsImage.lift IsImage.lift_fac

attribute [reassoc (attr := simp)] IsImage.lift_fac

namespace IsImage

@[reassoc (attr := simp)]
/--
theorem `fac_lift` / 定理 `fac_lift`

English:
theorem fac_lift
  given: {F : MonoFactorisation f} (hF : IsImage F) (F' : MonoFactorisation f)
  proof: (cancel_mono F'.m).1 by simp

中文:
定理 fac_lift
  条件: {F : 单态射分解 f} (hF : 是像 F) (F' : 单态射分解 f)
  证明: (cancel_mono F'.m).1 by simp

Depends on / 依赖: cancel_mono
-/
theorem fac_lift {F : MonoFactorisation f} (hF : IsImage F) (F' : MonoFactorisation f) :
    F.e ≫ hF.lift F' = F'.e :=
(cancel_mono F'.m).1 by simp

variable (f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The trivial factorisation of a monomorphism satisfies the universal property. -/
@[simps]
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: [Mono f]
  body: F'.e

中文:
定义 self
  签名: [单态射 f]
  定义体: F'.e
-/
def self [Mono f] : IsImage (MonoFactorisation.self f) where lift F' := F'.e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Inhabited (IsImage (MonoFactorisation.self f))
  body: ⟨self f⟩

中文:
实例 [单态射
  签名: f] : 可居 (是像 (单态射分解.self f))
  定义体: ⟨self f⟩
-/
instance [Mono f] : Inhabited (IsImage (MonoFactorisation.self f)) :=
  ⟨self f⟩

variable {f}

-- TODO this is another good candidate for a future `UniqueUpToCanonicalIso`.
/-- Two factorisations through monomorphisms satisfying the universal property
must factor through isomorphic objects. -/
@[simps]
/--
Definition of `isoExt` / `isoExt` 的定义

English:
definition isoExt
  signature: {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F')
  body: hF.lift F'
  inv := hF'.lift F
  hom_inv_id := (cancel_mono F.m).1 (by simp)
  inv_hom_id := (cancel_mono F'.m).1 (by simp)

中文:
定义 isoExt
  签名: {F F' : 单态射分解 f} (hF : 是像 F) (hF' : 是像 F')
  定义体: hF.lift F'
  inv := hF'.lift F
  hom_inv_id := (cancel_mono F.m).1 (by simp)
  inv_hom_id := (cancel_mono F'.m).1 (by simp)

Depends on / 依赖: hF.lift
-/
def isoExt {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F') :
    F.I ≅ F'.I where
  hom := hF.lift F'
  inv := hF'.lift F
  hom_inv_id := (cancel_mono F.m).1 (by simp)
  inv_hom_id := (cancel_mono F'.m).1 (by simp)

variable {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F')

/--
theorem `isoExt_hom_m` / 定理 `isoExt_hom_m`

English:
theorem isoExt_hom_m
  statement: (isoExt hF hF').hom ≫ F'.m = F.m
  proof: by simp

中文:
定理 isoExt_hom_m
  结论: (isoExt hF hF').hom ≫ F'.m = F.m
  证明: by simp
-/
theorem isoExt_hom_m : (isoExt hF hF').hom ≫ F'.m = F.m := by simp

/--
theorem `isoExt_inv_m` / 定理 `isoExt_inv_m`

English:
theorem isoExt_inv_m
  statement: (isoExt hF hF').inv ≫ F.m = F'.m
  proof: by simp

中文:
定理 isoExt_inv_m
  结论: (isoExt hF hF').inv ≫ F.m = F'.m
  证明: by simp
-/
theorem isoExt_inv_m : (isoExt hF hF').inv ≫ F.m = F'.m := by simp

/--
theorem `e_isoExt_hom` / 定理 `e_isoExt_hom`

English:
theorem e_isoExt_hom
  statement: F.e ≫ (isoExt hF hF').hom = F'.e
  proof: by simp

中文:
定理 e_isoExt_hom
  结论: F.e ≫ (isoExt hF hF').hom = F'.e
  证明: by simp
-/
theorem e_isoExt_hom : F.e ≫ (isoExt hF hF').hom = F'.e := by simp

/--
theorem `e_isoExt_inv` / 定理 `e_isoExt_inv`

English:
theorem e_isoExt_inv
  statement: F'.e ≫ (isoExt hF hF').inv = F.e
  proof: by simp

中文:
定理 e_isoExt_inv
  结论: F'.e ≫ (isoExt hF hF').inv = F.e
  证明: by simp
-/
theorem e_isoExt_inv : F'.e ≫ (isoExt hF hF').inv = F.e := by simp

set_option backward.isDefEq.respectTransparency false in
/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f` that is an image
gives a mono factorisation of `g` that is an image -/
@[simps]
/--
Definition of `ofArrowIso` / `ofArrowIso` 的定义

English:
definition ofArrowIso
  signature: {f g : Arrow C} {F : MonoFactorisation f.hom} (hF : IsImage F) (sq : f ⟶ g)
  body: hF.lift (F'.ofArrowIso (inv sq))
  lift_fac F' := by
    simpa only [MonoFactorisation.ofArrowIso_m, Arrow.inv_right, ← Category.assoc,
      IsIso.comp_inv_eq] using hF.lift_fac (F'.ofArrowIso (inv sq))

中文:
定义 ofArrowIso
  签名: {f g : 箭头 C} {F : 单态射分解 f.hom} (hF : 是像 F) (sq : f ⟶ g)
  定义体: hF.lift (F'.ofArrowIso (inv sq))
  lift_fac F' := by
    simpa only [MonoFactorisation.ofArrowIso_m, Arrow.inv_right, ← Category.assoc,
      IsIso.comp_inv_eq] using hF.lift_fac (F'.ofArrowIso (inv sq))

Depends on / 依赖: hF.lift, ofArrowIso
-/
def ofArrowIso {f g : Arrow C} {F : MonoFactorisation f.hom} (hF : IsImage F) (sq : f ⟶ g)
    [IsIso sq] : IsImage (F.ofArrowIso sq) where
  lift F' := hF.lift (F'.ofArrowIso (inv sq))
  lift_fac F' := by
    simpa only [MonoFactorisation.ofArrowIso_m, Arrow.inv_right, ← Category.assoc,
      IsIso.comp_inv_eq] using hF.lift_fac (F'.ofArrowIso (inv sq))

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a mono factorisation `X ⟶ I ⟶ Y` of an arrow `f` that is an image and an isomorphism `I ≅ I'`,
the induced mono factorisation by the isomorphism is also an image.
-/
@[simps]
/--
Definition of `ofIsoI` / `ofIsoI` 的定义

English:
definition ofIsoI
  signature: {F : MonoFactorisation f} (hF : IsImage F) {I' : C} (e : F.I ≅ I')
  body: e.inv ≫ hF.lift F'

中文:
定义 ofIsoI
  签名: {F : 单态射分解 f} (hF : 是像 F) {I' : C} (e : F.I ≅ I')
  定义体: e.inv ≫ hF.lift F'

Depends on / 依赖: e.inv, hF.lift, isIso_prodComparison_of_preservesLimit_pair
-/
def ofIsoI {F : MonoFactorisation f} (hF : IsImage F) {I' : C} (e : F.I ≅ I') :
    IsImage (F.ofIsoI e) where
  lift F' := e.inv ≫ hF.lift F'

set_option backward.defeqAttrib.useBackward true in
/--
Copying a mono factorisation to another mono factorisation with propositionally equal fields
preserves the property of being an image.
This is useful when one needs precise control of the `m` and `e` fields.
-/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {F : MonoFactorisation f} (hF : IsImage F) (m : F.I ⟶ Y) (e : X ⟶ F.I)
  body: hF.lift

中文:
定义 copy
  签名: {F : 单态射分解 f} (hF : 是像 F) (m : F.I ⟶ Y) (e : X ⟶ F.I)
  定义体: hF.lift

Depends on / 依赖: F.copy, IsImage, cat_disch, hF.lift
-/
def copy {F : MonoFactorisation f} (hF : IsImage F) (m : F.I ⟶ Y) (e : X ⟶ F.I)
    (hm : m = F.m := by cat_disch) (he : e = F.e := by cat_disch) :
    IsImage (F.copy m e) where
  lift := hF.lift

end IsImage

variable (f)

/--
Definition of `ImageFactorisation` / `ImageFactorisation` 的定义

English:
structure ImageFactorisation
  parameters: (f : X ⟶ Y)
  axioms and operations (2):
    - F : MonoFactorisation f
    - isImage : IsImage F

中文:
结构 ImageFactorisation
  参数: (f : X ⟶ Y)
  公理与运算 (2 个):
    - F : 单态射分解 f
    - isImage : 是像 F
-/
structure ImageFactorisation (f : X ⟶ Y) where
  F : MonoFactorisation f
  isImage : IsImage F

attribute [inherit_doc ImageFactorisation] ImageFactorisation.F ImageFactorisation.isImage

namespace ImageFactorisation

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Inhabited (ImageFactorisation f)
  body: ⟨⟨_, IsImage.self f⟩⟩

中文:
实例 [单态射
  签名: f] : 可居 (ImageFactorisation f)
  定义体: ⟨⟨_, IsImage.self f⟩⟩

Depends on / 依赖: IsImage, IsImage.self
-/
instance [Mono f] : Inhabited (ImageFactorisation f) :=
  ⟨⟨_, IsImage.self f⟩⟩

/-- If `f` and `g` are isomorphic arrows, then an image factorisation of `f`
gives an image factorisation of `g` -/
@[simps]
/--
Definition of `ofArrowIso` / `ofArrowIso` 的定义

English:
definition ofArrowIso
  signature: {f g : Arrow C} (F : ImageFactorisation f.hom) (sq : f ⟶ g) [IsIso sq]
  body: F.F.ofArrowIso sq
  isImage := F.isImage.ofArrowIso sq

中文:
定义 ofArrowIso
  签名: {f g : 箭头 C} (F : ImageFactorisation f.hom) (sq : f ⟶ g) [是同构 sq]
  定义体: F.F.ofArrowIso sq
  isImage := F.isImage.ofArrowIso sq

Depends on / 依赖: F.F.ofArrowIso, ofArrowIso
-/
def ofArrowIso {f g : Arrow C} (F : ImageFactorisation f.hom) (sq : f ⟶ g) [IsIso sq] :
    ImageFactorisation g.hom where
  F := F.F.ofArrowIso sq
  isImage := F.isImage.ofArrowIso sq

/--
Given an image factorisation `X ⟶ I ⟶ Y` of an arrow `f`, an isomorphism `I ≅ I'` induces a new
image factorisation `X ⟶ I' ⟶ Y` of `f`.
-/
@[simps]
/--
Definition of `ofIsoI` / `ofIsoI` 的定义

English:
definition ofIsoI
  signature: {f : X ⟶ Y} (F : ImageFactorisation f) {I' : C} (e : F.F.I ≅ I')
  body: F.F.ofIsoI e
  isImage := F.isImage.ofIsoI e

中文:
定义 ofIsoI
  签名: {f : X ⟶ Y} (F : ImageFactorisation f) {I' : C} (e : F.F.I ≅ I')
  定义体: F.F.ofIsoI e
  isImage := F.isImage.ofIsoI e

Depends on / 依赖: F.F.ofIsoI, ofIsoI
-/
def ofIsoI {f : X ⟶ Y} (F : ImageFactorisation f) {I' : C} (e : F.F.I ≅ I') :
    ImageFactorisation f where
  F := F.F.ofIsoI e
  isImage := F.isImage.ofIsoI e

/--
Copying an image factorisation to another image factorisation with propositionally equal
`m` and `e` fields.
-/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {f : X ⟶ Y} (F : ImageFactorisation f) (m : F.F.I ⟶ Y) (e : X ⟶ F.F.I)
  body: F.F.copy m e
  isImage := F.isImage.copy m e

中文:
定义 copy
  签名: {f : X ⟶ Y} (F : ImageFactorisation f) (m : F.F.I ⟶ Y) (e : X ⟶ F.F.I)
  定义体: F.F.copy m e
  isImage := F.isImage.copy m e

Depends on / 依赖: F.F.copy, F.F.e, F.isImage.copy, ImageFactorisation, cat_disch, isImage
-/
def copy {f : X ⟶ Y} (F : ImageFactorisation f) (m : F.F.I ⟶ Y) (e : X ⟶ F.F.I)
    (hm : m = F.F.m := by cat_disch) (he : e = F.F.e := by cat_disch) :
    ImageFactorisation f where
  F := F.F.copy m e
  isImage := F.isImage.copy m e

end ImageFactorisation

/--
Definition of `HasImage` / `HasImage` 的定义

English:
class HasImage
  parameters: (f : X ⟶ Y)
  (no additional axioms)

中文:
类 有像
  参数: (f : X ⟶ Y)
  (无附加公理)
-/
class HasImage (f : X ⟶ Y) : Prop where mk' ::
  exists_image : Nonempty (ImageFactorisation f)

attribute [inherit_doc HasImage] HasImage.exists_image

/--
theorem `HasImage.mk` / 定理 `HasImage.mk`

English:
theorem HasImage.mk
  given: {f : X ⟶ Y} (F : ImageFactorisation f)
  statement: HasImage f
  proof: ⟨Nonempty.intro F⟩

中文:
定理 有像.mk
  条件: {f : X ⟶ Y} (F : ImageFactorisation f)
  结论: 有像 f
  证明: ⟨Nonempty.intro F⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasImage.mk {f : X ⟶ Y} (F : ImageFactorisation f) : HasImage f :=
  ⟨Nonempty.intro F⟩

/--
theorem `HasImage.of_arrow_iso` / 定理 `HasImage.of_arrow_iso`

English:
theorem HasImage.of_arrow_iso
  given: {f g : Arrow C} [h : HasImage f.hom] (sq : f ⟶ g) [IsIso sq]
  proof: ⟨⟨h.exists_image.some.ofArrowIso sq⟩⟩

中文:
定理 有像.of_arrow_iso
  条件: {f g : 箭头 C} [h : 有像 f.hom] (sq : f ⟶ g) [是同构 sq]
  证明: ⟨⟨h.exists_image.some.ofArrowIso sq⟩⟩

Depends on / 依赖: exists_image, h.exists_image.some.ofArrowIso, ofArrowIso
-/
theorem HasImage.of_arrow_iso {f g : Arrow C} [h : HasImage f.hom] (sq : f ⟶ g) [IsIso sq] :
    HasImage g.hom :=
  ⟨⟨h.exists_image.some.ofArrowIso sq⟩⟩

instance (priority := 100) mono_hasImage (f : X ⟶ Y) [Mono f] : HasImage f :=
  HasImage.mk ⟨_, IsImage.self f⟩

section

variable [HasImage f]

/--
Definition of `Image.imageFactorisation` / `Image.imageFactorisation` 的定义

English:
definition Image.imageFactorisation
  signature: : ImageFactorisation f
  body: Classical.choice HasImage.exists_image

中文:
定义 像.imageFactorisation
  签名: : ImageFactorisation f
  定义体: Classical.choice HasImage.exists_image

Depends on / 依赖: Classical, Classical.choice, HasImage, HasImage.exists_image, choice, exists_image
-/
def Image.imageFactorisation : ImageFactorisation f :=
  Classical.choice HasImage.exists_image

/--
Definition of `Image.monoFactorisation` / `Image.monoFactorisation` 的定义

English:
definition Image.monoFactorisation
  signature: : MonoFactorisation f
  body: (Image.imageFactorisation f).F

中文:
定义 像.monoFactorisation
  签名: : 单态射分解 f
  定义体: (Image.imageFactorisation f).F

Depends on / 依赖: Image.imageFactorisation, imageFactorisation
-/
def Image.monoFactorisation : MonoFactorisation f :=
  (Image.imageFactorisation f).F

/--
Definition of `Image.isImage` / `Image.isImage` 的定义

English:
definition Image.isImage
  signature: : IsImage (Image.monoFactorisation f)
  body: (Image.imageFactorisation f).isImage

中文:
定义 像.isImage
  签名: : 是像 (像.monoFactorisation f)
  定义体: (Image.imageFactorisation f).isImage

Depends on / 依赖: Image.imageFactorisation, imageFactorisation, isImage
-/
def Image.isImage : IsImage (Image.monoFactorisation f) :=
  (Image.imageFactorisation f).isImage

/-- The categorical image of a morphism. -/
@[implicit_reducible]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : C
  body: (Image.monoFactorisation f).I

中文:
定义 像
  签名: : C
  定义体: (Image.monoFactorisation f).I

Depends on / 依赖: Image.monoFactorisation, monoFactorisation
-/
def image : C :=
  (Image.monoFactorisation f).I

/--
Definition of `image.ι` / `image.ι` 的定义

English:
definition image.ι
  signature: : image f ⟶ Y
  body: (Image.monoFactorisation f).m

@[simp]

中文:
定义 像.ι
  签名: : 像 f ⟶ Y
  定义体: (Image.monoFactorisation f).m

@[simp]
-/
def image.ι : image f ⟶ Y :=
  (Image.monoFactorisation f).m

@[simp]
/--
theorem `image.as_ι` / 定理 `image.as_ι`

English:
theorem image.as_ι
  statement: (Image.monoFactorisation f).m = image.ι f
  proof: rfl

中文:
定理 像.as_ι
  结论: (像.monoFactorisation f).m = 像.ι f
  证明: rfl
-/
theorem image.as_ι : (Image.monoFactorisation f).m = image.ι f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (image.ι f)
  body: (Image.monoFactorisation f).m_mono

中文:
实例 :
  签名: 单态射 (像.ι f)
  定义体: (Image.monoFactorisation f).m_mono

Depends on / 依赖: Image.monoFactorisation, m_mono, monoFactorisation
-/
instance : Mono (image.ι f) :=
  (Image.monoFactorisation f).m_mono

/--
Definition of `factorThruImage` / `factorThruImage` 的定义

English:
definition factorThruImage
  signature: : X ⟶ image f
  body: (Image.monoFactorisation f).e

中文:
定义 factorThruImage
  签名: : X ⟶ 像 f
  定义体: (Image.monoFactorisation f).e

Depends on / 依赖: Image.monoFactorisation, monoFactorisation
-/
def factorThruImage : X ⟶ image f :=
  (Image.monoFactorisation f).e

/-- Rewrite in terms of the `factorThruImage` interface. -/
@[simp]
/--
theorem `as_factorThruImage` / 定理 `as_factorThruImage`

English:
theorem as_factorThruImage
  statement: (Image.monoFactorisation f).e = factorThruImage f
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 as_factorThruImage
  结论: (像.monoFactorisation f).e = factorThruImage f
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem as_factorThruImage : (Image.monoFactorisation f).e = factorThruImage f :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `image.fac` / 定理 `image.fac`

English:
theorem image.fac
  statement: factorThruImage f ≫ image.ι f = f
  proof: (Image.monoFactorisation f).fac

中文:
定理 像.fac
  结论: factorThruImage f ≫ 像.ι f = f
  证明: (Image.monoFactorisation f).fac
-/
theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  (Image.monoFactorisation f).fac

variable {f}

/--
Definition of `image.lift` / `image.lift` 的定义

English:
definition image.lift
  signature: (F' : MonoFactorisation f)
  body: (Image.isImage f).lift F'

@[reassoc (attr := simp)]

中文:
定义 像.lift
  签名: (F' : 单态射分解 f)
  定义体: (Image.isImage f).lift F'

@[reassoc (attr := simp)]
-/
def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  (Image.isImage f).lift F'

@[reassoc (attr := simp)]
/--
theorem `image.lift_fac` / 定理 `image.lift_fac`

English:
theorem image.lift_fac
  given: (F' : MonoFactorisation f)
  statement: image.lift F' ≫ F'.m = image.ι f
  proof: (Image.isImage f).lift_fac F'

@[reassoc (attr := simp)]

中文:
定理 像.lift_fac
  条件: (F' : 单态射分解 f)
  结论: 像.lift F' ≫ F'.m = 像.ι f
  证明: (Image.isImage f).lift_fac F'

@[reassoc (attr := simp)]
-/
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f :=
  (Image.isImage f).lift_fac F'

@[reassoc (attr := simp)]
/--
theorem `image.fac_lift` / 定理 `image.fac_lift`

English:
theorem image.fac_lift
  given: (F' : MonoFactorisation f)
  statement: factorThruImage f ≫ image.lift F' = F'.e
  proof: (Image.isImage f).fac_lift F'

@[simp]

中文:
定理 像.fac_lift
  条件: (F' : 单态射分解 f)
  结论: factorThruImage f ≫ 像.lift F' = F'.e
  证明: (Image.isImage f).fac_lift F'

@[simp]

Depends on / 依赖: Image.isImage, fac_lift, isImage
-/
theorem image.fac_lift (F' : MonoFactorisation f) : factorThruImage f ≫ image.lift F' = F'.e :=
  (Image.isImage f).fac_lift F'

@[simp]
/--
theorem `image.isImage_lift` / 定理 `image.isImage_lift`

English:
theorem image.isImage_lift
  given: (F : MonoFactorisation f)
  statement: (Image.isImage f).lift F = image.lift F
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 像.isImage_lift
  条件: (F : 单态射分解 f)
  结论: (像.isImage f).lift F = 像.lift F
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem image.isImage_lift (F : MonoFactorisation f) : (Image.isImage f).lift F = image.lift F :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `IsImage.lift_ι` / 定理 `IsImage.lift_ι`

English:
theorem IsImage.lift_ι
  given: {F : MonoFactorisation f} (hF : IsImage F)
  proof: hF.lift_fac _

@[reassoc (attr := simp)]

中文:
定理 是像.lift_ι
  条件: {F : 单态射分解 f} (hF : 是像 F)
  证明: hF.lift_fac _

@[reassoc (attr := simp)]

Depends on / 依赖: hF.lift_fac, lift_fac
-/
theorem IsImage.lift_ι {F : MonoFactorisation f} (hF : IsImage F) :
    hF.lift (Image.monoFactorisation f) ≫ image.ι f = F.m :=
  hF.lift_fac _

@[reassoc (attr := simp)]
/--
theorem `image.lift_mk_factorThruImage` / 定理 `image.lift_mk_factorThruImage`

English:
theorem image.lift_mk_factorThruImage
  proof: (Image.isImage f).lift_fac _

@[reassoc (attr := simp)]

中文:
定理 像.lift_mk_factorThruImage
  证明: (Image.isImage f).lift_fac _

@[reassoc (attr := simp)]

Depends on / 依赖: factorThruImage
-/
theorem image.lift_mk_factorThruImage :
    image.lift { I := image f, m := ι f, e := factorThruImage f } ≫ image.ι f = image.ι f :=
  (Image.isImage f).lift_fac _

@[reassoc (attr := simp)]
/--
theorem `image.lift_mk_comp` / 定理 `image.lift_mk_comp`

English:
theorem image.lift_mk_comp
  statement: {C : Type u} [Category.{v} C] {X Y Z : C}
  proof: image.lift_fac _

中文:
定理 像.lift_mk_comp
  结论: {C : 类型u} [范畴.{v} C] {X Y Z : C}
  证明: image.lift_fac _
-/
theorem image.lift_mk_comp {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasImage g] [HasImage (f ≫ g)]
    (h : Y ⟶ image g) (H : (f ≫ h) ≫ image.ι g = f ≫ g) :
    image.lift { I := image g, m := ι g, e := (f ≫ h) } ≫ image.ι g = image.ι (f ≫ g) :=
  image.lift_fac _

-- TODO we could put a category structure on `MonoFactorisation f`,
-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s
-- (they then automatically commute with the `e`s)
-- and show that an `imageOf f` gives an initial object there
-- (uniqueness of the lift comes for free).
/--
Instance `image.lift_mono` / 实例 `image.lift_mono`

English:
instance image.lift_mono
  signature: (F' : MonoFactorisation f)
  body: by
  refine @mono_of_mono _ _ _ _ _ _ F'.m ?_
  simpa using! MonoFactorisation.m_mono _

中文:
实例 像.lift_mono
  签名: (F' : 单态射分解 f)
  定义体: by
  refine @mono_of_mono _ _ _ _ _ _ F'.m ?_
  simpa using! MonoFactorisation.m_mono _

Depends on / 依赖: MonoFactorisation, MonoFactorisation.m_mono, m_mono, mono_of_mono
-/
instance image.lift_mono (F' : MonoFactorisation f) : Mono (image.lift F') := by
  refine @mono_of_mono _ _ _ _ _ _ F'.m ?_
  simpa using! MonoFactorisation.m_mono _

/--
theorem `HasImage.uniq` / 定理 `HasImage.uniq`

English:
theorem HasImage.uniq
  given: (F' : MonoFactorisation f) (l : image f ⟶ F'.I) (w : l ≫ F'.m = image.ι f)
  proof: (cancel_mono F'.m).1 (by simp [w])

中文:
定理 有像.uniq
  条件: (F' : 单态射分解 f) (l : 像 f ⟶ F'.I) (w : l ≫ F'.m = 像.ι f)
  证明: (cancel_mono F'.m).1 (by simp [w])

Depends on / 依赖: cancel_mono
-/
theorem HasImage.uniq (F' : MonoFactorisation f) (l : image f ⟶ F'.I) (w : l ≫ F'.m = image.ι f) :
    l = image.lift F' :=
  (cancel_mono F'.m).1 (by simp [w])

/-- If `has_image g`, then `has_image (f ≫ g)` when `f` is an isomorphism. -/
instance {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [HasImage g] : HasImage (f ≫ g) where
  exists_image :=
    ⟨{ F :=
          { I := image g
            m := image.ι g
            e := f ≫ factorThruImage g }
        isImage :=
          { lift := fun F' => image.lift
                { I := F'.I
                  m := F'.m
                  e := inv f ≫ F'.e } } }⟩

end

section

variable (C)

/--
Definition of `HasImages` / `HasImages` 的定义

English:
class HasImages
  parameters: : Prop where
  axioms and operations (1):
    - has_image : forall {X Y : C} (f : X ⟶ Y), HasImage f

中文:
类 有Images
  参数: : 命题 where
  公理与运算 (1 个):
    - has_image : 对任意 {X Y : C} (f : X ⟶ Y), 有像 f
-/
class HasImages : Prop where
  has_image : forall {X Y : C} (f : X ⟶ Y), HasImage f

attribute [inherit_doc HasImages] HasImages.has_image

attribute [instance 100] HasImages.has_image

end

section

/--
Definition of `imageMonoIsoSource` / `imageMonoIsoSource` 的定义

English:
definition imageMonoIsoSource
  signature: [Mono f]
  body: IsImage.isoExt (Image.isImage f) (IsImage.self f)

@[reassoc (attr := simp)]

中文:
定义 imageMonoIsoSource
  签名: [单态射 f]
  定义体: IsImage.isoExt (Image.isImage f) (IsImage.self f)

@[reassoc (attr := simp)]

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, IsImage.self, isImage, isoExt
-/
def imageMonoIsoSource [Mono f] : image f ≅ X :=
  IsImage.isoExt (Image.isImage f) (IsImage.self f)

@[reassoc (attr := simp)]
/--
theorem `imageMonoIsoSource_inv_ι` / 定理 `imageMonoIsoSource_inv_ι`

English:
theorem imageMonoIsoSource_inv_ι
  given: [Mono f]
  statement: (imageMonoIsoSource f).inv ≫ image.ι f = f
  proof: by
  simp [imageMonoIsoSource]

@[reassoc (attr := simp)]

中文:
定理 imageMonoIsoSource_inv_ι
  条件: [单态射 f]
  结论: (imageMonoIsoSource f).inv ≫ 像.ι f = f
  证明: by
  simp [imageMonoIsoSource]

@[reassoc (attr := simp)]

Depends on / 依赖: imageMonoIsoSource
-/
theorem imageMonoIsoSource_inv_ι [Mono f] : (imageMonoIsoSource f).inv ≫ image.ι f = f := by
  simp [imageMonoIsoSource]

@[reassoc (attr := simp)]
/--
theorem `imageMonoIsoSource_hom_self` / 定理 `imageMonoIsoSource_hom_self`

English:
theorem imageMonoIsoSource_hom_self
  given: [Mono f]
  statement: (imageMonoIsoSource f).hom ≫ f = image.ι f
  proof: by
  simp only [← imageMonoIsoSource_inv_ι f]
  rw [← Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.id_comp]

中文:
定理 imageMonoIsoSource_hom_self
  条件: [单态射 f]
  结论: (imageMonoIsoSource f).hom ≫ f = 像.ι f
  证明: by
  simp only [← imageMonoIsoSource_inv_ι f]
  rw [← Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Iso.hom_inv_id, hom_inv_id, id_comp
-/
theorem imageMonoIsoSource_hom_self [Mono f] : (imageMonoIsoSource f).hom ≫ f = image.ι f := by
  simp only [← imageMonoIsoSource_inv_ι f]
  rw [← Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
-- This is the proof that `factorThruImage f` is an epimorphism
-- from https://en.wikipedia.org/wiki/Image_%28category_theory%29, which is in turn taken from:
-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1
@[ext (iff := false)]
/--
theorem `image.ext` / 定理 `image.ext`

English:
theorem image.ext
  statement: [HasImage f] {W : C} {g h : image f ⟶ W} [HasLimit (parallelPair g h)]
  proof: by
  let q := equalizer.ι g h
  let e' := equalizer.lift _ w
  let F' : MonoFactorisation f :=
    { I := equalizer g h
      m := q ≫ image.ι f
      m_mono := mono_comp _ _
      e := e' }
  let v := image.lift F'
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F'
  have t : v ≫ q = 𝟙 (image f) :=
    (cancel_mono_id (image.ι f)).1
      (by
        convert! t₀ using 1
        rw [Category.assoc])
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc
    g = 𝟙 (image f) ≫ g := by rw [Category.id_comp]
    _ = v ≫ q ≫ g := by rw [← t, Category.assoc]
    _ = v ≫ q ≫ h := by rw [equalizer.condition g h]
    _ = 𝟙 (image f) ≫ h := by rw [← Category.assoc, t]
    _ = h := by rw [Category.id_comp]

中文:
定理 像.ext
  结论: [有像 f] {W : C} {g h : 像 f ⟶ W} [有极限 (parallelPair g h)]
  证明: by
  let q := equalizer.ι g h
  let e' := equalizer.lift _ w
  let F' : MonoFactorisation f :=
    { I := equalizer g h
      m := q ≫ image.ι f
      m_mono := mono_comp _ _
      e := e' }
  let v := image.lift F'
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F'
  have t : v ≫ q = 𝟙 (image f) :=
    (cancel_mono_id (image.ι f)).1
      (by
        convert! t₀ using 1
        rw [Category.assoc])
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc
    g = 𝟙 (image f) ≫ g := by rw [Category.id_comp]
    _ = v ≫ q ≫ g := by rw [← t, Category.assoc]
    _ = v ≫ q ≫ h := by rw [equalizer.condition g h]
    _ = 𝟙 (image f) ≫ h := by rw [← Category.assoc, t]
    _ = h := by rw [Category.id_comp]

Depends on / 依赖: Category, Category.assoc, MonoFactorisation, cancel_mono_id, convert, equalizer, equalizer.lift, image.lift, image.lift_fac, lift_fac, m_mono, mono_comp
-/
theorem image.ext [HasImage f] {W : C} {g h : image f ⟶ W} [HasLimit (parallelPair g h)]
    (w : factorThruImage f ≫ g = factorThruImage f ≫ h) : g = h := by
  let q := equalizer.ι g h
  let e' := equalizer.lift _ w
  let F' : MonoFactorisation f :=
    { I := equalizer g h
      m := q ≫ image.ι f
      m_mono := mono_comp _ _
      e := e' }
  let v := image.lift F'
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F'
  have t : v ≫ q = 𝟙 (image f) :=
    (cancel_mono_id (image.ι f)).1
      (by
        convert! t₀ using 1
        rw [Category.assoc])
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc
    g = 𝟙 (image f) ≫ g := by rw [Category.id_comp]
    _ = v ≫ q ≫ g := by rw [← t, Category.assoc]
    _ = v ≫ q ≫ h := by rw [equalizer.condition g h]
    _ = 𝟙 (image f) ≫ h := by rw [← Category.assoc, t]
    _ = h := by rw [Category.id_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasImage
  signature: f] [forall {Z : C} (g h : image f ⟶ Z), HasLimit (parallelPair g h)] :
  body: ⟨fun _ _ w => image.ext f w⟩

中文:
实例 [有像
  签名: f] [对任意 {Z : C} (g h : 像 f ⟶ Z), 有极限 (parallelPair g h)] :
  定义体: ⟨fun _ _ w => image.ext f w⟩

Depends on / 依赖: image.ext
-/
instance [HasImage f] [forall {Z : C} (g h : image f ⟶ Z), HasLimit (parallelPair g h)] :
    Epi (factorThruImage f) :=
  ⟨fun _ _ w => image.ext f w⟩

/--
theorem `epi_image_of_epi` / 定理 `epi_image_of_epi`

English:
theorem epi_image_of_epi
  given: {X Y : C} (f : X ⟶ Y) [HasImage f] [E : Epi f]
  statement: Epi (image.ι f)
  proof: by
  rw [← image.fac f] at E
  exact epi_of_epi (factorThruImage f) (image.ι f)

中文:
定理 epi_image_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [有像 f] [E : 满态射 f]
  结论: 满态射 (像.ι f)
  证明: by
  rw [← image.fac f] at E
  exact epi_of_epi (factorThruImage f) (image.ι f)

Depends on / 依赖: epi_of_epi, factorThruImage, image.fac
-/
theorem epi_image_of_epi {X Y : C} (f : X ⟶ Y) [HasImage f] [E : Epi f] : Epi (image.ι f) := by
  rw [← image.fac f] at E
  exact epi_of_epi (factorThruImage f) (image.ι f)

/--
theorem `epi_of_epi_image` / 定理 `epi_of_epi_image`

English:
theorem epi_of_epi_image
  statement: {X Y : C} (f : X ⟶ Y) [HasImage f] [Epi (image.ι f)]
  proof: by
  rw [← image.fac f]
  apply epi_comp

中文:
定理 epi_of_epi_image
  结论: {X Y : C} (f : X ⟶ Y) [有像 f] [满态射 (像.ι f)]
  证明: by
  rw [← image.fac f]
  apply epi_comp

Depends on / 依赖: epi_comp, image.fac
-/
theorem epi_of_epi_image {X Y : C} (f : X ⟶ Y) [HasImage f] [Epi (image.ι f)]
    [Epi (factorThruImage f)] : Epi f := by
  rw [← image.fac f]
  apply epi_comp

end

section

variable {f}
variable {f' : X ⟶ Y} [HasImage f] [HasImage f']

/--
Definition of `image.eqToHom` / `image.eqToHom` 的定义

English:
definition image.eqToHom
  signature: (h : f = f')
  body: image.lift
    { I := image f'
      m := image.ι f'
      e := factorThruImage f'
      fac := by rw [h]; simp only [image.fac] }

中文:
定义 像.eqToHom
  签名: (h : f = f')
  定义体: image.lift
    { I := image f'
      m := image.ι f'
      e := factorThruImage f'
      fac := by rw [h]; simp only [image.fac] }

Depends on / 依赖: factorThruImage, image.fac, image.lift
-/
def image.eqToHom (h : f = f') : image f ⟶ image f' :=
  image.lift
    { I := image f'
      m := image.ι f'
      e := factorThruImage f'
      fac := by rw [h]; simp only [image.fac] }

instance (h : f = f') : IsIso (image.eqToHom h) :=
  ⟨⟨image.eqToHom h.symm,
      ⟨(cancel_mono (image.ι f)).1 (by
          subst h
          simp [image.eqToHom, Category.assoc, Category.id_comp]),
        (cancel_mono (image.ι f')).1 (by
          subst h
          simp [image.eqToHom])⟩⟩⟩

/--
Definition of `image.eqToIso` / `image.eqToIso` 的定义

English:
definition image.eqToIso
  signature: (h : f = f')
  body: asIso (image.eqToHom h)

中文:
定义 像.eqToIso
  签名: (h : f = f')
  定义体: asIso (image.eqToHom h)

Depends on / 依赖: eqToHom, image.eqToHom
-/
def image.eqToIso (h : f = f') : image f ≅ image f' :=
  asIso (image.eqToHom h)

/--
theorem `image.eq_fac` / 定理 `image.eq_fac`

English:
theorem image.eq_fac
  given: [HasEqualizers C] (h : f = f')
  proof: by
  apply image.ext
  subst h
  simp [asIso, image.eqToIso, image.eqToHom]

中文:
定理 像.eq_fac
  条件: [HasEqualizers C] (h : f = f')
  证明: by
  apply image.ext
  subst h
  simp [asIso, image.eqToIso, image.eqToHom]

Depends on / 依赖: eqToHom, eqToIso, image.eqToHom, image.eqToIso, image.ext
-/
theorem image.eq_fac [HasEqualizers C] (h : f = f') :
    image.ι f = (image.eqToIso h).hom ≫ image.ι f' := by
  apply image.ext
  subst h
  simp [asIso, image.eqToIso, image.eqToHom]

end

section

variable {Z : C} (g : Y ⟶ Z)

/--
Definition of `image.preComp` / `image.preComp` 的定义

English:
definition image.preComp
  signature: [HasImage g] [HasImage (f ≫ g)]
  body: image.lift
    { I := image g
      m := image.ι g
      e := f ≫ factorThruImage g }

@[reassoc (attr := simp)]

中文:
定义 像.preComp
  签名: [有像 g] [有像 (f ≫ g)]
  定义体: image.lift
    { I := image g
      m := image.ι g
      e := f ≫ factorThruImage g }

@[reassoc (attr := simp)]

Depends on / 依赖: factorThruImage, image.lift
-/
def image.preComp [HasImage g] [HasImage (f ≫ g)] : image (f ≫ g) ⟶ image g :=
  image.lift
    { I := image g
      m := image.ι g
      e := f ≫ factorThruImage g }

@[reassoc (attr := simp)]
/--
theorem `image.preComp_ι` / 定理 `image.preComp_ι`

English:
theorem image.preComp_ι
  given: [HasImage g] [HasImage (f ≫ g)]
  proof: by
      simp [image.preComp]

@[reassoc (attr := simp)]

中文:
定理 像.preComp_ι
  条件: [有像 g] [有像 (f ≫ g)]
  证明: by
      simp [image.preComp]

@[reassoc (attr := simp)]

Depends on / 依赖: image.preComp, preComp
-/
theorem image.preComp_ι [HasImage g] [HasImage (f ≫ g)] :
    image.preComp f g ≫ image.ι g = image.ι (f ≫ g) := by
      simp [image.preComp]

@[reassoc (attr := simp)]
/--
theorem `image.factorThruImage_preComp` / 定理 `image.factorThruImage_preComp`

English:
theorem image.factorThruImage_preComp
  given: [HasImage g] [HasImage (f ≫ g)]
  proof: by simp [image.preComp]

中文:
定理 像.factorThruImage_preComp
  条件: [有像 g] [有像 (f ≫ g)]
  证明: by simp [image.preComp]

Depends on / 依赖: image.preComp, preComp
-/
theorem image.factorThruImage_preComp [HasImage g] [HasImage (f ≫ g)] :
    factorThruImage (f ≫ g) ≫ image.preComp f g = f ≫ factorThruImage g := by simp [image.preComp]

/--
Instance `image.preComp_mono` / 实例 `image.preComp_mono`

English:
instance image.preComp_mono
  signature: [HasImage g] [HasImage (f ≫ g)]
  body: by
  refine @mono_of_mono _ _ _ _ _ _ (image.ι g) ?_
  simp only [image.preComp_ι]
  infer_instance

中文:
实例 像.preComp_mono
  签名: [有像 g] [有像 (f ≫ g)]
  定义体: by
  refine @mono_of_mono _ _ _ _ _ _ (image.ι g) ?_
  simp only [image.preComp_ι]
  infer_instance

Depends on / 依赖: image.preComp_, infer_instance, mono_of_mono
-/
instance image.preComp_mono [HasImage g] [HasImage (f ≫ g)] : Mono (image.preComp f g) := by
  refine @mono_of_mono _ _ _ _ _ _ (image.ι g) ?_
  simp only [image.preComp_ι]
  infer_instance

/--
theorem `image.preComp_comp` / 定理 `image.preComp_comp`

English:
theorem image.preComp_comp
  statement: {W : C} (h : Z ⟶ W) [HasImage (g ≫ h)] [HasImage (f ≫ g ≫ h)]
  proof: by
  apply (cancel_mono (image.ι h)).1
  simp only [preComp, Category.assoc, fac, lift_mk_comp, eqToHom]
  rw [image.lift_fac]

中文:
定理 像.preComp_comp
  结论: {W : C} (h : Z ⟶ W) [有像 (g ≫ h)] [有像 (f ≫ g ≫ h)]
  证明: by
  apply (cancel_mono (image.ι h)).1
  simp only [preComp, Category.assoc, fac, lift_mk_comp, eqToHom]
  rw [image.lift_fac]

Depends on / 依赖: Category, Category.assoc, cancel_mono, eqToHom, image.lift_fac, lift_fac, lift_mk_comp, preComp
-/
theorem image.preComp_comp {W : C} (h : Z ⟶ W) [HasImage (g ≫ h)] [HasImage (f ≫ g ≫ h)]
    [HasImage h] [HasImage ((f ≫ g) ≫ h)] :
    image.preComp f (g ≫ h) ≫ image.preComp g h =
      image.eqToHom (Category.assoc f g h).symm ≫ image.preComp (f ≫ g) h := by
  apply (cancel_mono (image.ι h)).1
  simp only [preComp, Category.assoc, fac, lift_mk_comp, eqToHom]
  rw [image.lift_fac]

variable [HasEqualizers C]

/--
Instance `image.preComp_epi_of_epi` / 实例 `image.preComp_epi_of_epi`

English:
instance image.preComp_epi_of_epi
  signature: [HasImage g] [HasImage (f ≫ g)] [Epi f]
  body: by
  apply @epi_of_epi_fac _ _ _ _ _ _ _ _ ?_ (image.factorThruImage_preComp _ _)
  exact epi_comp _ _

中文:
实例 像.preComp_epi_of_epi
  签名: [有像 g] [有像 (f ≫ g)] [满态射 f]
  定义体: by
  apply @epi_of_epi_fac _ _ _ _ _ _ _ _ ?_ (image.factorThruImage_preComp _ _)
  exact epi_comp _ _

Depends on / 依赖: epi_comp, epi_of_epi_fac, factorThruImage_preComp, image.factorThruImage_preComp
-/
instance image.preComp_epi_of_epi [HasImage g] [HasImage (f ≫ g)] [Epi f] :
    Epi (image.preComp f g) := by
  apply @epi_of_epi_fac _ _ _ _ _ _ _ _ ?_ (image.factorThruImage_preComp _ _)
  exact epi_comp _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasImage_iso_comp` / 实例 `hasImage_iso_comp`

English:
instance hasImage_iso_comp
  signature: [IsIso f] [HasImage g]
  body: HasImage.mk
    { F := (Image.monoFactorisation g).isoComp f
      isImage := { lift := fun F' => image.lift (F'.ofIsoComp f)
                   lift_fac := fun F' => by
                    dsimp
                    have : (MonoFactorisation.ofIsoComp f F').m = F'.m := rfl
                    rw [← this]; rw [image.lift_fac (MonoFactorisation.ofIsoComp f F')] } }

中文:
实例 hasImage_iso_comp
  签名: [是同构 f] [有像 g]
  定义体: HasImage.mk
    { F := (Image.monoFactorisation g).isoComp f
      isImage := { lift := fun F' => image.lift (F'.ofIsoComp f)
                   lift_fac := fun F' => by
                    dsimp
                    have : (MonoFactorisation.ofIsoComp f F').m = F'.m := rfl
                    rw [← this]; rw [image.lift_fac (MonoFactorisation.ofIsoComp f F')] } }

Depends on / 依赖: HasImage, HasImage.mk, Image.monoFactorisation, MonoFactorisation, MonoFactorisation.ofIsoComp, image.lift, image.lift_fac, isImage, isoComp, lift_fac, monoFactorisation, ofIsoComp
-/
instance hasImage_iso_comp [IsIso f] [HasImage g] : HasImage (f ≫ g) :=
  HasImage.mk
    { F := (Image.monoFactorisation g).isoComp f
      isImage := { lift := fun F' => image.lift (F'.ofIsoComp f)
                   lift_fac := fun F' => by
                    dsimp
                    have : (MonoFactorisation.ofIsoComp f F').m = F'.m := rfl
                    rw [← this]; rw [image.lift_fac (MonoFactorisation.ofIsoComp f F')] } }

/--
Instance `image.isIso_precomp_iso` / 实例 `image.isIso_precomp_iso`

English:
instance image.isIso_precomp_iso
  signature: (f : X ⟶ Y) [IsIso f] [HasImage g]
  body: ⟨⟨image.lift
        { I := image (f ≫ g)
          m := image.ι (f ≫ g)
          e := inv f ≫ factorThruImage (f ≫ g) },
      ⟨by
        ext
        simp [image.preComp], by
        ext
        simp [image.preComp]⟩⟩⟩

中文:
实例 像.isIso_precomp_iso
  签名: (f : X ⟶ Y) [是同构 f] [有像 g]
  定义体: ⟨⟨image.lift
        { I := image (f ≫ g)
          m := image.ι (f ≫ g)
          e := inv f ≫ factorThruImage (f ≫ g) },
      ⟨by
        ext
        simp [image.preComp], by
        ext
        simp [image.preComp]⟩⟩⟩

Depends on / 依赖: factorThruImage, image.lift, image.preComp, preComp
-/
instance image.isIso_precomp_iso (f : X ⟶ Y) [IsIso f] [HasImage g] : IsIso (image.preComp f g) :=
  ⟨⟨image.lift
        { I := image (f ≫ g)
          m := image.ι (f ≫ g)
          e := inv f ≫ factorThruImage (f ≫ g) },
      ⟨by
        ext
        simp [image.preComp], by
        ext
        simp [image.preComp]⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
-- Note that in general we don't have the other comparison map you might expect
-- `image f ⟶ image (f ≫ g)`.
/--
Instance `hasImage_comp_iso` / 实例 `hasImage_comp_iso`

English:
instance hasImage_comp_iso
  signature: [HasImage f] [IsIso g]
  body: HasImage.mk
    { F := (Image.monoFactorisation f).compMono g
      isImage :=
      { lift := fun F' => image.lift F'.ofCompIso
        lift_fac := fun F' => by
          rw [← Category.comp_id (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m)]; rw [← IsIso.inv_hom_id g]; rw [← Category.assoc]
          refine congrArg (· ≫ g) ?_
          have : (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m) ≫ inv g =
            image.lift (MonoFactorisation.ofCompIso F') ≫
            ((MonoFactorisation.ofCompIso F').m) := by
              simp only [Category.assoc,
                MonoFactorisation.ofCompIso_m]
          rw [this]; rw [image.lift_fac (MonoFactorisation.ofCompIso F')]; rw [image.as_ι] } }

中文:
实例 hasImage_comp_iso
  签名: [有像 f] [是同构 g]
  定义体: HasImage.mk
    { F := (Image.monoFactorisation f).compMono g
      isImage :=
      { lift := fun F' => image.lift F'.ofCompIso
        lift_fac := fun F' => by
          rw [← Category.comp_id (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m)]; rw [← IsIso.inv_hom_id g]; rw [← Category.assoc]
          refine congrArg (· ≫ g) ?_
          have : (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m) ≫ inv g =
            image.lift (MonoFactorisation.ofCompIso F') ≫
            ((MonoFactorisation.ofCompIso F').m) := by
              simp only [Category.assoc,
                MonoFactorisation.ofCompIso_m]
          rw [this]; rw [image.lift_fac (MonoFactorisation.ofCompIso F')]; rw [image.as_ι] } }

Depends on / 依赖: Category, Category.assoc, Category.comp_id, HasImage, HasImage.mk, Image.monoFactorisation, IsIso.inv_hom_id, MonoFactorisation, MonoFactorisation.ofCo, MonoFactorisation.ofCompIso, compMono, comp_id, image.lift, inv_hom_id, isImage, lift_fac, monoFactorisation, ofCompIso
-/
instance hasImage_comp_iso [HasImage f] [IsIso g] : HasImage (f ≫ g) :=
  HasImage.mk
    { F := (Image.monoFactorisation f).compMono g
      isImage :=
      { lift := fun F' => image.lift F'.ofCompIso
        lift_fac := fun F' => by
          rw [← Category.comp_id (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m)]; rw [← IsIso.inv_hom_id g]; rw [← Category.assoc]
          refine congrArg (· ≫ g) ?_
          have : (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m) ≫ inv g =
            image.lift (MonoFactorisation.ofCompIso F') ≫
            ((MonoFactorisation.ofCompIso F').m) := by
              simp only [Category.assoc,
                MonoFactorisation.ofCompIso_m]
          rw [this]; rw [image.lift_fac (MonoFactorisation.ofCompIso F')]; rw [image.as_ι] } }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `image.compIso` / `image.compIso` 的定义

English:
definition image.compIso
  signature: [HasImage f] [IsIso g]
  body: image.lift (Image.monoFactorisation (f ≫ g)).ofCompIso
  inv := image.lift ((Image.monoFactorisation f).compMono g)

中文:
定义 像.compIso
  签名: [有像 f] [是同构 g]
  定义体: image.lift (Image.monoFactorisation (f ≫ g)).ofCompIso
  inv := image.lift ((Image.monoFactorisation f).compMono g)

Depends on / 依赖: Image.monoFactorisation, image.lift, monoFactorisation, ofCompIso
-/
def image.compIso [HasImage f] [IsIso g] : image f ≅ image (f ≫ g) where
  hom := image.lift (Image.monoFactorisation (f ≫ g)).ofCompIso
  inv := image.lift ((Image.monoFactorisation f).compMono g)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `image.compIso_hom_comp_image_ι` / 定理 `image.compIso_hom_comp_image_ι`

English:
theorem image.compIso_hom_comp_image_ι
  given: [HasImage f] [IsIso g]
  proof: by
  ext
  simp [image.compIso]

中文:
定理 像.compIso_hom_comp_image_ι
  条件: [有像 f] [是同构 g]
  证明: by
  ext
  simp [image.compIso]

Depends on / 依赖: compIso, image.compIso
-/
theorem image.compIso_hom_comp_image_ι [HasImage f] [IsIso g] :
    (image.compIso f g).hom ≫ image.ι (f ≫ g) = image.ι f ≫ g := by
  ext
  simp [image.compIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `image.compIso_inv_comp_image_ι` / 定理 `image.compIso_inv_comp_image_ι`

English:
theorem image.compIso_inv_comp_image_ι
  given: [HasImage f] [IsIso g]
  proof: by
  ext
  simp [image.compIso]

中文:
定理 像.compIso_inv_comp_image_ι
  条件: [有像 f] [是同构 g]
  证明: by
  ext
  simp [image.compIso]

Depends on / 依赖: compIso, image.compIso
-/
theorem image.compIso_inv_comp_image_ι [HasImage f] [IsIso g] :
    (image.compIso f g).inv ≫ image.ι f = image.ι (f ≫ g) ≫ inv g := by
  ext
  simp [image.compIso]

end

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

instance {X Y : C} (f : X ⟶ Y) [HasImage f] : HasImage (Arrow.mk f).hom :=
inferInstanceAs HasImage f

end

section HasImageMap

/--
Definition of `ImageMap` / `ImageMap` 的定义

English:
structure ImageMap
  parameters: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
  axioms and operations (2):
    - map : image f.hom ⟶ image g.hom
    - map_ι : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right  [default: by aesop]

中文:
结构 像映射
  参数: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] (sq : f ⟶ g)
  公理与运算 (2 个):
    - map : 像 f.hom ⟶ 像 g.hom
    - map_ι : map ≫ 像.ι g.hom = 像.ι f.hom ≫ sq.right  [默认: by aesop]
-/
structure ImageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g) where
  map : image f.hom ⟶ image g.hom
  map_ι : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right := by aesop

attribute [inherit_doc ImageMap] ImageMap.map ImageMap.map_ι

/--
Instance `inhabitedImageMap` / 实例 `inhabitedImageMap`

English:
instance inhabitedImageMap
  signature: {f : Arrow C} [HasImage f.hom]
  body: ⟨⟨𝟙 _, by simp⟩⟩

中文:
实例 inhabitedImageMap
  签名: {f : 箭头 C} [有像 f.hom]
  定义体: ⟨⟨𝟙 _, by simp⟩⟩
-/
instance inhabitedImageMap {f : Arrow C} [HasImage f.hom] : Inhabited (ImageMap (𝟙 f)) :=
  ⟨⟨𝟙 _, by simp⟩⟩

attribute [reassoc (attr := simp)] ImageMap.map_ι

@[reassoc (attr := simp)]
/--
theorem `ImageMap.factor_map` / 定理 `ImageMap.factor_map`

English:
theorem ImageMap.factor_map
  statement: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
  proof: (cancel_mono (image.ι g.hom)).1 by simp

中文:
定理 像映射.factor_map
  结论: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] (sq : f ⟶ g)
  证明: (cancel_mono (image.ι g.hom)).1 by simp

Depends on / 依赖: cancel_mono, g.hom
-/
theorem ImageMap.factor_map {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    (m : ImageMap sq) : factorThruImage f.hom ≫ m.map = sq.left ≫ factorThruImage g.hom :=
(cancel_mono (image.ι g.hom)).1 by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ImageMap.transport` / `ImageMap.transport` 的定义

English:
definition ImageMap.transport
  signature: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
  body: image.lift F ≫ map ≫ hF'.lift (Image.monoFactorisation g.hom)
  map_ι := by simp [map_ι]

中文:
定义 像映射.transport
  签名: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] (sq : f ⟶ g)
  定义体: image.lift F ≫ map ≫ hF'.lift (Image.monoFactorisation g.hom)
  map_ι := by simp [map_ι]

Depends on / 依赖: Image.monoFactorisation, g.hom, image.lift, monoFactorisation
-/
def ImageMap.transport {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    (F : MonoFactorisation f.hom) {F' : MonoFactorisation g.hom} (hF' : IsImage F')
    {map : F.I ⟶ F'.I} (map_ι : map ≫ F'.m = F.m ≫ sq.right) : ImageMap sq where
  map := image.lift F ≫ map ≫ hF'.lift (Image.monoFactorisation g.hom)
  map_ι := by simp [map_ι]

/--
Definition of `HasImageMap` / `HasImageMap` 的定义

English:
class HasImageMap
  parameters: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
  axioms and operations (1):
    - mk' : : has_image_map : Nonempty (ImageMap sq)

中文:
类 有像映射
  参数: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] (sq : f ⟶ g)
  公理与运算 (1 个):
    - mk' : : has_image_map : 非空 (像映射 sq)
-/
class HasImageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g) : Prop where
mk' ::
  has_image_map : Nonempty (ImageMap sq)

attribute [inherit_doc HasImageMap] HasImageMap.has_image_map

/--
theorem `HasImageMap.mk` / 定理 `HasImageMap.mk`

English:
theorem HasImageMap.mk
  statement: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] {sq : f ⟶ g}
  proof: ⟨Nonempty.intro m⟩

中文:
定理 有像映射.mk
  结论: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] {sq : f ⟶ g}
  证明: ⟨Nonempty.intro m⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasImageMap.mk {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] {sq : f ⟶ g}
    (m : ImageMap sq) : HasImageMap sq :=
  ⟨Nonempty.intro m⟩

/--
theorem `HasImageMap.transport` / 定理 `HasImageMap.transport`

English:
theorem HasImageMap.transport
  statement: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
  proof: HasImageMap.mk ImageMap.transport sq F hF' map_ι

中文:
定理 有像映射.transport
  结论: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] (sq : f ⟶ g)
  证明: HasImageMap.mk ImageMap.transport sq F hF' map_ι

Depends on / 依赖: HasImageMap, HasImageMap.mk, ImageMap, ImageMap.transport, transport
-/
theorem HasImageMap.transport {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    (F : MonoFactorisation f.hom) {F' : MonoFactorisation g.hom} (hF' : IsImage F')
    (map : F.I ⟶ F'.I) (map_ι : map ≫ F'.m = F.m ≫ sq.right) : HasImageMap sq :=
HasImageMap.mk ImageMap.transport sq F hF' map_ι

/--
Definition of `HasImageMap.imageMap` / `HasImageMap.imageMap` 的定义

English:
definition HasImageMap.imageMap
  signature: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
  body: Classical.choice @HasImageMap.has_image_map _ _ _ _ _ _ sq _

中文:
定义 有像映射.imageMap
  签名: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] (sq : f ⟶ g)
  定义体: Classical.choice @HasImageMap.has_image_map _ _ _ _ _ _ sq _

Depends on / 依赖: Classical, Classical.choice, HasImageMap, HasImageMap.has_image_map, choice, has_image_map
-/
def HasImageMap.imageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    [HasImageMap sq] : ImageMap sq :=
Classical.choice @HasImageMap.has_image_map _ _ _ _ _ _ sq _

-- see Note [lower instance priority]
instance (priority := 100) hasImageMapOfIsIso {f g : Arrow C} [HasImage f.hom] [HasImage g.hom]
    (sq : f ⟶ g) [IsIso sq] : HasImageMap sq :=
  HasImageMap.mk
    { map := image.lift ((Image.monoFactorisation g.hom).ofArrowIso (inv sq))
      map_ι := by
        erw [← cancel_mono (inv sq).right, Category.assoc, ← MonoFactorisation.ofArrowIso_m,
          image.lift_fac, Category.assoc, ← Comma.comp_right, IsIso.hom_inv_id, Comma.id_right,
          Category.comp_id] }

/--
Instance `HasImageMap.comp` / 实例 `HasImageMap.comp`

English:
instance HasImageMap.comp
  signature: {f g h : Arrow C} [HasImage f.hom] [HasImage g.hom] [HasImage h.hom]
  body: HasImageMap.mk
    { map := (HasImageMap.imageMap sq1).map ≫ (HasImageMap.imageMap sq2).map
      map_ι := by
        rw [Category.assoc]; rw [ImageMap.map_ι]; rw [ImageMap.map_ι_assoc]; rw [Arrow.comp_right] }

中文:
实例 有像映射.comp
  签名: {f g h : 箭头 C} [有像 f.hom] [有像 g.hom] [有像 h.hom]
  定义体: HasImageMap.mk
    { map := (HasImageMap.imageMap sq1).map ≫ (HasImageMap.imageMap sq2).map
      map_ι := by
        rw [Category.assoc]; rw [ImageMap.map_ι]; rw [ImageMap.map_ι_assoc]; rw [Arrow.comp_right] }

Depends on / 依赖: Arrow.comp_right, Category, Category.assoc, HasImageMap, HasImageMap.imageMap, HasImageMap.mk, ImageMap, ImageMap.map_, comp_right, imageMap
-/
instance HasImageMap.comp {f g h : Arrow C} [HasImage f.hom] [HasImage g.hom] [HasImage h.hom]
    (sq1 : f ⟶ g) (sq2 : g ⟶ h) [HasImageMap sq1] [HasImageMap sq2] : HasImageMap (sq1 ≫ sq2) :=
  HasImageMap.mk
    { map := (HasImageMap.imageMap sq1).map ≫ (HasImageMap.imageMap sq2).map
      map_ι := by
        rw [Category.assoc]; rw [ImageMap.map_ι]; rw [ImageMap.map_ι_assoc]; rw [Arrow.comp_right] }

variable {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)

section

attribute [local ext] ImageMap

/--
theorem `ImageMap.map_uniq_aux` / 定理 `ImageMap.map_uniq_aux`

English:
theorem ImageMap.map_uniq_aux
  statement: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] {sq : f ⟶ g}
  proof: by
  have : map ≫ image.ι g.hom = map' ≫ image.ι g.hom := by rw [map_ι, map_ι']
  apply (cancel_mono (image.ι g.hom)).1 this

中文:
定理 像映射.map_uniq_aux
  结论: {f g : 箭头 C} [有像 f.hom] [有像 g.hom] {sq : f ⟶ g}
  证明: by
  have : map ≫ image.ι g.hom = map' ≫ image.ι g.hom := by rw [map_ι, map_ι']
  apply (cancel_mono (image.ι g.hom)).1 this

Depends on / 依赖: cancel_mono, cat_disch, f.hom, g.hom, sq.right
-/
theorem ImageMap.map_uniq_aux {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] {sq : f ⟶ g}
    (map : image f.hom ⟶ image g.hom)
    (map_ι : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right := by cat_disch)
    (map' : image f.hom ⟶ image g.hom)
    (map_ι' : map' ≫ image.ι g.hom = image.ι f.hom ≫ sq.right) : (map = map') := by
  have : map ≫ image.ι g.hom = map' ≫ image.ι g.hom := by rw [map_ι, map_ι']
  apply (cancel_mono (image.ι g.hom)).1 this

/--
theorem `ImageMap.map_uniq` / 定理 `ImageMap.map_uniq`

English:
theorem ImageMap.map_uniq
  statement: {f g : Arrow C} [HasImage f.hom] [HasImage g.hom]
  proof: by
  apply ImageMap.map_uniq_aux _ F.map_ι _ G.map_ι

@[deprecated (since := "2026-04-08")]
alias ImageMap.mk.injEq' := ImageMap.mk.injEq

中文:
定理 像映射.map_uniq
  结论: {f g : 箭头 C} [有像 f.hom] [有像 g.hom]
  证明: by
  apply ImageMap.map_uniq_aux _ F.map_ι _ G.map_ι

@[deprecated (since := "2026-04-08")]
alias ImageMap.mk.injEq' := ImageMap.mk.injEq

Depends on / 依赖: F.map_, G.map_, ImageMap, ImageMap.map_uniq_aux, map_uniq_aux
-/
theorem ImageMap.map_uniq {f g : Arrow C} [HasImage f.hom] [HasImage g.hom]
    {sq : f ⟶ g} (F G : ImageMap sq) : F.map = G.map := by
  apply ImageMap.map_uniq_aux _ F.map_ι _ G.map_ι

@[deprecated (since := "2026-04-08")]
alias ImageMap.mk.injEq' := ImageMap.mk.injEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (ImageMap sq)
  body: Subsingleton.intro fun a b =>
ImageMap.ext ImageMap.map_uniq a b

中文:
实例 :
  签名: 子单例 (像映射 sq)
  定义体: Subsingleton.intro fun a b =>
ImageMap.ext ImageMap.map_uniq a b

Depends on / 依赖: ImageMap, ImageMap.ext, ImageMap.map_uniq, Subsingleton, Subsingleton.intro, map_uniq
-/
instance : Subsingleton (ImageMap sq) :=
  Subsingleton.intro fun a b =>
ImageMap.ext ImageMap.map_uniq a b

end

variable [HasImageMap sq]

/--
Definition of `image.map` / `image.map` 的定义

English:
abbreviation image.map
  signature: : image f.hom ⟶ image g.hom
  body: (HasImageMap.imageMap sq).map

中文:
缩写 像.map
  签名: : 像 f.hom ⟶ 像 g.hom
  定义体: (HasImageMap.imageMap sq).map

Depends on / 依赖: HasImageMap, HasImageMap.imageMap, imageMap
-/
abbrev image.map : image f.hom ⟶ image g.hom :=
  (HasImageMap.imageMap sq).map

/--
theorem `image.factor_map` / 定理 `image.factor_map`

English:
theorem image.factor_map
  proof: by simp

中文:
定理 像.factor_map
  证明: by simp
-/
theorem image.factor_map :
    factorThruImage f.hom ≫ image.map sq = sq.left ≫ factorThruImage g.hom := by simp

/--
theorem `image.map_ι` / 定理 `image.map_ι`

English:
theorem image.map_ι
  statement: image.map sq ≫ image.ι g.hom = image.ι f.hom ≫ sq.right
  proof: by simp

中文:
定理 像.map_ι
  结论: 像.map sq ≫ 像.ι g.hom = 像.ι f.hom ≫ sq.right
  证明: by simp
-/
theorem image.map_ι : image.map sq ≫ image.ι g.hom = image.ι f.hom ≫ sq.right := by simp

/--
theorem `image.map_homMk'_ι` / 定理 `image.map_homMk'_ι`

English:
theorem image.map_homMk'_ι
  statement: {X Y P Q : C} {k : X ⟶ Y} [HasImage k] {l : P ⟶ Q} [HasImage l]
  proof: image.map_ι _

中文:
定理 像.map_homMk'_ι
  结论: {X Y P Q : C} {k : X ⟶ Y} [有像 k] {l : P ⟶ Q} [有像 l]
  证明: image.map_ι _

Depends on / 依赖: F.obj, Iso.refl, NatIso, NatIso.ofComponents, evaluation, image.map_, ofComponents, preservesColimitsOfShape_of_evaluation, preservesColimitsOfShape_of_natIso, tensorLeft, this.symm
-/
theorem image.map_homMk'_ι {X Y P Q : C} {k : X ⟶ Y} [HasImage k] {l : P ⟶ Q} [HasImage l]
    {m : X ⟶ P} {n : Y ⟶ Q} (w : m ≫ l = k ≫ n) [HasImageMap (Arrow.homMk' _ _ w)] :
    image.map (Arrow.homMk' _ _ w) ≫ image.ι l = image.ι k ≫ n :=
  image.map_ι _

section

variable {h : Arrow C} [HasImage h.hom] (sq' : g ⟶ h)
variable [HasImageMap sq']

/--
Definition of `imageMapComp` / `imageMapComp` 的定义

English:
definition imageMapComp
  signature: : ImageMap (sq ≫ sq') where map
  body: image.map sq ≫ image.map sq'

@[simp]

中文:
定义 imageMapComp
  签名: : 像映射 (sq ≫ sq') where map
  定义体: image.map sq ≫ image.map sq'

@[simp]

Depends on / 依赖: image.map
-/
def imageMapComp : ImageMap (sq ≫ sq') where map := image.map sq ≫ image.map sq'

@[simp]
/--
theorem `image.map_comp` / 定理 `image.map_comp`

English:
theorem image.map_comp
  given: [HasImageMap (sq ≫ sq')]
  proof: show (HasImageMap.imageMap (sq ≫ sq')).map = (imageMapComp sq sq').map by
    congr; simp only [eq_iff_true_of_subsingleton]

中文:
定理 像.map_comp
  条件: [有像映射 (sq ≫ sq')]
  证明: show (HasImageMap.imageMap (sq ≫ sq')).map = (imageMapComp sq sq').map by
    congr; simp only [eq_iff_true_of_subsingleton]

Depends on / 依赖: HasImageMap, HasImageMap.imageMap, eq_iff_true_of_subsingleton, imageMap, imageMapComp
-/
theorem image.map_comp [HasImageMap (sq ≫ sq')] :
    image.map (sq ≫ sq') = image.map sq ≫ image.map sq' :=
  show (HasImageMap.imageMap (sq ≫ sq')).map = (imageMapComp sq sq').map by
    congr; simp only [eq_iff_true_of_subsingleton]

end

section

variable (f)

/--
Definition of `imageMapId` / `imageMapId` 的定义

English:
definition imageMapId
  signature: : ImageMap (𝟙 f) where map
  body: 𝟙 (image f.hom)

@[simp]

中文:
定义 imageMapId
  签名: : 像映射 (𝟙 f) where map
  定义体: 𝟙 (image f.hom)

@[simp]

Depends on / 依赖: f.hom
-/
def imageMapId : ImageMap (𝟙 f) where map := 𝟙 (image f.hom)

@[simp]
/--
theorem `image.map_id` / 定理 `image.map_id`

English:
theorem image.map_id
  given: [HasImageMap (𝟙 f)]
  statement: image.map (𝟙 f) = 𝟙 (image f.hom)
  proof: show (HasImageMap.imageMap (𝟙 f)).map = (imageMapId f).map by
    congr; simp only [eq_iff_true_of_subsingleton]

中文:
定理 像.map_id
  条件: [有像映射 (𝟙 f)]
  结论: 像.map (𝟙 f) = 𝟙 (像 f.hom)
  证明: show (HasImageMap.imageMap (𝟙 f)).map = (imageMapId f).map by
    congr; simp only [eq_iff_true_of_subsingleton]

Depends on / 依赖: HasImageMap, HasImageMap.imageMap, eq_iff_true_of_subsingleton, imageMap, imageMapId
-/
theorem image.map_id [HasImageMap (𝟙 f)] : image.map (𝟙 f) = 𝟙 (image f.hom) :=
  show (HasImageMap.imageMap (𝟙 f)).map = (imageMapId f).map by
    congr; simp only [eq_iff_true_of_subsingleton]

end

end HasImageMap

section

variable (C) [HasImages C]

/--
Definition of `HasImageMaps` / `HasImageMaps` 的定义

English:
class HasImageMaps
  parameters: : Prop where
  axioms and operations (1):
    - has_image_map : forall {f g : Arrow C} (st : f ⟶ g), HasImageMap st

中文:
类 有ImageMaps
  参数: : 命题 where
  公理与运算 (1 个):
    - has_image_map : 对任意 {f g : 箭头 C} (st : f ⟶ g), 有像映射 st
-/
class HasImageMaps : Prop where
  has_image_map : forall {f g : Arrow C} (st : f ⟶ g), HasImageMap st

attribute [instance 100] HasImageMaps.has_image_map

end

section HasImageMaps

variable [HasImages C] [HasImageMaps C]

/-- The functor from the arrow category of `C` to `C` itself that maps a morphism to its image
and a commutative square to the induced morphism on images. -/
@[simps]
/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: : Arrow C ⥤ C where
  body: image f.hom
  map st := image.map st

中文:
定义 im
  签名: : 箭头 C ⥤ C where
  定义体: image f.hom
  map st := image.map st

Depends on / 依赖: f.hom
-/
def im : Arrow C ⥤ C where
  obj f := image f.hom
  map st := image.map st

end HasImageMaps

section StrongEpiMonoFactorisation

/--
Definition of `StrongEpiMonoFactorisation` / `StrongEpiMonoFactorisation` 的定义

English:
structure StrongEpiMonoFactorisation
  parameters: {X Y : C} (f : X ⟶ Y)
  extends: MonoFactorisation f
  axioms and operations (1):
    - [e_strong_epi : StrongEpi e]

中文:
结构 StrongEpiMonoFactorisation
  参数: {X Y : C} (f : X ⟶ Y)
  继承: 单态射分解 f
  公理与运算 (1 个):
    - [e_strong_epi : 强满态射 e]
-/
structure StrongEpiMonoFactorisation {X Y : C} (f : X ⟶ Y) extends MonoFactorisation f where
  [e_strong_epi : StrongEpi e]

attribute [inherit_doc StrongEpiMonoFactorisation] StrongEpiMonoFactorisation.e_strong_epi

attribute [instance] StrongEpiMonoFactorisation.e_strong_epi

/--
Instance `strongEpiMonoFactorisationInhabited` / 实例 `strongEpiMonoFactorisationInhabited`

English:
instance strongEpiMonoFactorisationInhabited
  signature: {X Y : C} (f : X ⟶ Y) [StrongEpi f]
  body: ⟨⟨⟨Y, 𝟙 Y, f, by simp⟩⟩⟩

中文:
实例 strongEpiMonoFactorisationInhabited
  签名: {X Y : C} (f : X ⟶ Y) [强满态射 f]
  定义体: ⟨⟨⟨Y, 𝟙 Y, f, by simp⟩⟩⟩
-/
instance strongEpiMonoFactorisationInhabited {X Y : C} (f : X ⟶ Y) [StrongEpi f] :
    Inhabited (StrongEpiMonoFactorisation f) :=
  ⟨⟨⟨Y, 𝟙 Y, f, by simp⟩⟩⟩

/--
Definition of `StrongEpiMonoFactorisation.toMonoIsImage` / `StrongEpiMonoFactorisation.toMonoIsImage` 的定义

English:
definition StrongEpiMonoFactorisation.toMonoIsImage
  signature: {X Y : C} {f : X ⟶ Y}
  body: (CommSq.mk (show G.e ≫ G.m = F.e ≫ F.m by rw [F.toMonoFactorisation.fac, G.fac])).lift

中文:
定义 StrongEpiMonoFactorisation.toMonoIsImage
  签名: {X Y : C} {f : X ⟶ Y}
  定义体: (CommSq.mk (show G.e ≫ G.m = F.e ≫ F.m by rw [F.toMonoFactorisation.fac, G.fac])).lift

Depends on / 依赖: CommSq, CommSq.mk, F.toMonoFactorisation.fac, G.fac, toMonoFactorisation
-/
def StrongEpiMonoFactorisation.toMonoIsImage {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) : IsImage F.toMonoFactorisation where
  lift G :=
    (CommSq.mk (show G.e ≫ G.m = F.e ≫ F.m by rw [F.toMonoFactorisation.fac, G.fac])).lift

variable (C)

/--
Definition of `HasStrongEpiMonoFactorisations` / `HasStrongEpiMonoFactorisations` 的定义

English:
class HasStrongEpiMonoFactorisations
  parameters: : Prop where mk' ::
  (no additional axioms)

中文:
类 有StrongEpiMonoFactorisations
  参数: : 命题 where mk' ::
  (无附加公理)
-/
class HasStrongEpiMonoFactorisations : Prop where mk' ::
  has_fac : forall {X Y : C} (f : X ⟶ Y), Nonempty (StrongEpiMonoFactorisation f)

attribute [inherit_doc HasStrongEpiMonoFactorisations] HasStrongEpiMonoFactorisations.has_fac

variable {C}

/--
theorem `HasStrongEpiMonoFactorisations.mk` / 定理 `HasStrongEpiMonoFactorisations.mk`

English:
theorem HasStrongEpiMonoFactorisations.mk
  proof: ⟨fun f => Nonempty.intro d f⟩

中文:
定理 有StrongEpiMonoFactorisations.mk
  证明: ⟨fun f => Nonempty.intro d f⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasStrongEpiMonoFactorisations.mk
    (d : forall {X Y : C} (f : X ⟶ Y), StrongEpiMonoFactorisation f) :
    HasStrongEpiMonoFactorisations C :=
⟨fun f => Nonempty.intro d f⟩

instance (priority := 100) hasImages_of_hasStrongEpiMonoFactorisations
    [HasStrongEpiMonoFactorisations C] : HasImages C where
  has_image f :=
    let F' := Classical.choice (HasStrongEpiMonoFactorisations.has_fac f)
    HasImage.mk
      { F := F'.toMonoFactorisation
        isImage := F'.toMonoIsImage }

end StrongEpiMonoFactorisation

section HasStrongEpiImages

variable (C) [HasImages C]

/--
Definition of `HasStrongEpiImages` / `HasStrongEpiImages` 的定义

English:
class HasStrongEpiImages
  parameters: : Prop where
  axioms and operations (1):
    - strong_factorThruImage : forall {X Y : C} (f : X ⟶ Y), StrongEpi (factorThruImage f)

中文:
类 有StrongEpiImages
  参数: : 命题 where
  公理与运算 (1 个):
    - strong_factorThruImage : 对任意 {X Y : C} (f : X ⟶ Y), 强满态射 (factorThruImage f)
-/
class HasStrongEpiImages : Prop where
  strong_factorThruImage : forall {X Y : C} (f : X ⟶ Y), StrongEpi (factorThruImage f)

attribute [instance] HasStrongEpiImages.strong_factorThruImage

end HasStrongEpiImages

section HasStrongEpiImages

/--
theorem `strongEpi_of_strongEpiMonoFactorisation` / 定理 `strongEpi_of_strongEpiMonoFactorisation`

English:
theorem strongEpi_of_strongEpiMonoFactorisation
  statement: {X Y : C} {f : X ⟶ Y}
  proof: by
  rw [← IsImage.e_isoExt_hom F.toMonoIsImage hF']
  apply strongEpi_comp

中文:
定理 strongEpi_of_strongEpiMonoFactorisation
  结论: {X Y : C} {f : X ⟶ Y}
  证明: by
  rw [← IsImage.e_isoExt_hom F.toMonoIsImage hF']
  apply strongEpi_comp

Depends on / 依赖: F.toMonoIsImage, IsImage, IsImage.e_isoExt_hom, e_isoExt_hom, strongEpi_comp, toMonoIsImage
-/
theorem strongEpi_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) {F' : MonoFactorisation f} (hF' : IsImage F') :
    StrongEpi F'.e := by
  rw [← IsImage.e_isoExt_hom F.toMonoIsImage hF']
  apply strongEpi_comp

/--
theorem `strongEpi_factorThruImage_of_strongEpiMonoFactorisation` / 定理 `strongEpi_factorThruImage_of_strongEpiMonoFactorisation`

English:
theorem strongEpi_factorThruImage_of_strongEpiMonoFactorisation
  statement: {X Y : C} {f : X ⟶ Y} [HasImage f]
  proof: strongEpi_of_strongEpiMonoFactorisation F Image.isImage f

中文:
定理 strongEpi_factorThruImage_of_strongEpiMonoFactorisation
  结论: {X Y : C} {f : X ⟶ Y} [有像 f]
  证明: strongEpi_of_strongEpiMonoFactorisation F Image.isImage f

Depends on / 依赖: Image.isImage, isImage, strongEpi_of_strongEpiMonoFactorisation
-/
theorem strongEpi_factorThruImage_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y} [HasImage f]
    (F : StrongEpiMonoFactorisation f) : StrongEpi (factorThruImage f) :=
strongEpi_of_strongEpiMonoFactorisation F Image.isImage f

/-- If we constructed our images from strong epi-mono factorisations, then these images are
strong epi images. -/
instance (priority := 100) hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
    [HasStrongEpiMonoFactorisations C] : HasStrongEpiImages C where
  strong_factorThruImage f :=
strongEpi_factorThruImage_of_strongEpiMonoFactorisation
Classical.choice HasStrongEpiMonoFactorisations.has_fac f

end HasStrongEpiImages

section HasStrongEpiImages

variable [HasImages C]

/-- A category with strong epi images has image maps. -/
instance (priority := 100) hasImageMapsOfHasStrongEpiImages [HasStrongEpiImages C] :
    HasImageMaps C where
  has_image_map {f} {g} st :=
    HasImageMap.mk
      { map :=
          (CommSq.mk
              (show
                (st.left ≫ factorThruImage g.hom) ≫ image.ι g.hom =
                  factorThruImage f.hom ≫ image.ι f.hom ≫ st.right
                by simp)).lift }

set_option backward.isDefEq.respectTransparency false in
/-- If a category has images, equalizers and pullbacks, then images are automatically strong epi
images. -/
instance (priority := 100) hasStrongEpiImages_of_hasPullbacks_of_hasEqualizers [HasPullbacks C]
    [HasEqualizers C] : HasStrongEpiImages C where
  strong_factorThruImage f :=
    StrongEpi.mk' fun {A} {B} h h_mono x y sq =>
      CommSq.HasLift.mk'
        { l :=
            image.lift
                { I := pullback h y
                  m := pullback.snd h y ≫ image.ι f
                  m_mono := mono_comp _ _
                  e := pullback.lift _ _ sq.w } ≫
              pullback.fst h y
          fac_left := by simp only [image.fac_lift_assoc, pullback.lift_fst]
          fac_right := by
            apply image.ext
            simp only [sq.w, Category.assoc, image.fac_lift_assoc, pullback.lift_fst_assoc] }

end HasStrongEpiImages

variable [HasStrongEpiMonoFactorisations C]
variable {X Y : C} {f : X ⟶ Y}

/--
Definition of `image.isoStrongEpiMono` / `image.isoStrongEpiMono` 的定义

English:
definition image.isoStrongEpiMono
  signature: {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [StrongEpi e]
  body: let F : StrongEpiMonoFactorisation f := { I := I', m := m, e := e }
IsImage.isoExt F.toMonoIsImage Image.isImage f

中文:
定义 像.isoStrongEpiMono
  签名: {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [强满态射 e]
  定义体: let F : StrongEpiMonoFactorisation f := { I := I', m := m, e := e }
IsImage.isoExt F.toMonoIsImage Image.isImage f

Depends on / 依赖: F.toMonoIsImage, Image.isImage, IsImage, IsImage.isoExt, StrongEpiMonoFactorisation, isImage, isoExt, toMonoIsImage
-/
def image.isoStrongEpiMono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [StrongEpi e]
    [Mono m] : I' ≅ image f :=
  let F : StrongEpiMonoFactorisation f := { I := I', m := m, e := e }
IsImage.isoExt F.toMonoIsImage Image.isImage f

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `image.isoStrongEpiMono_hom_comp_ι` / 定理 `image.isoStrongEpiMono_hom_comp_ι`

English:
theorem image.isoStrongEpiMono_hom_comp_ι
  statement: {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
  proof: by
  dsimp [isoStrongEpiMono]
  apply IsImage.lift_fac

@[simp]

中文:
定理 像.isoStrongEpiMono_hom_comp_ι
  结论: {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
  证明: by
  dsimp [isoStrongEpiMono]
  apply IsImage.lift_fac

@[simp]

Depends on / 依赖: IsImage, IsImage.lift_fac, isoStrongEpiMono, lift_fac
-/
theorem image.isoStrongEpiMono_hom_comp_ι {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] : (image.isoStrongEpiMono e m comm).hom ≫ image.ι f = m := by
  dsimp [isoStrongEpiMono]
  apply IsImage.lift_fac

@[simp]
/--
theorem `image.isoStrongEpiMono_inv_comp_mono` / 定理 `image.isoStrongEpiMono_inv_comp_mono`

English:
theorem image.isoStrongEpiMono_inv_comp_mono
  statement: {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
  proof: image.lift_fac _

中文:
定理 像.isoStrongEpiMono_inv_comp_mono
  结论: {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
  证明: image.lift_fac _

Depends on / 依赖: image.lift_fac, lift_fac
-/
theorem image.isoStrongEpiMono_inv_comp_mono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] : (image.isoStrongEpiMono e m comm).inv ≫ m = image.ι f :=
  image.lift_fac _

open MorphismProperty

variable (C)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorialEpiMonoFactorizationData` / `functorialEpiMonoFactorizationData` 的定义

English:
definition functorialEpiMonoFactorizationData
  signature: :
  body: im
  i := { app := fun f => factorThruImage f.hom }
  p := { app := fun f => image.ι f.hom }
  hi _ := epimorphisms.infer_property _
  hp _ := monomorphisms.infer_property _

中文:
定义 functorialEpiMonoFactorizationData
  签名: :
  定义体: im
  i := { app := fun f => factorThruImage f.hom }
  p := { app := fun f => image.ι f.hom }
  hi _ := epimorphisms.infer_property _
  hp _ := monomorphisms.infer_property _
-/
noncomputable def functorialEpiMonoFactorizationData :
    FunctorialFactorizationData (epimorphisms C) (monomorphisms C) where
  Z := im
  i := { app := fun f => factorThruImage f.hom }
  p := { app := fun f => image.ι f.hom }
  hi _ := epimorphisms.infer_property _
  hp _ := monomorphisms.infer_property _

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasStrongEpiMonoFactorisations_imp_of_isEquivalence` / 定理 `hasStrongEpiMonoFactorisations_imp_of_isEquivalence`

English:
theorem hasStrongEpiMonoFactorisations_imp_of_isEquivalence
  statement: (F : C ⥤ D) [IsEquivalence F]
  proof: ⟨fun {X} {Y} f => by
    let em : StrongEpiMonoFactorisation (F.inv.map f) :=
      (HasStrongEpiMonoFactorisations.has_fac (F.inv.map f)).some
    have : Mono (F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y) := mono_comp _ _
    have : StrongEpi (F.asEquivalence.counitIso.inv.app X ≫ F.map em.e) := strongEpi_comp _ _
    exact
      Nonempty.intro
        { I := F.obj em.I
          e := F.asEquivalence.counitIso.inv.app X ≫ F.map em.e
          m := F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y
          fac := by
            simp only [Category.assoc, ← F.map_comp_assoc,
              MonoFactorisation.fac, fun_inv_map, id_obj, Iso.inv_hom_id_app, Category.comp_id,
              Iso.inv_hom_id_app_assoc] }⟩

中文:
定理 hasStrongEpiMonoFactorisations_imp_of_isEquivalence
  结论: (F : C ⥤ D) [是等价 F]
  证明: ⟨fun {X} {Y} f => by
    let em : StrongEpiMonoFactorisation (F.inv.map f) :=
      (HasStrongEpiMonoFactorisations.has_fac (F.inv.map f)).some
    have : Mono (F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y) := mono_comp _ _
    have : StrongEpi (F.asEquivalence.counitIso.inv.app X ≫ F.map em.e) := strongEpi_comp _ _
    exact
      Nonempty.intro
        { I := F.obj em.I
          e := F.asEquivalence.counitIso.inv.app X ≫ F.map em.e
          m := F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y
          fac := by
            simp only [Category.assoc, ← F.map_comp_assoc,
              MonoFactorisation.fac, fun_inv_map, id_obj, Iso.inv_hom_id_app, Category.comp_id,
              Iso.inv_hom_id_app_assoc] }⟩

Depends on / 依赖: Category, Category.assoc, F.asEquivalence.counitIso.hom.app, F.asEquivalence.counitIso.inv.app, F.inv.map, F.map, F.map_comp, F.obj, HasStrongEpiMonoFactorisations, HasStrongEpiMonoFactorisations.has_fac, Nonempty, Nonempty.intro, StrongEpi, StrongEpiMonoFactorisation, asEquivalence, counitIso, em.I, em.e, em.m, has_fac
-/
theorem hasStrongEpiMonoFactorisations_imp_of_isEquivalence (F : C ⥤ D) [IsEquivalence F]
    [h : HasStrongEpiMonoFactorisations C] : HasStrongEpiMonoFactorisations D :=
  ⟨fun {X} {Y} f => by
    let em : StrongEpiMonoFactorisation (F.inv.map f) :=
      (HasStrongEpiMonoFactorisations.has_fac (F.inv.map f)).some
    have : Mono (F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y) := mono_comp _ _
    have : StrongEpi (F.asEquivalence.counitIso.inv.app X ≫ F.map em.e) := strongEpi_comp _ _
    exact
      Nonempty.intro
        { I := F.obj em.I
          e := F.asEquivalence.counitIso.inv.app X ≫ F.map em.e
          m := F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y
          fac := by
            simp only [Category.assoc, ← F.map_comp_assoc,
              MonoFactorisation.fac, fun_inv_map, id_obj, Iso.inv_hom_id_app, Category.comp_id,
              Iso.inv_hom_id_app_assoc] }⟩

end CategoryTheory.Functor
