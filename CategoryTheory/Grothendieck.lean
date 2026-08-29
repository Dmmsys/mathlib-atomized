/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj b`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).toFunctor.obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consist again of `β : b ⟶ b'` and `φ : f ⟶ (G.map (op β)).obj f'`.

## Notable constructions

- `Grothendieck F` is the Grothendieck construction.
- Elements of `Grothendieck F` whose base is `c : C` can be transported along `f : c ⟶ d` using
  `transport`.
- A natural transformation `α : F ⟶ G` induces `map α : Grothendieck F ⥤ Grothendieck G`.
- The Grothendieck construction and `map` together form a functor (`functor`) from the functor
  category `E ⥤ Cat` to the over category `Over E`.
- A functor `G : D ⥤ C` induces `pre F G : Grothendieck (G ⋙ F) ⥤ Grothendieck F`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of a functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/

@[expose] public section


universe w u v u₁ v₁ u₂ v₂

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable (F : C ⥤ Cat.{v₂, u₂})

/--
Definition of `Grothendieck` / `Grothendieck` 的定义

English:
structure Grothendieck
  parameters: where
  axioms and operations (2):
    - base : C
    - fiber : F.obj base

中文:
结构 Grothendieck
  参数: where
  公理与运算 (2 个):
    - base : C
    - fiber : F.obj base
-/
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Grothendieck F)
  axioms and operations (2):
    - base : X.base ⟶ Y.base
    - fiber : (F.map base).toFunctor.obj X.fiber ⟶ Y.fiber

中文:
结构 Hom
  参数: (X Y : Grothendieck F)
  公理与运算 (2 个):
    - base : X.base ⟶ Y.base
    - fiber : (F.map base).toFunctor.obj X.fiber ⟶ Y.fiber
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).toFunctor.obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
  proof: by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

中文:
定理 ext
  结论: {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
  证明: by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

Depends on / 依赖: cat_disch, w_base
-/
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : Grothendieck F)
  body: 𝟙 X.base
  fiber := eqToHom (by simp)

中文:
定义 id
  签名: (X : Grothendieck F)
  定义体: 𝟙 X.base
  fiber := eqToHom (by simp)

Depends on / 依赖: X.base
-/
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by simp)

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z)
  body: f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber

中文:
定义 comp
  签名: {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z)
  定义体: f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber

Depends on / 依赖: f.base, g.base
-/
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Grothendieck F)
  body: Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp f g := Grothendieck.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 ((Cat.Hom.toNatIso <| eqToIso (F.map_id Y.base)) ≪≫
        (eqToIso Cat.Hom.id_toFunctor)) f.fiber]
     

中文:
实例 :
  签名: Category (Grothendieck F)
  定义体: Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp f g := Grothendieck.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 ((Cat.Hom.toNatIso <| eqToIso (F.map_id Y.base)) ≪≫
        (eqToIso Cat.Hom.id_toFunctor)) f.fiber]
     

Depends on / 依赖: Grothendieck, Grothendieck.Hom
-/
instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp f g := Grothendieck.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 ((Cat.Hom.toNatIso <| eqToIso (F.map_id Y.base)) ≪≫
        (eqToIso Cat.Hom.id_toFunctor)) f.fiber]
      simp
  id_comp f := by ext <;> simp [comp, id]
  assoc f g h := by
    ext
    · simp [comp]
    · simp [comp, ← NatIso.naturality_2 (Cat.Hom.toNatIso (eqToIso (F.map_comp g.base h.base)) ≪≫
        (eqToIso (Cat.Hom.comp_toFunctor _ _))) f.fiber]

@[simp]
/--
theorem `id_base` / 定理 `id_base`

English:
theorem id_base
  given: (X : Grothendieck F)
  proof: rfl

@[simp]

中文:
定理 id_base
  条件: (X : Grothendieck F)
  证明: rfl

@[simp]
-/
theorem id_base (X : Grothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
/--
theorem `id_fiber` / 定理 `id_fiber`

English:
theorem id_fiber
  given: (X : Grothendieck F)
  proof: rfl

@[simp]

中文:
定理 id_fiber
  条件: (X : Grothendieck F)
  证明: rfl

@[simp]
-/
theorem id_fiber (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by simp) :=
  rfl

@[simp]
/--
theorem `comp_base` / 定理 `comp_base`

English:
theorem comp_base
  given: {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 comp_base
  条件: {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
/--
theorem `comp_fiber` / 定理 `comp_fiber`

English:
theorem comp_fiber
  given: {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_fiber
  条件: {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
      eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber :=
  rfl

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g)
  proof: by
  subst h
  simp

@[simp]

中文:
定理 congr
  条件: {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g)
  证明: by
  subst h
  simp

@[simp]
-/
theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  simp

@[simp]
/--
theorem `base_eqToHom` / 定理 `base_eqToHom`

English:
theorem base_eqToHom
  given: {X Y : Grothendieck F} (h : X = Y)
  proof: by subst h; rfl

@[simp]

中文:
定理 base_eqToHom
  条件: {X Y : Grothendieck F} (h : X = Y)
  证明: by subst h; rfl

@[simp]
-/
theorem base_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by subst h; rfl

@[simp]
/--
theorem `fiber_eqToHom` / 定理 `fiber_eqToHom`

English:
theorem fiber_eqToHom
  given: {X Y : Grothendieck F} (h : X = Y)
  proof: by subst h; rfl

中文:
定理 fiber_eqToHom
  条件: {X Y : Grothendieck F} (h : X = Y)
  证明: by subst h; rfl
-/
theorem fiber_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) := by subst h; rfl

/--
lemma `eqToHom_eq` / 引理 `eqToHom_eq`

English:
lemma eqToHom_eq
  given: {X Y : Grothendieck F} (hF : X = Y)
  proof: by
  subst hF
  rfl

中文:
引理 eqToHom_eq
  条件: {X Y : Grothendieck F} (hF : X = Y)
  证明: by
  subst hF
  rfl

Depends on / 依赖: eqToHom
-/
lemma eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl

section Transport

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element of `Grothendieck F` to a `d`-based element.
-/
@[simps]
/--
Definition of `transport` / `transport` 的定义

English:
definition transport
  signature: (x : Grothendieck F) {c : C} (t : x.base ⟶ c)
  body: ⟨c, (F.map t).toFunctor.obj x.fiber⟩

中文:
定义 transport
  签名: (x : Grothendieck F) {c : C} (t : x.base ⟶ c)
  定义体: ⟨c, (F.map t).toFunctor.obj x.fiber⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.const, F.map, Functor, hasZeroObject, isZero, isZero_zero, toFunctor, toFunctor.obj, x.fiber
-/
def transport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : Grothendieck F :=
  ⟨c, (F.map t).toFunctor.obj x.fiber⟩

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element `x` of `Grothendieck F` to a `d`-based element `x.transport t`.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
@[simps]
/--
Definition of `toTransport` / `toTransport` 的定义

English:
definition toTransport
  signature: (x : Grothendieck F) {c : C} (t : x.base ⟶ c)
  body: ⟨t, 𝟙 _⟩

中文:
定义 toTransport
  签名: (x : Grothendieck F) {c : C} (t : x.base ⟶ c)
  定义体: ⟨t, 𝟙 _⟩
-/
def toTransport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : x ⟶ x.transport t :=
  ⟨t, 𝟙 _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Construct an isomorphism in a Grothendieck construction from isomorphisms in its base and fiber.
-/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base)
  body: ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, (F.map e₁.inv).toFunctor.map e₂.inv ≫ eqToHom (by
    rw [← Cat.Hom.comp_obj]; rw [← F.map_comp]; rw [e₁.hom_inv_id]; rw [F.map_id]; rw [Cat.Hom.id_obj])⟩
  hom_inv_id := Grothendieck.ext _ _ (by simp) (by simp)
  inv_hom_id := Grothendieck.ext _ _ (by simp) (by
  

中文:
定义 isoMk
  签名: {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base)
  定义体: ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, (F.map e₁.inv).toFunctor.map e₂.inv ≫ eqToHom (by
    rw [← Cat.Hom.comp_obj]; rw [← F.map_comp]; rw [e₁.hom_inv_id]; rw [F.map_id]; rw [Cat.Hom.id_obj])⟩
  hom_inv_id := Grothendieck.ext _ _ (by simp) (by simp)
  inv_hom_id := Grothendieck.ext _ _ (by simp) (by
  
-/
def isoMk {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, (F.map e₁.inv).toFunctor.map e₂.inv ≫ eqToHom (by
    rw [← Cat.Hom.comp_obj]; rw [← F.map_comp]; rw [e₁.hom_inv_id]; rw [F.map_id]; rw [Cat.Hom.id_obj])⟩
  hom_inv_id := Grothendieck.ext _ _ (by simp) (by simp)
  inv_hom_id := Grothendieck.ext _ _ (by simp) (by
    have := Functor.congr_hom congr($((F.mapIso e₁).inv_hom_id).toFunctor) e₂.inv
    simp_all)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
If `F : C ⥤ Cat` and `x : Grothendieck F`, then every `C`-isomorphism `α : x.base ≅ c` induces
an isomorphism between `x` and its transport along `α`
-/
@[simps!]
/--
Definition of `transportIso` / `transportIso` 的定义

English:
definition transportIso
  signature: (x : Grothendieck F) {c : C} (α : x.base ≅ c)
  body: (isoMk α (Iso.refl _)).symm

中文:
定义 transportIso
  签名: (x : Grothendieck F) {c : C} (α : x.base ≅ c)
  定义体: (isoMk α (Iso.refl _)).symm

Depends on / 依赖: Iso.refl
-/
def transportIso (x : Grothendieck F) {c : C} (α : x.base ≅ c) :
    x.transport α.hom ≅ x := (isoMk α (Iso.refl _)).symm

end Transport
section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Grothendieck F ⥤ C where
  body: X.1
  map f := f.1

中文:
定义 forget
  签名: : Grothendieck F ⥤ C where
  定义体: X.1
  map f := f.1
-/
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map f := f.1

end

section

variable {G : C ⥤ Cat}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (α : F ⟶ G)
  body: { base := X.base
    fiber := (α.app X.base).toFunctor.obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber }
  -- map_id X := by simp only [id_base, id_fiber, eqToHom_map, eqToHom_tran

中文:
定义 map
  签名: (α : F ⟶ G)
  定义体: { base := X.base
    fiber := (α.app X.base).toFunctor.obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber }
  -- map_id X := by simp only [id_base, id_fiber, eqToHom_map, eqToHom_tran

Depends on / 依赖: X.base, X.fiber, Y.base, eqToHom, f.base, f.fiber, naturality, toFunctor, toFunctor.map, toFunctor.obj, toNatTrans, toNatTrans.app
-/
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X :=
  { base := X.base
    fiber := (α.app X.base).toFunctor.obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber }
  -- map_id X := by simp only [id_base, id_fiber, eqToHom_map, eqToHom_trans]; rfl
  map_comp {X Y Z} f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_fiber, map_comp, ← Cat.Hom.comp_map,
      Functor.congr_hom congr($(α.naturality g.base).toFunctor) f.fiber]
    simp


set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `map_obj` / 定理 `map_obj`

English:
theorem map_obj
  given: {α : F ⟶ G} (X : Grothendieck F)
  proof: rfl

中文:
定理 map_obj
  条件: {α : F ⟶ G} (X : Grothendieck F)
  证明: rfl
-/
theorem map_obj {α : F ⟶ G} (X : Grothendieck F) :
    (Grothendieck.map α).obj X = ⟨X.base, (α.app X.base).toFunctor.obj X.fiber⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y}
  proof: by
    apply Grothendieck.ext _ _ (by simp) (by simp)

中文:
定理 map_map
  条件: {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y}
  证明: by
    apply Grothendieck.ext _ _ (by simp) (by simp)

Depends on / 依赖: Grothendieck, Grothendieck.ext
-/
theorem map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} :
    (Grothendieck.map α).map f =
    ⟨f.base, (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber⟩ := by
    apply Grothendieck.ext _ _ (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `functor_comp_forget` / 定理 `functor_comp_forget`

English:
theorem functor_comp_forget
  given: {α : F ⟶ G}
  proof: rfl

中文:
定理 functor_comp_forget
  条件: {α : F ⟶ G}
  证明: rfl
-/
theorem functor_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_id_eq` / 定理 `map_id_eq`

English:
theorem map_id_eq
  statement: map (𝟙 F) = Functor.id (Grothendieck <| F)
  proof: by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

中文:
定理 map_id_eq
  结论: map (𝟙 F) = Functor.id (Grothendieck <| F)
  证明: by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

Depends on / 依赖: Functor, Functor.ext, fapply, map_map
-/
theorem map_id_eq : map (𝟙 F) = Functor.id (Grothendieck <| F) := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapIdIso` / `mapIdIso` 的定义

English:
definition mapIdIso
  signature: : (map (𝟙 F)).toCatHom ≅ 𝟙 (Cat.of <| Grothendieck <| F)
  body: eqToIso congr(($map_id_eq).toCatHom)

中文:
定义 mapIdIso
  签名: : (map (𝟙 F)).toCatHom ≅ 𝟙 (Cat.of <| Grothendieck <| F)
  定义体: eqToIso congr(($map_id_eq).toCatHom)

Depends on / 依赖: eqToIso, map_id_eq, toCatHom
-/
def mapIdIso : (map (𝟙 F)).toCatHom ≅ 𝟙 (Cat.of <| Grothendieck <| F) :=
  eqToIso congr(($map_id_eq).toCatHom)

variable {H : C ⥤ Cat}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_comp_eq` / 定理 `map_comp_eq`

English:
theorem map_comp_eq
  given: (α : F ⟶ G) (β : G ⟶ H)
  proof: by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, map_obj_fiber, NatTrans.comp_app, Cat.Hom.comp_toFunctor,
      comp_obj, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.comp_map, eqToHom_refl, map_comp,
      eqToHom_map, eqToHom_trans_assoc, Cate

中文:
定理 map_comp_eq
  条件: (α : F ⟶ G) (β : G ⟶ H)
  证明: by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, map_obj_fiber, NatTrans.comp_app, Cat.Hom.comp_toFunctor,
      comp_obj, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.comp_map, eqToHom_refl, map_comp,
      eqToHom_map, eqToHom_trans_assoc, Cate

Depends on / 依赖: Cat.Hom, Cat.Hom.comp_toFunctor, Category, Category.comp_id, Category.id_comp, Functor, Functor.comp_map, Functor.ext, NatTrans, NatTrans.comp_app, comp_app, comp_id, comp_map, comp_obj, comp_toFunctor, eqToHom_app, eqToHom_map, eqToHom_refl, eqToHom_toNatTrans, eqToHom_trans_assoc
-/
theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, map_obj_fiber, NatTrans.comp_app, Cat.Hom.comp_toFunctor,
      comp_obj, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.comp_map, eqToHom_refl, map_comp,
      eqToHom_map, eqToHom_trans_assoc, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapCompIso` / `mapCompIso` 的定义

English:
definition mapCompIso
  signature: (α : F ⟶ G) (β : G ⟶ H)
  body: eqToIso (map_comp_eq α β)

中文:
定义 mapCompIso
  签名: (α : F ⟶ G) (β : G ⟶ H)
  定义体: eqToIso (map_comp_eq α β)

Depends on / 依赖: eqToIso, map_comp_eq
-/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
/--
Definition of `compAsSmallFunctorEquivalenceInverse` / `compAsSmallFunctorEquivalenceInverse` 的定义

English:
definition compAsSmallFunctorEquivalenceInverse
  signature: :
  body: ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

中文:
定义 compAsSmallFunctorEquivalenceInverse
  签名: :
  定义体: ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

Depends on / 依赖: AsSmall, AsSmall.up.obj, X.base, X.fiber
-/
def compAsSmallFunctorEquivalenceInverse :
    Grothendieck F ⥤ Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) where
  obj X := ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
/--
Definition of `compAsSmallFunctorEquivalenceFunctor` / `compAsSmallFunctorEquivalenceFunctor` 的定义

English:
definition compAsSmallFunctorEquivalenceFunctor
  signature: :
  body: ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

中文:
定义 compAsSmallFunctorEquivalenceFunctor
  签名: :
  定义体: ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

Depends on / 依赖: AsSmall, AsSmall.down.obj, X.base, X.fiber
-/
def compAsSmallFunctorEquivalenceFunctor :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ⥤ Grothendieck F where
  obj X := ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Taking the Grothendieck construction on `F ⋙ asSmallFunctor`, where
`asSmallFunctor : Cat ⥤ Cat` is the functor which turns each category into a small category of a
(potentially) larger universe, is equivalent to the Grothendieck construction on `F` itself. -/
@[simps]
/--
Definition of `compAsSmallFunctorEquivalence` / `compAsSmallFunctorEquivalence` 的定义

English:
definition compAsSmallFunctorEquivalence
  signature: :
  body: compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

中文:
定义 compAsSmallFunctorEquivalence
  签名: :
  定义体: compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

Depends on / 依赖: compAsSmallFunctorEquivalenceFunctor
-/
def compAsSmallFunctorEquivalence :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ≌ Grothendieck F where
  functor := compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
/--
Definition of `mapWhiskerRightAsSmallFunctor` / `mapWhiskerRightAsSmallFunctor` 的定义

English:
definition mapWhiskerRightAsSmallFunctor
  signature: (α : F ⟶ G)
  body: NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
        comp_obj, compAsSmallFunctorEquivalenceInverse_obj

中文:
定义 mapWhiskerRightAsSmallFunctor
  签名: (α : F ⟶ G)
  定义体: NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
        comp_obj, compAsSmallFunctorEquivalenceInverse_obj

Depends on / 依赖: Cat.asSmallFunctor_obj, Cat.of_, Functor, Functor.comp_map, Grothendieck, Grothendieck.ext, Iso.refl, Iso.refl_hom, NatIso, NatIso.ofComponents, asSmallFunctor_obj, compAsSmallFunctorE, compAsSmallFunctorEquivalenceFunctor_obj_base, compAsSmallFunctorEquivalenceInverse, compAsSmallFunctorEquivalenceInverse_map_base, compAsSmallFunctorEquivalenceInverse_obj_base, compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse, comp_base, comp_map
-/
def mapWhiskerRightAsSmallFunctor (α : F ⟶ G) :
    map (whiskerRight α Cat.asSmallFunctor.{w}) ≅
    (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙
      (compAsSmallFunctorEquivalence G).inverse :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
        comp_obj, compAsSmallFunctorEquivalenceInverse_obj_base, map_obj_base,
        compAsSmallFunctorEquivalenceFunctor_obj_base, Cat.asSmallFunctor_obj, Cat.of_α,
        Iso.refl_hom, Functor.comp_map, comp_base, id_base,
        compAsSmallFunctorEquivalenceInverse_map_base, map_map_base,
        compAsSmallFunctorEquivalenceFunctor_map_base, Cat.asSmallFunctor_map, toCatHom_toFunctor,
        map_obj_fiber, whiskerRight_app, AsSmall.down_obj, AsSmall.up_obj_down,
        compAsSmallFunctorEquivalenceInverse_obj_fiber,
        compAsSmallFunctorEquivalenceFunctor_obj_fiber, comp_fiber, map_map_fiber, AsSmall.down_map,
        down_comp, eqToHom_down, AsSmall.up_map_down, map_comp, eqToHom_map, id_fiber,
        Category.assoc, eqToHom_trans_assoc, compAsSmallFunctorEquivalenceInverse_map_fiber,
        compAsSmallFunctorEquivalenceFunctor_map_fiber, eqToHom_comp_iff, comp_eqToHom_iff]
        simp only [conj_eqToHom_iff_heq']
        rw [G.map_id]
        simp)

end

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: {E : Cat.{v, u}}
  body: Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F).toCatHom
  map {_ _} α := Over.homMk (X := E) (Grothendieck.map α).toCatHom
    congr($(Grothendieck.functor_comp_forget).toCatHom)
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp

中文:
定义 functor
  签名: {E : Cat.{v, u}}
  定义体: Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F).toCatHom
  map {_ _} α := Over.homMk (X := E) (Grothendieck.map α).toCatHom
    congr($(Grothendieck.functor_comp_forget).toCatHom)
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp
-/
def functor {E : Cat.{v, u}} : (E ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F).toCatHom
  map {_ _} α := Over.homMk (X := E) (Grothendieck.map α).toCatHom
    congr($(Grothendieck.functor_comp_forget).toCatHom)
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
/--
Definition of `grothendieckTypeToCatFunctor` / `grothendieckTypeToCatFunctor` 的定义

English:
definition grothendieckTypeToCatFunctor
  signature: : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  body: ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

中文:
定义 grothendieckTypeToCatFunctor
  签名: : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  定义体: ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩
-/
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
/--
Definition of `grothendieckTypeToCatInverse` / `grothendieckTypeToCatInverse` 的定义

English:
definition grothendieckTypeToCatInverse
  signature: : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  body: ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

中文:
定义 grothendieckTypeToCatInverse
  签名: : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  定义体: ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩
-/
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps!]
/--
Definition of `grothendieckTypeToCat` / `grothendieckTypeToCat` 的定义

English:
definition grothendieckTypeToCat
  signature: : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  body: grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :

中文:
定义 grothendieckTypeToCat
  签名: : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  定义体: grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :

Depends on / 依赖: grothendieckTypeToCatFunctor
-/
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    simp
    rfl

section Pre

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction induces a functor
`Grothendieck (G ⋙ F) ⥤ Grothendieck F`. -/
@[simps, implicit_reducible]
/--
Definition of `pre` / `pre` 的定义

English:
definition pre
  signature: (G : D ⥤ C)
  body: ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

@[simp]

中文:
定义 pre
  签名: (G : D ⥤ C)
  定义体: ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

@[simp]

Depends on / 依赖: G.obj, X.base, X.fiber
-/
def pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

@[simp]
/--
theorem `pre_id` / 定理 `pre_id`

English:
theorem pre_id
  statement: pre F (𝟭 C) = 𝟭 _
  proof: rfl

中文:
定理 pre_id
  结论: pre F (𝟭 C) = 𝟭 _
  证明: rfl
-/
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `preNatIso` / `preNatIso` 的定义

English:
definition preNatIso
  signature: {G H : D ⥤ C} (α : G ≅ H)
  body: NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by fapply Grothendieck.ext <;> simp)

中文:
定义 preNatIso
  签名: {G H : D ⥤ C} (α : G ≅ H)
  定义体: NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by fapply Grothendieck.ext <;> simp)

Depends on / 依赖: G.obj, Grothendieck, Grothendieck.ext, NatIso, NatIso.ofComponents, X.base, X.fiber, fapply, ofComponents, transportIso
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by fapply Grothendieck.ext <;> simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `preInv` / `preInv` 的定义

English:
definition preInv
  signature: (G : D ≌ C)
  body: map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

中文:
定义 preInv
  签名: (G : D ≌ C)
  定义体: map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

Depends on / 依赖: G.counitInv, G.functor, G.inverse, Grothendieck, Grothendieck.pre, counitInv, functor, inverse, whiskerRight
-/
def preInv (G : D ≌ C) : Grothendieck F ⥤ Grothendieck (G.functor ⋙ F) :=
  map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

set_option backward.isDefEq.respectTransparency.types false in
variable {F} in
/--
lemma `pre_comp_map` / 引理 `pre_comp_map`

English:
lemma pre_comp_map
  given: (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H)
  proof: rfl

中文:
引理 pre_comp_map
  条件: (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H)
  证明: rfl
-/
lemma pre_comp_map (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {F} in
/--
lemma `pre_comp_map_assoc` / 引理 `pre_comp_map_assoc`

English:
lemma pre_comp_map_assoc
  statement: (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Category* E]
  proof: rfl

中文:
引理 pre_comp_map_assoc
  结论: (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : 类型} [Category* E]
  证明: rfl
-/
lemma pre_comp_map_assoc (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Category* E]
    (K : Grothendieck H ⥤ E) : pre F G ⋙ map α ⋙ K = map (whiskerLeft G α) ⋙ pre H G ⋙ K := rfl

variable {E : Type*} [Category* E] in
@[simp]
/--
lemma `pre_comp` / 引理 `pre_comp`

English:
lemma pre_comp
  given: (G : D ⥤ C) (H : E ⥤ D)
  statement: pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G
  proof: rfl

中文:
引理 pre_comp
  条件: (G : D ⥤ C) (H : E ⥤ D)
  结论: pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G
  证明: rfl
-/
lemma pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `preUnitIso` / `preUnitIso` 的定义

English:
definition preUnitIso
  signature: (G : D ≌ C)
  body: .symm preNatIso _ G.unitIso.symm

中文:
定义 preUnitIso
  签名: (G : D ≌ C)
  定义体: .symm preNatIso _ G.unitIso.symm
-/
protected def preUnitIso (G : D ≌ C) :
    map (whiskerRight G.unitInv _) ≅ pre (G.functor ⋙ F) (G.functor ⋙ G.inverse) :=
.symm preNatIso _ G.unitIso.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `preEquivalence` / `preEquivalence` 的定义

English:
definition preEquivalence
  signature: (G : D ≌ C)
  body: pre F G.functor
  inverse := preInv F G
  unitIso := by
    refine (eqToIso ?_)
      ≪≫ (Grothendieck.preUnitIso F G |> isoWhiskerLeft (map _))
      ≪≫ (pre_comp_map_assoc G.functor _ _ |> Eq.symm |> eqToIso)
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ ma

中文:
定义 preEquivalence
  签名: (G : D ≌ C)
  定义体: pre F G.functor
  inverse := preInv F G
  unitIso := by
    refine (eqToIso ?_)
      ≪≫ (Grothendieck.preUnitIso F G |> isoWhiskerLeft (map _))
      ≪≫ (pre_comp_map_assoc G.functor _ _ |> Eq.symm |> eqToIso)
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ ma

Depends on / 依赖: G.functor, functor
-/
def preEquivalence (G : D ≌ C) : Grothendieck (G.functor ⋙ F) ≌ Grothendieck F where
  functor := pre F G.functor
  inverse := preInv F G
  unitIso := by
    refine (eqToIso ?_)
      ≪≫ (Grothendieck.preUnitIso F G |> isoWhiskerLeft (map _))
      ≪≫ (pre_comp_map_assoc G.functor _ _ |> Eq.symm |> eqToIso)
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ map _ := map_comp_eq _ _
    congr; ext X
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Functor.id_obj,
      Functor.map_id, NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app, whiskerRight_app,
      Equivalence.counitInv_functor_comp]
.symm counitIso := preNatIso F G.counitIso.symm
  functor_unitIso_comp := by
    intro X
    simp only [preInv, Grothendieck.preUnitIso, pre_id,
      Iso.trans_hom, eqToIso.hom, eqToHom_app, eqToHom_refl, isoWhiskerLeft_hom, NatTrans.comp_app]
    fapply Grothendieck.ext <;> simp [preNatIso, transportIso]

set_option backward.isDefEq.respectTransparency.types false in
variable {F} in
/--
Definition of `mapWhiskerLeftIsoConjPreMap` / `mapWhiskerLeftIsoConjPreMap` 的定义

English:
definition mapWhiskerLeftIsoConjPreMap
  signature: {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F')
  body: (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

中文:
定义 mapWhiskerLeftIsoConjPreMap
  签名: {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F')
  定义体: (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

Depends on / 依赖: Functor, Functor.rightUnitor, isoWhiskerLeft, preEquivalence, rightUnitor, unitIso
-/
def mapWhiskerLeftIsoConjPreMap {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F') :
    map (whiskerLeft G.functor α) ≅
      (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalence F' G).inverse :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

end Pre

section FunctorFrom

variable {E : Type*} [Category* E]

set_option backward.isDefEq.respectTransparency.types false in
variable (F) in
/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendieck
construction. -/
@[simps obj map]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: (c : C)
  body: ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
 

中文:
定义 ι
  签名: (c : C)
  定义体: ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
 
-/
def ι (c : C) : F.obj c ⥤ Grothendieck F where
  obj d := ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
    simp only [eqToHom_comp_iff, Category.assoc, eqToHom_trans_assoc]
    apply Functor.congr_hom congr($(F.map_id _).toFunctor).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `faithful_ι` / 实例 `faithful_ι`

English:
instance faithful_ι
  signature: (c : C)
  body: by
    injection f with _ f
    rwa [cancel_epi] at f

中文:
实例 faithful_ι
  签名: (c : C)
  定义体: by
    injection f with _ f
    rwa [cancel_epi] at f

Depends on / 依赖: cancel_epi, injection
-/
instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
@[simps]
/--
Definition of `ιNatTrans` / `ιNatTrans` 的定义

English:
definition ιNatTrans
  signature: {X Y : C} (f : X ⟶ Y)
  body: ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

中文:
定义 ιNatTrans
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])
-/
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ (F.map f).toFunctor ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

variable (fib : forall c, F.obj c ⥤ E) (hom : forall {c c' : C} (f : c ⟶ c'),
  fib c ⟶ (F.map f).toFunctor ⋙ fib c')
variable (hom_id : forall c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : forall c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct a functor from `Grothendieck F` to another category `E` by providing a family of
functors on the fibers of `Grothendieck F`, a family of natural transformations on morphisms in the
base of `Grothendieck F` and coherence data for this family of natural transformations. -/
@[simps]
/--
Definition of `functorFrom` / `functorFrom` 的定义

English:
definition functorFrom
  signature: : Grothendieck F ⥤ E where
  body: (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

中文:
定义 functorFrom
  签名: : Grothendieck F ⥤ E where
  定义体: (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

Depends on / 依赖: X.base, X.fiber
-/
def functorFrom : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ιCompFunctorFrom` / `ιCompFunctorFrom` 的定义

English:
definition ιCompFunctorFrom
  signature: (c : C)
  body: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

中文:
定义 ιCompFunctorFrom
  签名: (c : C)
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, hom_id, ofComponents
-/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

end FunctorFrom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι F' c`. -/
@[simps!]
/--
Definition of `ιCompMap` / `ιCompMap` 的定义

English:
definition ιCompMap
  signature: {F' : C ⥤ Cat} (α : F ⟶ F') (c : C)
  body: NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [map])

中文:
定义 ιCompMap
  签名: {F' : C ⥤ Cat} (α : F ⟶ F') (c : C)
  定义体: NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [map])

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def ιCompMap {F' : C ⥤ Cat} (α : F ⟶ F') (c : C) : ι F c ⋙ map α ≅ (α.app c).toFunctor ⋙ ι F' c :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [map])

end Grothendieck

end CategoryTheory
