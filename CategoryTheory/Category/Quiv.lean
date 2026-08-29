/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Emily Riehl, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.
-/

@[expose] public section

universe v u v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/--
Definition of `Quiv` / `Quiv` 的定义

English:
definition Quiv
  body: Bundled Quiver.{v, u}

中文:
定义 Quiv
  定义体: Bundled Quiver.{v, u}

Depends on / 依赖: Bundled, Quiver
-/
def Quiv :=
  Bundled Quiver.{v, u}

namespace Quiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Quiv (Type u)
  body: Bundled.α

中文:
实例 :
  签名: CoeSort Quiv (类型u)
  定义体: Bundled.α

Depends on / 依赖: Bundled
-/
instance : CoeSort Quiv (Type u) where coe := Bundled.α

/--
Instance `str'` / 实例 `str'`

English:
instance str'
  signature: (C : Quiv.{v, u})
  body: C.str

中文:
实例 str'
  签名: (C : Quiv.{v, u})
  定义体: C.str

Depends on / 依赖: C.str
-/
instance str' (C : Quiv.{v, u}) : Quiver.{v, u} C :=
  C.str

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (C : Type u) [Quiver.{v} C]
  body: Bundled.of C

中文:
定义 of
  签名: (C : 类型u) [Quiver.{v} C]
  定义体: Bundled.of C

Depends on / 依赖: Bundled, Bundled.of
-/
def of (C : Type u) [Quiver.{v} C] : Quiv.{v, u} :=
  Bundled.of C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Quiv
  body: ⟨Quiv.of (Quiver.Empty PEmpty)⟩

中文:
实例 :
  签名: Inhabited Quiv
  定义体: ⟨Quiv.of (Quiver.Empty PEmpty)⟩

Depends on / 依赖: PEmpty, Quiv.of, Quiver, Quiver.Empty
-/
instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty PEmpty)⟩

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : LargeCategory.{max v u} Quiv.{v, u} where
  body: Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G

中文:
实例 category
  签名: : LargeCategory.{max v u} Quiv.{v, u} where
  定义体: Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G

Depends on / 依赖: Prefunctor
-/
instance category : LargeCategory.{max v u} Quiv.{v, u} where
  Hom C D := Prefunctor C D
  id C := Prefunctor.id C
  comp F G := Prefunctor.comp F G

/-- The forgetful functor from categories to quivers. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Cat.{v, u} ⥤ Quiv.{v, u} where
  body: Quiv.of C
  map F := F.toFunctor.toPrefunctor

中文:
定义 forget
  签名: : Cat.{v, u} ⥤ Quiv.{v, u} where
  定义体: Quiv.of C
  map F := F.toFunctor.toPrefunctor

Depends on / 依赖: Quiv.of
-/
def forget : Cat.{v, u} ⥤ Quiv.{v, u} where
  obj C := Quiv.of C
  map F := F.toFunctor.toPrefunctor

/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  given: (X : Quiv)
  statement: 𝟙 X = 𝟭q X
  proof: rfl

中文:
定理 id_eq_id
  条件: (X : Quiv)
  结论: 𝟙 X = 𝟭q X
  证明: rfl
-/
theorem id_eq_id (X : Quiv) : 𝟙 X = 𝟭q X := rfl

/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  given: {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z)
  statement: F ≫ G = F ⋙q G
  proof: rfl

中文:
定理 comp_eq_comp
  条件: {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z)
  结论: F ≫ G = F ⋙q G
  证明: rfl
-/
theorem comp_eq_comp {X Y Z : Quiv} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙q G := rfl

end Quiv

namespace Prefunctor

/--
Definition of `toQuivHom` / `toQuivHom` 的定义

English:
definition toQuivHom
  signature: {C D : Type u} [Quiver.{v} C] [Quiver.{v} D] (F : C ⥤q D)
  body: F

中文:
定义 toQuivHom
  签名: {C D : 类型u} [Quiver.{v} C] [Quiver.{v} D] (F : C ⥤q D)
  定义体: F
-/
def toQuivHom {C D : Type u} [Quiver.{v} C] [Quiver.{v} D] (F : C ⥤q D) :
    Quiv.of C ⟶ Quiv.of D := F

/--
Definition of `ofQuivHom` / `ofQuivHom` 的定义

English:
definition ofQuivHom
  signature: {C D : Quiv} (F : C ⟶ D)
  body: F

中文:
定义 ofQuivHom
  签名: {C D : Quiv} (F : C ⟶ D)
  定义体: F
-/
def ofQuivHom {C D : Quiv} (F : C ⟶ D) : C ⥤q D := F

/--
theorem `to_ofQuivHom` / 定理 `to_ofQuivHom`

English:
theorem to_ofQuivHom
  given: {C D : Quiv} (F : C ⟶ D)
  statement: toQuivHom (ofQuivHom F) = F
  proof: rfl

中文:
定理 to_ofQuivHom
  条件: {C D : Quiv} (F : C ⟶ D)
  结论: toQuivHom (ofQuivHom F) = F
  证明: rfl
-/
@[simp] theorem to_ofQuivHom {C D : Quiv} (F : C ⟶ D) : toQuivHom (ofQuivHom F) = F := rfl

/--
theorem `of_toQuivHom` / 定理 `of_toQuivHom`

English:
theorem of_toQuivHom
  given: {C D : Type} [Quiver C] [Quiver D] (F : C ⥤q D)
  proof: rfl

中文:
定理 of_toQuivHom
  条件: {C D : Type} [Quiver C] [Quiver D] (F : C ⥤q D)
  证明: rfl
-/
@[simp] theorem of_toQuivHom {C D : Type} [Quiver C] [Quiver D] (F : C ⥤q D) :
    ofQuivHom (toQuivHom F) = F := rfl

end Prefunctor
namespace Cat

/-- A prefunctor `V ⥤q W` induces a functor between the path categories defined by `F.mapPath`. -/
@[simps]
/--
Definition of `freeMap` / `freeMap` 的定义

English:
definition freeMap
  signature: {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)
  body: F.obj
  map := F.mapPath
  map_comp f g := F.mapPath_comp f g

中文:
定义 freeMap
  签名: {V W : 类型} [Quiver V] [Quiver W] (F : V ⥤q W)
  定义体: F.obj
  map := F.mapPath
  map_comp f g := F.mapPath_comp f g

Depends on / 依赖: F.obj
-/
def freeMap {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W) : Paths V ⥤ Paths W where
  obj := F.obj
  map := F.mapPath
  map_comp f g := F.mapPath_comp f g

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `free : Quiv ⥤ Cat` preserves identities up to natural isomorphism and in fact up
to equality. -/
@[simps!]
/--
Definition of `freeMapIdIso` / `freeMapIdIso` 的定义

English:
definition freeMapIdIso
  signature: (V : Type*) [Quiver V]
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 freeMapIdIso
  签名: (V : 类型) [Quiver V]
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def freeMapIdIso (V : Type*) [Quiver V] : freeMap (𝟭q V) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `freeMap_id` / 定理 `freeMap_id`

English:
theorem freeMap_id
  given: (V : Type*) [Quiver V]
  proof: Functor.ext_of_iso (freeMapIdIso V) (fun _ => rfl)

中文:
定理 freeMap_id
  条件: (V : 类型) [Quiver V]
  证明: Functor.ext_of_iso (freeMapIdIso V) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, freeMapIdIso
-/
theorem freeMap_id (V : Type*) [Quiver V] :
    freeMap (𝟭q V) = 𝟭 _ :=
  Functor.ext_of_iso (freeMapIdIso V) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `free : Quiv ⥤ Cat` preserves composition up to natural isomorphism and in fact up
to equality. -/
@[simps!]
/--
Definition of `freeMapCompIso` / `freeMapCompIso` 的定义

English:
definition freeMapCompIso
  signature: {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
  body: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    simp only [Category.comp_id, Category.id_comp, Prefunctor.mapPath_comp_apply])

中文:
定义 freeMapCompIso
  签名: {V₁ : 类型u₁} {V₂ : 类型u₂} {V₃ : 类型u₃}
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    simp only [Category.comp_id, Category.id_comp, Prefunctor.mapPath_comp_apply])

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Iso.refl, NatIso, NatIso.ofComponents, Prefunctor, Prefunctor.mapPath_comp_apply, comp_id, id_comp, mapPath_comp_apply, ofComponents
-/
def freeMapCompIso {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
    [Quiver.{v₁} V₁] [Quiver.{v₂} V₂] [Quiver.{v₃} V₃] (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) :
    freeMap (F ⋙q G) ≅ freeMap F ⋙ freeMap G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    simp only [Category.comp_id, Category.id_comp, Prefunctor.mapPath_comp_apply])

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `freeMap_comp` / 定理 `freeMap_comp`

English:
theorem freeMap_comp
  statement: {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
  proof: Functor.ext_of_iso (freeMapCompIso F G) (fun _ => rfl)

中文:
定理 freeMap_comp
  结论: {V₁ : 类型u₁} {V₂ : 类型u₂} {V₃ : 类型u₃}
  证明: Functor.ext_of_iso (freeMapCompIso F G) (fun _ => rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, freeMapCompIso
-/
theorem freeMap_comp {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
    [Quiver.{v₁} V₁] [Quiver.{v₂} V₂] [Quiver.{v₃} V₃]
    (F : V₁ ⥤q V₂) (G : V₂ ⥤q V₃) :
    freeMap (F ⋙q G) = freeMap F ⋙ freeMap G :=
  Functor.ext_of_iso (freeMapCompIso F G) (fun _ => rfl)

/-- The functor sending each quiver to its path category. -/
@[simps]
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  body: Cat.of (Paths V)
  map F := Functor.toCatHom (freeMap (Prefunctor.ofQuivHom F))
  map_id _ := congr($(freeMap_id _).toCatHom)
  map_comp _ _ := congr($(freeMap_comp _ _).toCatHom)

中文:
定义 free
  签名: : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  定义体: Cat.of (Paths V)
  map F := Functor.toCatHom (freeMap (Prefunctor.ofQuivHom F))
  map_id _ := congr($(freeMap_id _).toCatHom)
  map_comp _ _ := congr($(freeMap_comp _ _).toCatHom)

Depends on / 依赖: Cat.of, SemilatticeInf, hasFiniteLimits_of_semilatticeInf_orderTop
-/
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj V := Cat.of (Paths V)
  map F := Functor.toCatHom (freeMap (Prefunctor.ofQuivHom F))
  map_id _ := congr($(freeMap_id _).toCatHom)
  map_comp _ _ := congr($(freeMap_comp _ _).toCatHom)

end Cat

namespace Quiv

section
variable {V W : Quiv} (e : V ≅ W)

/-- An isomorphism of quivers defines an equivalence on carrier types. -/
@[simps]
/--
Definition of `equivOfIso` / `equivOfIso` 的定义

English:
definition equivOfIso
  signature: : V ≃ W where
  body: e.hom.obj
  invFun := e.inv.obj
  left_inv := Prefunctor.congr_obj e.hom_inv_id
  right_inv := Prefunctor.congr_obj e.inv_hom_id

@[simp]

中文:
定义 equivOfIso
  签名: : V ≃ W where
  定义体: e.hom.obj
  invFun := e.inv.obj
  left_inv := Prefunctor.congr_obj e.hom_inv_id
  right_inv := Prefunctor.congr_obj e.inv_hom_id

@[simp]

Depends on / 依赖: SemilatticeSup, e.hom.obj, hasFiniteColimits_of_semilatticeSup_orderBot
-/
def equivOfIso : V ≃ W where
  toFun := e.hom.obj
  invFun := e.inv.obj
  left_inv := Prefunctor.congr_obj e.hom_inv_id
  right_inv := Prefunctor.congr_obj e.inv_hom_id

@[simp]
/--
lemma `inv_obj_hom_obj_of_iso` / 引理 `inv_obj_hom_obj_of_iso`

English:
lemma inv_obj_hom_obj_of_iso
  given: (X : V)
  statement: e.inv.obj (e.hom.obj X) = X
  proof: (equivOfIso e).left_inv X

@[simp]

中文:
引理 inv_obj_hom_obj_of_iso
  条件: (X : V)
  结论: e.inv.obj (e.hom.obj X) = X
  证明: (equivOfIso e).left_inv X

@[simp]

Depends on / 依赖: equivOfIso, left_inv
-/
lemma inv_obj_hom_obj_of_iso (X : V) : e.inv.obj (e.hom.obj X) = X := (equivOfIso e).left_inv X

@[simp]
/--
lemma `hom_obj_inv_obj_of_iso` / 引理 `hom_obj_inv_obj_of_iso`

English:
lemma hom_obj_inv_obj_of_iso
  given: (Y : W)
  statement: e.hom.obj (e.inv.obj Y) = Y
  proof: (equivOfIso e).right_inv Y

中文:
引理 hom_obj_inv_obj_of_iso
  条件: (Y : W)
  结论: e.hom.obj (e.inv.obj Y) = Y
  证明: (equivOfIso e).right_inv Y

Depends on / 依赖: equivOfIso, right_inv
-/
lemma hom_obj_inv_obj_of_iso (Y : W) : e.hom.obj (e.inv.obj Y) = Y := (equivOfIso e).right_inv Y

/--
lemma `hom_map_inv_map_of_iso` / 引理 `hom_map_inv_map_of_iso`

English:
lemma hom_map_inv_map_of_iso
  given: {V W : Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y)
  proof: by
  rw [← Prefunctor.comp_map]
  exact (Prefunctor.congr_hom e.inv_hom_id.symm f).symm

中文:
引理 hom_map_inv_map_of_iso
  条件: {V W : Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y)
  证明: by
  rw [← Prefunctor.comp_map]
  exact (Prefunctor.congr_hom e.inv_hom_id.symm f).symm

Depends on / 依赖: Prefunctor, Prefunctor.comp_map, Prefunctor.congr_hom, comp_map, congr_hom, e.inv_hom_id.symm, inv_hom_id
-/
lemma hom_map_inv_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : W} (f : X ⟶ Y) :
    e.hom.map (e.inv.map f) = Quiver.homOfEq f (by simp) (by simp) := by
  rw [← Prefunctor.comp_map]
  exact (Prefunctor.congr_hom e.inv_hom_id.symm f).symm

/--
lemma `inv_map_hom_map_of_iso` / 引理 `inv_map_hom_map_of_iso`

English:
lemma inv_map_hom_map_of_iso
  given: {V W : Quiv} (e : V ≅ W) {X Y : V} (f : X ⟶ Y)
  proof: hom_map_inv_map_of_iso e.symm f

中文:
引理 inv_map_hom_map_of_iso
  条件: {V W : Quiv} (e : V ≅ W) {X Y : V} (f : X ⟶ Y)
  证明: hom_map_inv_map_of_iso e.symm f

Depends on / 依赖: e.symm, hom_map_inv_map_of_iso
-/
lemma inv_map_hom_map_of_iso {V W : Quiv} (e : V ≅ W) {X Y : V} (f : X ⟶ Y) :
    e.inv.map (e.hom.map f) = Quiver.homOfEq f (by simp) (by simp) :=
  hom_map_inv_map_of_iso e.symm f

/-- An isomorphism of quivers defines an equivalence on hom types. -/
@[simps]
/--
Definition of `homEquivOfIso` / `homEquivOfIso` 的定义

English:
definition homEquivOfIso
  signature: {V W : Quiv} (e : V ≅ W) {X Y : V}
  body: e.hom.map f
  invFun g := Quiver.homOfEq (e.inv.map g) (by simp) (by simp)
  left_inv f := by simp [inv_map_hom_map_of_iso]
  right_inv g := by simp [hom_map_inv_map_of_iso]

中文:
定义 homEquivOfIso
  签名: {V W : Quiv} (e : V ≅ W) {X Y : V}
  定义体: e.hom.map f
  invFun g := Quiver.homOfEq (e.inv.map g) (by simp) (by simp)
  left_inv f := by simp [inv_map_hom_map_of_iso]
  right_inv g := by simp [hom_map_inv_map_of_iso]

Depends on / 依赖: HasBinaryProducts, HasLimit, OrderTop, SemilatticeInf, e.hom.map, hasBinaryProducts_of_hasLimit_pair, hasFiniteLimits_of_hasFiniteLimits_of_size, infer_instance
-/
def homEquivOfIso {V W : Quiv} (e : V ≅ W) {X Y : V} :
    (X ⟶ Y) ≃ (e.hom.obj X ⟶ e.hom.obj Y) where
  toFun f := e.hom.map f
  invFun g := Quiver.homOfEq (e.inv.map g) (by simp) (by simp)
  left_inv f := by simp [inv_map_hom_map_of_iso]
  right_inv g := by simp [hom_map_inv_map_of_iso]

end

section
variable {V W : Type u} [Quiver V] [Quiver W]
  (e : V ≃ W) (he : forall X Y : V, (X ⟶ Y) ≃ (e X ⟶ e Y))

include he in
@[simp]
/--
lemma `homOfEq_map_homOfEq` / 引理 `homOfEq_map_homOfEq`

English:
lemma homOfEq_map_homOfEq
  statement: {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y')
  proof: by
  subst hX hY hX' hY'
  rfl

中文:
引理 homOfEq_map_homOfEq
  结论: {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y')
  证明: by
  subst hX hY hX' hY'
  rfl
-/
lemma homOfEq_map_homOfEq {X Y : V} (f : X ⟶ Y) {X' Y' : V} (hX : X = X') (hY : Y = Y')
    {X'' Y'' : W} (hX' : e X' = X'') (hY' : e Y' = Y'') :
    Quiver.homOfEq (he _ _ (Quiver.homOfEq f hX hY)) hX' hY' =
      Quiver.homOfEq (he _ _ f) (by rw [hX, hX']) (by rw [hY, hY']) := by
  subst hX hY hX' hY'
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoOfEquiv` / `isoOfEquiv` 的定义

English:
definition isoOfEquiv
  signature: : Quiv.of V ≅ Quiv.of W where
  body: Prefunctor.mk e (he _ _)
  inv :=
    { obj := e.symm
      map {X Y} f := (he _ _).symm (Quiver.homOfEq f (by simp) (by simp)) }
  hom_inv_id := Prefunctor.ext' e.left_inv (fun X Y f => by
    dsimp [Quiv.id_eq_id, Quiv.comp_eq_comp]
    apply (he _ _).injective
    apply Quiver.homOfEq_injective (

中文:
定义 isoOfEquiv
  签名: : Quiv.of V ≅ Quiv.of W where
  定义体: Prefunctor.mk e (he _ _)
  inv :=
    { obj := e.symm
      map {X Y} f := (he _ _).symm (Quiver.homOfEq f (by simp) (by simp)) }
  hom_inv_id := Prefunctor.ext' e.left_inv (fun X Y f => by
    dsimp [Quiv.id_eq_id, Quiv.comp_eq_comp]
    apply (he _ _).injective
    apply Quiver.homOfEq_injective (

Depends on / 依赖: HasBinaryCoproducts, HasColimit, OrderBot, Prefunctor, Prefunctor.mk, SemilatticeSup, hasBinaryCoproducts_of_hasColimit_pair, hasFiniteColimits_of_hasFiniteColimits_of_size, infer_instance
-/
def isoOfEquiv : Quiv.of V ≅ Quiv.of W where
  hom := Prefunctor.mk e (he _ _)
  inv :=
    { obj := e.symm
      map {X Y} f := (he _ _).symm (Quiver.homOfEq f (by simp) (by simp)) }
  hom_inv_id := Prefunctor.ext' e.left_inv (fun X Y f => by
    dsimp [Quiv.id_eq_id, Quiv.comp_eq_comp]
    apply (he _ _).injective
    apply Quiver.homOfEq_injective (X' := e X) (Y' := e Y) (by simp) (by simp)
    simp)
  inv_hom_id := Prefunctor.ext' e.right_inv (by simp [Quiv.id_eq_id, Quiv.comp_eq_comp])

end

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {V : Type u} [Quiver.{v} V] {C : Type u₁} [Category.{v₁} C]
  body: F.obj X
  map f := composePath (F.mapPath f)

中文:
定义 lift
  签名: {V : 类型u} [Quiver.{v} V] {C : 类型u₁} [Category.{v₁} C]
  定义体: F.obj X
  map f := composePath (F.mapPath f)

Depends on / 依赖: F.obj
-/
def lift {V : Type u} [Quiver.{v} V] {C : Type u₁} [Category.{v₁} C]
    (F : Prefunctor V C) : Paths V ⥤ C where
  obj X := F.obj X
  map f := composePath (F.mapPath f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `pathCompositionNaturality` / `pathCompositionNaturality` 的定义

English:
definition pathCompositionNaturality
  signature: {C : Type u} {D : Type u₁}
  body: Paths.liftNatIso (fun _ => Iso.refl _) (by simp)

中文:
定义 pathCompositionNaturality
  签名: {C : 类型u} {D : 类型u₁}
  定义体: Paths.liftNatIso (fun _ => Iso.refl _) (by simp)

Depends on / 依赖: Iso.refl, Paths.liftNatIso, liftNatIso
-/
def pathCompositionNaturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D] (F : C ⥤ D) :
    Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D ≅ pathComposition C ⋙ F :=
  Paths.liftNatIso (fun _ => Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `pathComposition_naturality` / 定理 `pathComposition_naturality`

English:
theorem pathComposition_naturality
  statement: {C : Type u} {D : Type u₁}
  proof: Paths.ext_functor rfl (by simp)

中文:
定理 pathComposition_naturality
  结论: {C : 类型u} {D : 类型u₁}
  证明: Paths.ext_functor rfl (by simp)

Depends on / 依赖: Paths.ext_functor, ext_functor
-/
theorem pathComposition_naturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) : Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D = pathComposition C ⋙ F :=
  Paths.ext_functor rfl (by simp)

/--
lemma `pathsOf_freeMap_toPrefunctor` / 引理 `pathsOf_freeMap_toPrefunctor`

English:
lemma pathsOf_freeMap_toPrefunctor
  proof: rfl

中文:
引理 pathsOf_freeMap_toPrefunctor
  证明: rfl
-/
lemma pathsOf_freeMap_toPrefunctor
    {V : Type u} {W : Type u₁} [Quiver.{v} V] [Quiver.{v₁} W] (F : V ⥤q W) :
    Paths.of V ⋙q (Cat.freeMap F).toPrefunctor = F ⋙q Paths.of W := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `freeMapPathsOfCompPathCompositionIso` / `freeMapPathsOfCompPathCompositionIso` 的定义

English:
definition freeMapPathsOfCompPathCompositionIso
  signature: (V : Type u) [Quiver.{v} V]
  body: Paths.liftNatIso (fun v => Iso.refl _) (by simp)

中文:
定义 freeMapPathsOfCompPathCompositionIso
  签名: (V : 类型u) [Quiver.{v} V]
  定义体: Paths.liftNatIso (fun v => Iso.refl _) (by simp)

Depends on / 依赖: Iso.refl, Paths.liftNatIso, liftNatIso
-/
def freeMapPathsOfCompPathCompositionIso (V : Type u) [Quiver.{v} V] :
    Cat.freeMap (Paths.of V) ⋙ pathComposition (Paths V) ≅ 𝟭 (Paths V) :=
  Paths.liftNatIso (fun v => Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `freeMap_pathsOf_pathComposition` / 引理 `freeMap_pathsOf_pathComposition`

English:
lemma freeMap_pathsOf_pathComposition
  given: (V : Type u) [Quiver.{v} V]
  proof: Paths.ext_functor rfl (by simp)

中文:
引理 freeMap_pathsOf_pathComposition
  条件: (V : 类型u) [Quiver.{v} V]
  证明: Paths.ext_functor rfl (by simp)

Depends on / 依赖: HasLimitsOfSize, hasLimits_of_completeLattice, pathComposition
-/
lemma freeMap_pathsOf_pathComposition (V : Type u) [Quiver.{v} V] :
    Cat.freeMap (Paths.of (V := V)) ⋙ pathComposition (Paths V) = 𝟭 (Paths V) :=
  Paths.ext_functor rfl (by simp)

/--
lemma `pathsOf_pathComposition_toPrefunctor` / 引理 `pathsOf_pathComposition_toPrefunctor`

English:
lemma pathsOf_pathComposition_toPrefunctor
  given: (C : Type u) [Category.{v} C]
  proof: by
  dsimp only [Prefunctor.comp]
  congr
  funext X Y f
  exact Category.id_comp _

中文:
引理 pathsOf_pathComposition_toPrefunctor
  条件: (C : 类型u) [Category.{v} C]
  证明: by
  dsimp only [Prefunctor.comp]
  congr
  funext X Y f
  exact Category.id_comp _

Depends on / 依赖: Category, Category.id_comp, HasColimitsOfSize, Prefunctor, Prefunctor.comp, hasColimits_of_completeLattice, id_comp
-/
lemma pathsOf_pathComposition_toPrefunctor (C : Type u) [Category.{v} C] :
    Paths.of C ⋙q (pathComposition C).toPrefunctor = 𝟭q C := by
  dsimp only [Prefunctor.comp]
  congr
  funext X Y f
  exact Category.id_comp _

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : Cat.free ⊣ Quiv.forget
  body: Adjunction.mkOfUnitCounit {
    unit := { app _ := Paths.of _}
    counit := {
      app C := (pathComposition C).toCatHom
      naturality _ _ F := congr($(pathComposition_naturality F.toFunctor).toCatHom)
    }
    left_triangle := by
      ext V
      exact freeMap_pathsOf_pathComposition V
    r

中文:
定义 adj
  签名: : Cat.free ⊣ Quiv.forget
  定义体: Adjunction.mkOfUnitCounit {
    unit := { app _ := Paths.of _}
    counit := {
      app C := (pathComposition C).toCatHom
      naturality _ _ F := congr($(pathComposition_naturality F.toFunctor).toCatHom)
    }
    left_triangle := by
      ext V
      exact freeMap_pathsOf_pathComposition V
    r

Depends on / 依赖: Adjunction, Adjunction.mkOfUnitCounit, F.toFunctor, Paths.of, counit, freeMap_pathsOf_pathComposition, left_triangle, mkOfUnitCounit, naturality, pathComposition, pathComposition_naturality, pathsOf_pathComposition_toPrefunctor, right_triangle, toCatHom, toFunctor
-/
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfUnitCounit {
    unit := { app _ := Paths.of _}
    counit := {
      app C := (pathComposition C).toCatHom
      naturality _ _ F := congr($(pathComposition_naturality F.toFunctor).toCatHom)
    }
    left_triangle := by
      ext V
      exact freeMap_pathsOf_pathComposition V
    right_triangle := by
      ext C
      exact pathsOf_pathComposition_toPrefunctor C
  }

/--
Definition of `pathsEquiv` / `pathsEquiv` 的定义

English:
definition pathsEquiv
  signature: {V : Type u} {C : Type u₁} [Quiver.{v} V] [Category.{v₁} C]
  body: (Paths.of V).comp F.toPrefunctor
  invFun G := Cat.freeMap G ⋙ pathComposition C
  left_inv F := by
    dsimp
    rw [Cat.freeMap_comp]; rw [Functor.assoc]; rw [pathComposition_naturality]; rw [← Functor.assoc]; rw [freeMap_pathsOf_pathComposition]; rw [Functor.id_comp]
  right_inv G := by
    dsimp

中文:
定义 pathsEquiv
  签名: {V : 类型u} {C : 类型u₁} [Quiver.{v} V] [Category.{v₁} C]
  定义体: (Paths.of V).comp F.toPrefunctor
  invFun G := Cat.freeMap G ⋙ pathComposition C
  left_inv F := by
    dsimp
    rw [Cat.freeMap_comp]; rw [Functor.assoc]; rw [pathComposition_naturality]; rw [← Functor.assoc]; rw [freeMap_pathsOf_pathComposition]; rw [Functor.id_comp]
  right_inv G := by
    dsimp

Depends on / 依赖: F.toPrefunctor, Paths.of, toPrefunctor
-/
def pathsEquiv {V : Type u} {C : Type u₁} [Quiver.{v} V] [Category.{v₁} C] :
    (Paths V ⥤ C) ≃ V ⥤q C where
  toFun F := (Paths.of V).comp F.toPrefunctor
  invFun G := Cat.freeMap G ⋙ pathComposition C
  left_inv F := by
    dsimp
    rw [Cat.freeMap_comp]; rw [Functor.assoc]; rw [pathComposition_naturality]; rw [← Functor.assoc]; rw [freeMap_pathsOf_pathComposition]; rw [Functor.id_comp]
  right_inv G := by
    dsimp
    rw [← Functor.toPrefunctor_comp]; rw [← Prefunctor.comp_assoc]; rw [pathsOf_freeMap_toPrefunctor]; rw [Prefunctor.comp_assoc]; rw [pathsOf_pathComposition_toPrefunctor]; rw [Prefunctor.comp_id]

@[simp]
/--
lemma `adj_homEquiv` / 引理 `adj_homEquiv`

English:
lemma adj_homEquiv
  given: {V C : Type u} [Quiver.{max u v} V] [Category.{max u v} C]
  proof: rfl

中文:
引理 adj_homEquiv
  条件: {V C : 类型u} [Quiver.{max u v} V] [Category.{max u v} C]
  证明: rfl

Depends on / 依赖: HasZeroMorphisms, MonoCoprod, monoCoprodOfHasZeroMorphisms
-/
lemma adj_homEquiv {V C : Type u} [Quiver.{max u v} V] [Category.{max u v} C] :
    adj.homEquiv (Quiv.of V) (Cat.of C) =
      (Cat.Hom.equivFunctor (.of (Paths V)) (.of C)).trans (pathsEquiv (V := V) (C := C)) := rfl

end Quiv

end CategoryTheory
