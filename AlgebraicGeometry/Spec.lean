/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.toTop`, valued in the category of topological spaces,
2. `Spec.toSheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.toLocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.toPresheafedSpace` as a composition of `Spec.toSheafedSpace` with
a forgetful functor.

## Related results

The adjunction `Γ ⊣ Spec` is constructed in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`.

-/

@[expose] public section


-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

/--
Definition of `Spec.topObj` / `Spec.topObj` 的定义

English:
definition Spec.topObj
  signature: (R : CommRingCat.{u})
  body: TopCat.of (PrimeSpectrum R)

中文:
定义 Spec.topObj
  签名: (R : 交换环范畴.{u})
  定义体: TopCat.of (PrimeSpectrum R)

Depends on / 依赖: PrimeSpectrum, TopCat, TopCat.of
-/
def Spec.topObj (R : CommRingCat.{u}) : TopCat :=
  TopCat.of (PrimeSpectrum R)

/--
theorem `Spec.topObj_forget` / 定理 `Spec.topObj_forget`

English:
theorem Spec.topObj_forget
  given: {R}
  statement: ToType (Spec.topObj R) = PrimeSpectrum R
  proof: rfl

中文:
定理 Spec.topObj_forget
  条件: {R}
  结论: ToType (Spec.topObj R) = 素谱 R
  证明: rfl
-/
@[simp] theorem Spec.topObj_forget {R} : ToType (Spec.topObj R) = PrimeSpectrum R :=
  rfl

/--
Definition of `Spec.topMap` / `Spec.topMap` 的定义

English:
definition Spec.topMap
  signature: {R S : CommRingCat.{u}} (f : R ⟶ S)
  body: TopCat.ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩

@[simp]

中文:
定义 Spec.topMap
  签名: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  定义体: TopCat.ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩

@[simp]

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.continuous_comap, TopCat, TopCat.ofHom, continuous_comap, f.hom
-/
def Spec.topMap {R S : CommRingCat.{u}} (f : R ⟶ S) : Spec.topObj S ⟶ Spec.topObj R :=
  TopCat.ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩

@[simp]
/--
theorem `Spec.topMap_id` / 定理 `Spec.topMap_id`

English:
theorem Spec.topMap_id
  given: (R : CommRingCat.{u})
  statement: Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R)
  proof: rfl

@[simp]

中文:
定理 Spec.topMap_id
  条件: (R : 交换环范畴.{u})
  结论: Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R)
  证明: rfl

@[simp]
-/
theorem Spec.topMap_id (R : CommRingCat.{u}) : Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  rfl

@[simp]
/--
theorem `Spec.topMap_comp` / 定理 `Spec.topMap_comp`

English:
theorem Spec.topMap_comp
  given: {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

中文:
定理 Spec.topMap_comp
  条件: {R S T : 交换环范畴.{u}} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl
-/
theorem Spec.topMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.topMap (f ≫ g) = Spec.topMap g ≫ Spec.topMap f :=
  rfl

-- Porting note: `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps!]
/--
Definition of `Spec.toTop` / `Spec.toTop` 的定义

English:
definition Spec.toTop
  signature: : CommRingCat.{u}ᵒᵖ ⥤ TopCat where
  body: Spec.topObj (unop R)
  map {_ _} f := Spec.topMap f.unop

中文:
定义 Spec.toTop
  签名: : 交换环范畴.{u}ᵒᵖ ⥤ 顶元素范畴 where
  定义体: Spec.topObj (unop R)
  map {_ _} f := Spec.topMap f.unop

Depends on / 依赖: Spec.topObj, topObj
-/
def Spec.toTop : CommRingCat.{u}ᵒᵖ ⥤ TopCat where
  obj R := Spec.topObj (unop R)
  map {_ _} f := Spec.topMap f.unop

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
/--
Definition of `Spec.sheafedSpaceObj` / `Spec.sheafedSpaceObj` 的定义

English:
definition Spec.sheafedSpaceObj
  signature: (R : CommRingCat.{u})
  body: Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

中文:
定义 Spec.sheafedSpaceObj
  签名: (R : 交换环范畴.{u})
  定义体: Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

Depends on / 依赖: Spec.topObj, topObj
-/
def Spec.sheafedSpaceObj (R : CommRingCat.{u}) : SheafedSpace CommRingCat where
  carrier := Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

set_option backward.isDefEq.respectTransparency.types false in
/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps hom_base hom_c_app]
/--
Definition of `Spec.sheafedSpaceMap` / `Spec.sheafedSpaceMap` 的定义

English:
definition Spec.sheafedSpaceMap
  signature: {R S : CommRingCat.{u}} (f : R ⟶ S)
  body: Spec.topMap f
  hom.c :=
    { app := fun U => CommRingCat.ofHom <|
        comap f.hom (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => by ext; rfl }

中文:
定义 Spec.sheafedSpaceMap
  签名: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  定义体: Spec.topMap f
  hom.c :=
    { app := fun U => CommRingCat.ofHom <|
        comap f.hom (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => by ext; rfl }

Depends on / 依赖: Spec.topMap, topMap
-/
def Spec.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.sheafedSpaceObj S ⟶ Spec.sheafedSpaceObj R where
  hom.base := Spec.topMap f
  hom.c :=
    { app := fun U => CommRingCat.ofHom <|
        comap f.hom (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => by ext; rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Spec.sheafedSpaceMap_id` / 定理 `Spec.sheafedSpaceMap_id`

English:
theorem Spec.sheafedSpaceMap_id
  given: {R : CommRingCat.{u}}
  proof: by
  ext : 1
  · exact Spec.topMap_id R
  · ext
    dsimp
    rw [comap_id (by simp)]
    simp
    rfl

中文:
定理 Spec.sheafedSpaceMap_id
  条件: {R : 交换环范畴.{u}}
  证明: by
  ext : 1
  · exact Spec.topMap_id R
  · ext
    dsimp
    rw [comap_id (by simp)]
    simp
    rfl

Depends on / 依赖: Spec.topMap_id, comap_id, topMap_id
-/
theorem Spec.sheafedSpaceMap_id {R : CommRingCat.{u}} :
    Spec.sheafedSpaceMap (𝟙 R) = 𝟙 (Spec.sheafedSpaceObj R) := by
  ext : 1
  · exact Spec.topMap_id R
  · ext
    dsimp
    rw [comap_id (by simp)]
    simp
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Spec.sheafedSpaceMap_comp` / 定理 `Spec.sheafedSpaceMap_comp`

English:
theorem Spec.sheafedSpaceMap_comp
  given: {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
  proof: by
  ext : 1
  · exact Spec.topMap_comp f g
  · ext
    -- Porting note: was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app]; rw [sheafedSpaceMap_hom_c_app]; rw [Functor.whiskerRight_app]; rw [eqToHom_refl]
    erw

中文:
定理 Spec.sheafedSpaceMap_comp
  条件: {R S T : 交换环范畴.{u}} (f : R ⟶ S) (g : S ⟶ T)
  证明: by
  ext : 1
  · exact Spec.topMap_comp f g
  · ext
    -- Porting note: was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app]; rw [sheafedSpaceMap_hom_c_app]; rw [Functor.whiskerRight_app]; rw [eqToHom_refl]
    erw

Depends on / 依赖: Spec.topMap_comp, topMap_comp
-/
theorem Spec.sheafedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.sheafedSpaceMap (f ≫ g) = Spec.sheafedSpaceMap g ≫ Spec.sheafedSpaceMap f := by
  ext : 1
  · exact Spec.topMap_comp f g
  · ext
    -- Porting note: was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app]; rw [sheafedSpaceMap_hom_c_app]; rw [Functor.whiskerRight_app]; rw [eqToHom_refl]
    erw [(sheafedSpaceObj T).presheaf.map_id]
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [comap_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
/--
Definition of `Spec.toSheafedSpace` / `Spec.toSheafedSpace` 的定义

English:
definition Spec.toSheafedSpace
  signature: : CommRingCat.{u}ᵒᵖ ⥤ SheafedSpace CommRingCat where
  body: Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_comp f g := by simp [Spec.sheafedSpaceMap_comp]

中文:
定义 Spec.toSheafedSpace
  签名: : 交换环范畴.{u}ᵒᵖ ⥤ Sheafed空间 交换环范畴 where
  定义体: Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_comp f g := by simp [Spec.sheafedSpaceMap_comp]

Depends on / 依赖: Spec.sheafedSpaceObj, sheafedSpaceObj
-/
def Spec.toSheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ SheafedSpace CommRingCat where
  obj R := Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_comp f g := by simp [Spec.sheafedSpaceMap_comp]

/--
Definition of `Spec.toPresheafedSpace` / `Spec.toPresheafedSpace` 的定义

English:
definition Spec.toPresheafedSpace
  signature: : CommRingCat.{u}ᵒᵖ ⥤ PresheafedSpace CommRingCat
  body: Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

@[simp]

中文:
定义 Spec.toPresheafedSpace
  签名: : 交换环范畴.{u}ᵒᵖ ⥤ Presheafed空间 交换环范畴
  定义体: Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

@[simp]

Depends on / 依赖: SheafedSpace, SheafedSpace.forgetToPresheafedSpace, Spec.toSheafedSpace, forgetToPresheafedSpace, toSheafedSpace
-/
def Spec.toPresheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ PresheafedSpace CommRingCat :=
  Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

@[simp]
/--
theorem `Spec.toPresheafedSpace_obj` / 定理 `Spec.toPresheafedSpace_obj`

English:
theorem Spec.toPresheafedSpace_obj
  given: (R : CommRingCat.{u}ᵒᵖ)
  proof: rfl

中文:
定理 Spec.toPresheafedSpace_obj
  条件: (R : 交换环范畴.{u}ᵒᵖ)
  证明: rfl
-/
theorem Spec.toPresheafedSpace_obj (R : CommRingCat.{u}ᵒᵖ) :
    Spec.toPresheafedSpace.obj R = (Spec.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl

/--
theorem `Spec.toPresheafedSpace_obj_op` / 定理 `Spec.toPresheafedSpace_obj_op`

English:
theorem Spec.toPresheafedSpace_obj_op
  given: (R : CommRingCat.{u})
  proof: rfl

@[simp]

中文:
定理 Spec.toPresheafedSpace_obj_op
  条件: (R : 交换环范畴.{u})
  证明: rfl

@[simp]
-/
theorem Spec.toPresheafedSpace_obj_op (R : CommRingCat.{u}) :
    Spec.toPresheafedSpace.obj (op R) = (Spec.sheafedSpaceObj R).toPresheafedSpace :=
  rfl

@[simp]
/--
theorem `Spec.toPresheafedSpace_map` / 定理 `Spec.toPresheafedSpace_map`

English:
theorem Spec.toPresheafedSpace_map
  given: (R S : CommRingCat.{u}ᵒᵖ) (f : R ⟶ S)
  proof: rfl

中文:
定理 Spec.toPresheafedSpace_map
  条件: (R S : 交换环范畴.{u}ᵒᵖ) (f : R ⟶ S)
  证明: rfl
-/
theorem Spec.toPresheafedSpace_map (R S : CommRingCat.{u}ᵒᵖ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f = (Spec.sheafedSpaceMap f.unop).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Spec.toPresheafedSpace_map_op` / 定理 `Spec.toPresheafedSpace_map_op`

English:
theorem Spec.toPresheafedSpace_map_op
  given: (R S : CommRingCat.{u}) (f : R ⟶ S)
  proof: rfl

中文:
定理 Spec.toPresheafedSpace_map_op
  条件: (R S : 交换环范畴.{u}) (f : R ⟶ S)
  证明: rfl
-/
theorem Spec.toPresheafedSpace_map_op (R S : CommRingCat.{u}) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f.op = (Spec.sheafedSpaceMap f).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Spec.basicOpen_hom_ext` / 定理 `Spec.basicOpen_hom_ext`

English:
theorem Spec.basicOpen_hom_ext
  statement: {X : RingedSpace.{u}} {R : CommRingCat.{u}}
  proof: by
  ext : 1
  · exact w
  · apply ((TopCat.Sheaf.pushforward _ β.hom.base).obj X.sheaf).hom_ext _
      PrimeSpectrum.isBasis_basic_opens
    intro r
    apply (StructureSheaf.to_basicOpen_epi R r).1
    simpa using! h r

中文:
定理 Spec.basicOpen_hom_ext
  结论: {X : RingedSpace.{u}} {R : 交换环范畴.{u}}
  证明: by
  ext : 1
  · exact w
  · apply ((TopCat.Sheaf.pushforward _ β.hom.base).obj X.sheaf).hom_ext _
      PrimeSpectrum.isBasis_basic_opens
    intro r
    apply (StructureSheaf.to_basicOpen_epi R r).1
    simpa using! h r

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen, basicOpen
-/
theorem Spec.basicOpen_hom_ext {X : RingedSpace.{u}} {R : CommRingCat.{u}}
    {α β : X ⟶ Spec.sheafedSpaceObj R} (w : α.hom.base = β.hom.base)
    (h : forall r : R,
      let U := PrimeSpectrum.basicOpen r
      ((CommRingCat.ofHom (algebraMap R _)) ≫ α.hom.c.app (op U)) ≫
        X.presheaf.map (eqToHom (by rw [w])) =
        CommRingCat.ofHom (algebraMap _ _) ≫ β.hom.c.app (op U)) :
    α = β := by
  ext : 1
  · exact w
  · apply ((TopCat.Sheaf.pushforward _ β.hom.base).obj X.sheaf).hom_ext _
      PrimeSpectrum.isBasis_basic_opens
    intro r
    apply (StructureSheaf.to_basicOpen_epi R r).1
    simpa using! h r

set_option backward.isDefEq.respectTransparency.types false in
-- `simps!` generates some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`. -/
@[simps! toSheafedSpace presheaf]
/--
Definition of `Spec.locallyRingedSpaceObj` / `Spec.locallyRingedSpaceObj` 的定义

English:
definition Spec.locallyRingedSpaceObj
  signature: (R : CommRingCat.{u})
  body: Spec.sheafedSpaceObj R
  isLocalRing x := (stalkIso R x).toRingEquiv.isLocalRing

中文:
定义 Spec.locallyRingedSpaceObj
  签名: (R : 交换环范畴.{u})
  定义体: Spec.sheafedSpaceObj R
  isLocalRing x := (stalkIso R x).toRingEquiv.isLocalRing

Depends on / 依赖: Spec.sheafedSpaceObj, sheafedSpaceObj
-/
def Spec.locallyRingedSpaceObj (R : CommRingCat.{u}) : LocallyRingedSpace where
  __ := Spec.sheafedSpaceObj R
  isLocalRing x := (stalkIso R x).toRingEquiv.isLocalRing

/--
lemma `Spec.locallyRingedSpaceObj_sheaf` / 引理 `Spec.locallyRingedSpaceObj_sheaf`

English:
lemma Spec.locallyRingedSpaceObj_sheaf
  given: (R : CommRingCat.{u})
  proof: rfl

中文:
引理 Spec.locallyRingedSpaceObj_sheaf
  条件: (R : 交换环范畴.{u})
  证明: rfl
-/
lemma Spec.locallyRingedSpaceObj_sheaf (R : CommRingCat.{u}) :
    (Spec.locallyRingedSpaceObj R).sheaf = structureSheaf R := rfl

/--
lemma `Spec.locallyRingedSpaceObj_sheaf'` / 引理 `Spec.locallyRingedSpaceObj_sheaf'`

English:
lemma Spec.locallyRingedSpaceObj_sheaf'
  given: (R : Type u) [CommRing R]
  proof: rfl

中文:
引理 Spec.locallyRingedSpaceObj_sheaf'
  条件: (R : 类型u) [交换环 R]
  证明: rfl
-/
lemma Spec.locallyRingedSpaceObj_sheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).sheaf = structureSheaf R := rfl

/--
lemma `Spec.locallyRingedSpaceObj_presheaf_map` / 引理 `Spec.locallyRingedSpaceObj_presheaf_map`

English:
lemma Spec.locallyRingedSpaceObj_presheaf_map
  given: (R : CommRingCat.{u}) {U V} (i : U ⟶ V)
  proof: rfl

中文:
引理 Spec.locallyRingedSpaceObj_presheaf_map
  条件: (R : 交换环范畴.{u}) {U V} (i : U ⟶ V)
  证明: rfl
-/
lemma Spec.locallyRingedSpaceObj_presheaf_map (R : CommRingCat.{u}) {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

/--
lemma `Spec.locallyRingedSpaceObj_presheaf'` / 引理 `Spec.locallyRingedSpaceObj_presheaf'`

English:
lemma Spec.locallyRingedSpaceObj_presheaf'
  given: (R : Type u) [CommRing R]
  proof: rfl

中文:
引理 Spec.locallyRingedSpaceObj_presheaf'
  条件: (R : 类型u) [交换环 R]
  证明: rfl
-/
lemma Spec.locallyRingedSpaceObj_presheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf = (structureSheaf R).1 := rfl

/--
lemma `Spec.locallyRingedSpaceObj_presheaf_map'` / 引理 `Spec.locallyRingedSpaceObj_presheaf_map'`

English:
lemma Spec.locallyRingedSpaceObj_presheaf_map'
  given: (R : Type u) [CommRing R] {U V} (i : U ⟶ V)
  proof: rfl

中文:
引理 Spec.locallyRingedSpaceObj_presheaf_map'
  条件: (R : 类型u) [交换环 R] {U V} (i : U ⟶ V)
  证明: rfl
-/
lemma Spec.locallyRingedSpaceObj_presheaf_map' (R : Type u) [CommRing R] {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise]
/--
theorem `stalkMap_toStalk` / 定理 `stalkMap_toStalk`

English:
theorem stalkMap_toStalk
  given: {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S)
  proof: by
  rw [← algebraMap_germ ⊤ p trivial]; rw [← algebraMap_germ ⊤ (PrimeSpectrum.comap f.hom p) trivial]; rw [Category.assoc]
  erw [PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f).hom ⊤ p trivial]
  rw [Spec.sheafedSpaceMap_hom_c_app]
  erw [toOpen_comp_comap_assoc]
  rfl

中文:
定理 stalkMap_toStalk
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S) (p : 素谱 S)
  证明: by
  rw [← algebraMap_germ ⊤ p trivial]; rw [← algebraMap_germ ⊤ (PrimeSpectrum.comap f.hom p) trivial]; rw [Category.assoc]
  erw [PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f).hom ⊤ p trivial]
  rw [Spec.sheafedSpaceMap_hom_c_app]
  erw [toOpen_comp_comap_assoc]
  rfl

Depends on / 依赖: Category, Category.assoc, PresheafedSpace, PresheafedSpace.stalkMap_germ, PrimeSpectrum, PrimeSpectrum.comap, Spec.sheafedSpaceMap, Spec.sheafedSpaceMap_hom_c_app, algebraMap_germ, f.hom, sheafedSpaceMap, sheafedSpaceMap_hom_c_app, stalkMap_germ, toOpen_comp_comap_assoc
-/
theorem stalkMap_toStalk {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f.hom p) ≫ (Spec.sheafedSpaceMap f).hom.stalkMap p =
      f ≫ toStalk S p := by
  rw [← algebraMap_germ ⊤ p trivial]; rw [← algebraMap_germ ⊤ (PrimeSpectrum.comap f.hom p) trivial]; rw [Category.assoc]
  erw [PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f).hom ⊤ p trivial]
  rw [Spec.sheafedSpaceMap_hom_c_app]
  erw [toOpen_comp_comap_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the isomorphisms `stalkIso`, the map `stalkMap (Spec.sheafedSpaceMap f) p` corresponds
to the induced local ring homomorphism `Localization.localRingHom`.
-/
@[elementwise]
/--
theorem `localRingHom_comp_stalkIso` / 定理 `localRingHom_comp_stalkIso`

English:
theorem localRingHom_comp_stalkIso
  given: {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S)
  proof: (stalkIso R (PrimeSpectrum.comap f.hom p)).toCommRingCatIso.symm.eq_inv_comp.mp
(stalkIso S p).toCommRingCatIso.symm.comp_inv_eq.mpr CommRingCat.hom_ext
      Localization.localRingHom_unique _ _ _ (PrimeSpectrum.comap_asIdeal _ _) fun x => by
  dsimp [-RingEquiv.symm_mk]
  simp only [AlgEquiv.commu

中文:
定理 localRingHom_comp_stalkIso
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S) (p : 素谱 S)
  证明: (stalkIso R (PrimeSpectrum.comap f.hom p)).toCommRingCatIso.symm.eq_inv_comp.mp
(stalkIso S p).toCommRingCatIso.symm.comp_inv_eq.mpr CommRingCat.hom_ext
      Localization.localRingHom_unique _ _ _ (PrimeSpectrum.comap_asIdeal _ _) fun x => by
  dsimp [-RingEquiv.symm_mk]
  simp only [AlgEquiv.commu

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, CommRingCat, CommRingCat.hom_ext, Localization, Localization.localRingHom_unique, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.comap_asIdeal, RingEquiv, RingEquiv.symm_apply_eq, RingEquiv.symm_mk, coe_ringEquiv, comap_asIdeal, commutes, comp_inv_eq, eq_inv_comp, f.hom, hom_ext
-/
theorem localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    CommRingCat.ofHom (stalkIso R (PrimeSpectrum.comap f.hom p)).symm.toRingHom ≫
      (CommRingCat.ofHom (Localization.localRingHom (PrimeSpectrum.comap f.hom p).asIdeal p.asIdeal
          f.hom rfl)) ≫
        CommRingCat.ofHom (stalkIso S p).toRingHom =
      (Spec.sheafedSpaceMap f).hom.stalkMap p :=
(stalkIso R (PrimeSpectrum.comap f.hom p)).toCommRingCatIso.symm.eq_inv_comp.mp
(stalkIso S p).toCommRingCatIso.symm.comp_inv_eq.mpr CommRingCat.hom_ext
      Localization.localRingHom_unique _ _ _ (PrimeSpectrum.comap_asIdeal _ _) fun x => by
  dsimp [-RingEquiv.symm_mk]
  simp only [AlgEquiv.commutes, RingEquiv.symm_apply_eq, AlgEquiv.coe_ringEquiv]
  exact stalkMap_toStalk_apply f p x

set_option backward.isDefEq.respectTransparency false in
/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps! toHom]
/--
Definition of `Spec.locallyRingedSpaceMap` / `Spec.locallyRingedSpaceMap` 的定义

English:
definition Spec.locallyRingedSpaceMap
  signature: {R S : CommRingCat.{u}} (f : R ⟶ S)
  body: LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f).hom fun p =>
    IsLocalHom.mk fun a ha => by
    rw [← localRingHom_comp_stalkIso] at ha
    dsimp at ha
    have : IsLocalHom (stalkIso S p) := isLocalHom_equiv _
    have : IsLocalHom (stalkIso R (p.comap f.hom)).symm := isLocalHom_equiv _
    ex

中文:
定义 Spec.locallyRingedSpaceMap
  签名: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  定义体: LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f).hom fun p =>
    IsLocalHom.mk fun a ha => by
    rw [← localRingHom_comp_stalkIso] at ha
    dsimp at ha
    have : IsLocalHom (stalkIso S p) := isLocalHom_equiv _
    have : IsLocalHom (stalkIso R (p.comap f.hom)).symm := isLocalHom_equiv _
    ex

Depends on / 依赖: IsLocalHom, IsLocalHom.mk, LocallyRingedSpace, LocallyRingedSpace.Hom.mk, Spec.sheafedSpaceMap, f.hom, ha.of_map, isLocalHom_equiv, localRingHom_comp_stalkIso, of_map, p.comap, sheafedSpaceMap, stalkIso
-/
def Spec.locallyRingedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R :=
  LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f).hom fun p =>
    IsLocalHom.mk fun a ha => by
    rw [← localRingHom_comp_stalkIso] at ha
    dsimp at ha
    have : IsLocalHom (stalkIso S p) := isLocalHom_equiv _
    have : IsLocalHom (stalkIso R (p.comap f.hom)).symm := isLocalHom_equiv _
    exact ((ha.of_map (stalkIso S p)).of_map _).of_map (stalkIso R (p.comap f.hom)).symm

@[simp]
/--
theorem `Spec.locallyRingedSpaceMap_id` / 定理 `Spec.locallyRingedSpaceMap_id`

English:
theorem Spec.locallyRingedSpaceMap_id
  given: (R : CommRingCat.{u})
  proof: LocallyRingedSpace.Hom.ext' by
    rw [Spec.locallyRingedSpaceMap_toHom]; rw [Spec.sheafedSpaceMap_id]; rfl

中文:
定理 Spec.locallyRingedSpaceMap_id
  条件: (R : 交换环范畴.{u})
  证明: LocallyRingedSpace.Hom.ext' by
    rw [Spec.locallyRingedSpaceMap_toHom]; rw [Spec.sheafedSpaceMap_id]; rfl

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.Hom.ext, Spec.locallyRingedSpaceMap_toHom, Spec.sheafedSpaceMap_id, locallyRingedSpaceMap_toHom, sheafedSpaceMap_id
-/
theorem Spec.locallyRingedSpaceMap_id (R : CommRingCat.{u}) :
    Spec.locallyRingedSpaceMap (𝟙 R) = 𝟙 (Spec.locallyRingedSpaceObj R) :=
LocallyRingedSpace.Hom.ext' by
    rw [Spec.locallyRingedSpaceMap_toHom]; rw [Spec.sheafedSpaceMap_id]; rfl

/--
theorem `Spec.locallyRingedSpaceMap_comp` / 定理 `Spec.locallyRingedSpaceMap_comp`

English:
theorem Spec.locallyRingedSpaceMap_comp
  given: {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
  proof: LocallyRingedSpace.Hom.ext' by
    rw [Spec.locallyRingedSpaceMap_toHom]; rw [Spec.sheafedSpaceMap_comp]; rfl

中文:
定理 Spec.locallyRingedSpaceMap_comp
  条件: {R S T : 交换环范畴.{u}} (f : R ⟶ S) (g : S ⟶ T)
  证明: LocallyRingedSpace.Hom.ext' by
    rw [Spec.locallyRingedSpaceMap_toHom]; rw [Spec.sheafedSpaceMap_comp]; rfl

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.Hom.ext, Spec.locallyRingedSpaceMap_toHom, Spec.sheafedSpaceMap_comp, locallyRingedSpaceMap_toHom, sheafedSpaceMap_comp
-/
theorem Spec.locallyRingedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.locallyRingedSpaceMap (f ≫ g) =
      Spec.locallyRingedSpaceMap g ≫ Spec.locallyRingedSpaceMap f :=
LocallyRingedSpace.Hom.ext' by
    rw [Spec.locallyRingedSpaceMap_toHom]; rw [Spec.sheafedSpaceMap_comp]; rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
/--
Definition of `Spec.toLocallyRingedSpace` / `Spec.toLocallyRingedSpace` 的定义

English:
definition Spec.toLocallyRingedSpace
  signature: : CommRingCat.{u}ᵒᵖ ⥤ LocallyRingedSpace where
  body: Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]

中文:
定义 Spec.toLocallyRingedSpace
  签名: : 交换环范畴.{u}ᵒᵖ ⥤ LocallyRinged空间 where
  定义体: Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]

Depends on / 依赖: Spec.locallyRingedSpaceObj, locallyRingedSpaceObj
-/
def Spec.toLocallyRingedSpace : CommRingCat.{u}ᵒᵖ ⥤ LocallyRingedSpace where
  obj R := Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toSpecΓ` / `toSpecΓ` 的定义

English:
definition toSpecΓ
  signature: (R : CommRingCat.{u})
  body: CommRingCat.ofHom (algebraMap _ _)

中文:
定义 toSpecΓ
  签名: (R : 交换环范畴.{u})
  定义体: CommRingCat.ofHom (algebraMap _ _)

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, algebraMap
-/
def toSpecΓ (R : CommRingCat.{u}) : R ⟶ Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  CommRingCat.ofHom (algebraMap _ _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isIso_toSpecΓ` / 实例 `isIso_toSpecΓ`

English:
instance isIso_toSpecΓ
  signature: (R : CommRingCat.{u})
  body: (ConcreteCategory.isIso_iff_bijective _).mpr algebraMap_obj_top_bijective

中文:
实例 isIso_toSpecΓ
  签名: (R : 交换环范畴.{u})
  定义体: (ConcreteCategory.isIso_iff_bijective _).mpr algebraMap_obj_top_bijective

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, algebraMap_obj_top_bijective, isIso_iff_bijective
-/
instance isIso_toSpecΓ (R : CommRingCat.{u}) : IsIso (toSpecΓ R) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr algebraMap_obj_top_bijective

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
theorem `Spec_Γ_naturality` / 定理 `Spec_Γ_naturality`

English:
theorem Spec_Γ_naturality
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` failed to pick up one of the three lemmas
  ext : 2
refine Subtype.ext funext fun x' => ?_; symm
  erw [comap_apply]
  apply Localization.localRingHom_to_map

#adaptation_note

中文:
定理 Spec_Γ_naturality
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` failed to pick up one of the three lemmas
  ext : 2
refine Subtype.ext funext fun x' => ?_; symm
  erw [comap_apply]
  apply Localization.localRingHom_to_map

#adaptation_note
-/
theorem Spec_Γ_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (Spec.toLocallyRingedSpace.map f.op).op := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` failed to pick up one of the three lemmas
  ext : 2
refine Subtype.ext funext fun x' => ?_; symm
  erw [comap_apply]
  apply Localization.localRingHom_to_map

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps! hom_app inv_app]
/--
Definition of `LocallyRingedSpace.SpecΓIdentity` / `LocallyRingedSpace.SpecΓIdentity` 的定义

English:
definition LocallyRingedSpace.SpecΓIdentity
  signature: : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _
  body: Iso.symm NatIso.ofComponents.{u, u, u + 1, u + 1} (fun R => asIso (toSpecΓ R) :)
    fun {X Y} f => by convert! Spec_Γ_naturality (R := X) (S := Y) f

中文:
定义 LocallyRinged空间.SpecΓIdentity
  签名: : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _
  定义体: Iso.symm NatIso.ofComponents.{u, u, u + 1, u + 1} (fun R => asIso (toSpecΓ R) :)
    fun {X Y} f => by convert! Spec_Γ_naturality (R := X) (S := Y) f

Depends on / 依赖: Iso.symm, NatIso, NatIso.ofComponents, convert, ofComponents
-/
def LocallyRingedSpace.SpecΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
Iso.symm NatIso.ofComponents.{u, u, u + 1, u + 1} (fun R => asIso (toSpecΓ R) :)
    fun {X Y} f => by convert! Spec_Γ_naturality (R := X) (S := Y) f

end SpecΓ

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIso_SpecMap_stakMap_localization` / 定理 `isIso_SpecMap_stakMap_localization`

English:
theorem isIso_SpecMap_stakMap_localization
  statement: (R : CommRingCat.{u}) (M : Submonoid R)
  proof: by
  dsimp only [Spec.toPresheafedSpace_map, Quiver.Hom.unop_op]
  rw [← localRingHom_comp_stalkIso]; rw [ConcreteCategory.isIso_iff_bijective]
  dsimp
  simp only [EquivLike.bijective_comp]
  refine (stalkIso (Localization M) x).bijective.comp ?_
  suffices
    IsIso (IsLocalization.localizationLoc

中文:
定理 isIso_SpecMap_stakMap_localization
  结论: (R : 交换环范畴.{u}) (M : 子幺半群 R)
  证明: by
  dsimp only [Spec.toPresheafedSpace_map, Quiver.Hom.unop_op]
  rw [← localRingHom_comp_stalkIso]; rw [ConcreteCategory.isIso_iff_bijective]
  dsimp
  simp only [EquivLike.bijective_comp]
  refine (stalkIso (Localization M) x).bijective.comp ?_
  suffices
    IsIso (IsLocalization.localizationLoc

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, EquivLike, EquivLike.bijective_comp, IsLocalization, IsLocalization.localizationLocalizationAtPrimeIsoLocalization, Localization, Quiver, Quiver.Hom.unop_op, Spec.toPresheafedSpace_map, asIdeal, bijective, bijective.comp, bijective_comp, infer_instance, isIso_iff_bijective, localRingHom_comp_stalkIso, localizationLocalizationAtPrimeIsoLocalization, stalkIso, toCommRingCatIso
-/
theorem isIso_SpecMap_stakMap_localization (R : CommRingCat.{u}) (M : Submonoid R)
    (x : PrimeSpectrum (Localization M)) :
    IsIso
      ((Spec.toPresheafedSpace.map
        (CommRingCat.ofHom (algebraMap R (Localization M))).op).stalkMap x) := by
  dsimp only [Spec.toPresheafedSpace_map, Quiver.Hom.unop_op]
  rw [← localRingHom_comp_stalkIso]; rw [ConcreteCategory.isIso_iff_bijective]
  dsimp
  simp only [EquivLike.bijective_comp]
  refine (stalkIso (Localization M) x).bijective.comp ?_
  suffices
    IsIso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
        x.asIdeal).toRingEquiv.toCommRingCatIso.hom by
    rwa [ConcreteCategory.isIso_iff_bijective] at this
  infer_instance

namespace StructureSheaf

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum R)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toPushforwardStalk` / `toPushforwardStalk` 的定义

English:
definition toPushforwardStalk
  signature: : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p
  body: CommRingCat.ofHom (algebraMap _ _) ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ p trivial

中文:
定义 toPushforwardStalk
  签名: : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p
  定义体: CommRingCat.ofHom (algebraMap _ _) ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ p trivial

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Presheaf, Spec.topMap, TopCat, TopCat.Presheaf.germ, algebraMap, structureSheaf, topMap
-/
def toPushforwardStalk : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p :=
  CommRingCat.ofHom (algebraMap _ _) ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ p trivial

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `toPushforwardStalk_comp` / 定理 `toPushforwardStalk_comp`

English:
theorem toPushforwardStalk_comp
  proof: by
  rw [StructureSheaf.toStalk]; rw [Category.assoc]; rw [TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _

中文:
定理 toPushforwardStalk_comp
  证明: by
  rw [StructureSheaf.toStalk]; rw [Category.assoc]; rw [TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _

Depends on / 依赖: Category, Category.assoc, Presheaf, StructureSheaf, StructureSheaf.toStalk, TopCat, TopCat.Presheaf.stalkFunctor_map_germ, stalkFunctor_map_germ, toStalk
-/
theorem toPushforwardStalk_comp :
    f ≫ StructureSheaf.toPushforwardStalk f p =
      StructureSheaf.toStalk R p ≫
        (TopCat.Presheaf.stalkFunctor _ _).map (Spec.sheafedSpaceMap f).hom.c := by
  rw [StructureSheaf.toStalk]; rw [Category.assoc]; rw [TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R ((Spec.topMap f _* (structureSheaf S).1).stalk p)
  body: (f ≫ StructureSheaf.toPushforwardStalk f p).hom.toAlgebra

中文:
实例 :
  签名: 代数 R ((Spec.topMap f _* (structureSheaf S).1).stalk p)
  定义体: (f ≫ StructureSheaf.toPushforwardStalk f p).hom.toAlgebra

Depends on / 依赖: StructureSheaf, StructureSheaf.toPushforwardStalk, hom.toAlgebra, toAlgebra, toPushforwardStalk
-/
instance : Algebra R ((Spec.topMap f _* (structureSheaf S).1).stalk p) :=
  (f ≫ StructureSheaf.toPushforwardStalk f p).hom.toAlgebra

/--
theorem `algebraMap_pushforward_stalk` / 定理 `algebraMap_pushforward_stalk`

English:
theorem algebraMap_pushforward_stalk
  proof: rfl

中文:
定理 algebraMap_pushforward_stalk
  证明: rfl
-/
theorem algebraMap_pushforward_stalk :
    algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stalk p) =
      (f ≫ StructureSheaf.toPushforwardStalk f p).hom :=
  rfl

variable (R S)
variable [Algebra R S]

set_option backward.isDefEq.respectTransparency.types false in
/--
This is the `AlgHom` version of `toPushforwardStalk`, which is the map `S ⟶ (f∗ 𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
@[simps!]
/--
Definition of `toPushforwardStalkAlgHom` / `toPushforwardStalkAlgHom` 的定义

English:
definition toPushforwardStalkAlgHom
  signature: :
  body: { (StructureSheaf.toPushforwardStalk (CommRingCat.ofHom (algebraMap R S)) p).hom with
    commutes' := fun _ => rfl }

中文:
定义 toPushforwardStalkAlgHom
  签名: :
  定义体: { (StructureSheaf.toPushforwardStalk (CommRingCat.ofHom (algebraMap R S)) p).hom with
    commutes' := fun _ => rfl }

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, StructureSheaf, StructureSheaf.toPushforwardStalk, algebraMap, commutes, toPushforwardStalk
-/
def toPushforwardStalkAlgHom :
    S ->ₐ[R] (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).stalk p :=
  { (StructureSheaf.toPushforwardStalk (CommRingCat.ofHom (algebraMap R S)) p).hom with
    commutes' := fun _ => rfl }

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isLocalizedModule_toPushforwardStalkAlgHom_aux` / 定理 `isLocalizedModule_toPushforwardStalkAlgHom_aux`

English:
theorem isLocalizedModule_toPushforwardStalkAlgHom_aux
  given: (y)
  proof: by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.exists_germ_eq _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p in PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r <= U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p in U from hp) U.2
  change PrimeSpectrum.basicOpen 

中文:
定理 isLocalizedModule_toPushforwardStalkAlgHom_aux
  条件: (y)
  证明: by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.exists_germ_eq _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p in PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r <= U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p in U from hp) U.2
  change PrimeSpectrum.basicOpen 

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Presheaf, PrimeSpectrum, PrimeSpectrum.basicOpen, PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open, Spec.topMap, TopCat, TopCat.Presheaf.exists_germ_eq, algebraMap, basicOpen, exists_germ_eq, exists_subset_of_mem_open, germ_res_apply, homOfLE, isTopologicalBasis_basic_opens, replace, structureSheaf, topMap
-/
theorem isLocalizedModule_toPushforwardStalkAlgHom_aux (y) :
    exists x : S × p.asIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1 := by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.exists_germ_eq _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p in PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r <= U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p in U from hp) U.2
  change PrimeSpectrum.basicOpen r <= U at hrU
  replace e :=
    ((Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).germ_res_apply
      (homOfLE hrU) p hpr _).trans e
  set s' := (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).map
      (homOfLE hrU).op s with h
  replace e : ((Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).obj).germ _
      p hpr) s' = y := by
    rw [h]; exact e
  clear_value s'; clear! U
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ :=
    @IsLocalization.surj _ _ _ _ _ _
      (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) s'
  refine ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, ?_⟩
  rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [algebraMap_pushforward_stalk]; rw [toPushforwardStalk]; rw [CommRingCat.comp_apply]; rw [CommRingCat.comp_apply]
  iterate 2
    erw [← (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).germ_res_apply
      (homOfLE le_top) p hpr]
  rw [← e]
  let f := TopCat.Presheaf.germ (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _*
      (structureSheaf S).obj) _ p hpr
  rw [← map_mul]; rw [mul_comm]
  dsimp only [Subtype.coe_mk] at hsn
  rw [← map_pow (algebraMap R S)] at hsn
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isLocalizedModule_toPushforwardStalkAlgHom` / 实例 `isLocalizedModule_toPushforwardStalkAlgHom`

English:
instance isLocalizedModule_toPushforwardStalkAlgHom
  signature: :
  body: by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx; rw [algebraMap_pushforward_stalk, toPushforwardStalk_comp]
    change IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap ↑R ↑S))).hom.c _)
    exact (IsLocalization.map_units ((s

中文:
实例 isLocalizedModule_toPushforwardStalkAlgHom
  签名: :
  定义体: by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx; rw [algebraMap_pushforward_stalk, toPushforwardStalk_comp]
    change IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap ↑R ↑S))).hom.c _)
    exact (IsLocalization.map_units ((s

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalization, IsLocalization.map_units, IsLocalizedModule, IsLocalizedModule.mkOfAlgebra, IsUnit, Presheaf, Spec.sheafedSpaceMap, TopCat, TopCat.Presheaf.stalkFunctor, algebraMap, algebraMap_pushforward_stalk, hom.c, isLocalizedModule_toPushforwardStalkAlgHom_aux, map_units, mkOfAlgebra, presheaf, presheaf.stalk, sheafedSpaceMap
-/
instance isLocalizedModule_toPushforwardStalkAlgHom :
    IsLocalizedModule p.asIdeal.primeCompl (toPushforwardStalkAlgHom R S p).toLinearMap := by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx; rw [algebraMap_pushforward_stalk, toPushforwardStalk_comp]
    change IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap ↑R ↑S))).hom.c _)
    exact (IsLocalization.map_units ((structureSheaf R).presheaf.stalk p) ⟨x, hx⟩).map _
  · apply isLocalizedModule_toPushforwardStalkAlgHom_aux
  · intro x hx
    rw [toPushforwardStalkAlgHom_apply]; rw [← (toPushforwardStalk (CommRingCat.ofHom (algebraMap ↑R ↑S)) p).hom.map_zero]; rw [toPushforwardStalk] at hx
    rw [CommRingCat.comp_apply]; rw [map_zero] at hx
    obtain ⟨U, hpU, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq (C := CommRingCat) _ _ _ _ _ _ hx
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p in U.1 from hpU)
        U.2
    apply_fun (Spec.topMap (CommRingCat.ofHom (algebraMap R S)) _* (structureSheaf S).1).map
        (homOfLE hrU).op at e
    have : algebraMap S ((structureSheaf S).presheaf.obj _) x = 0 := e
    have :=
      (@IsLocalization.mk'_one _ _ _ _ _ _
            (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) x).trans
        this
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp this
    refine ⟨⟨r, hpr⟩ ^ n, ?_⟩
    rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [SubmonoidClass.coe_pow]; rw [map_pow]
    exact e

end StructureSheaf

end AlgebraicGeometry
