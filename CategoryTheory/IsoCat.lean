/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom

/-!
# Isomorphisms of categories

An `IsoCat C D` is an isomorphism of categories: a pair of functors `C ⥤ D` and `D ⥤ C`
whose composites are *equal* (not merely naturally isomorphic) to the identity functors.
This is a strict notion, stronger than an equivalence of categories `C ≌ D`.
We also define `Functor.IsIso` as a property saying that a functor is fully faithful and
bijective on objects. We develop basic api for these two concepts.

Unless the application explicitly demands an isomorphism, the equivalence of categories is
to be preferred.

## Main definitions

* `CategoryTheory.IsoCat`: the type of isomorphisms between categories `C` and `D`.
* `CategoryTheory.Functor.IsIso`: a typeclass expressing that a functor is full,
  faithful and bijective on objects, hence underlies an isomorphism of categories.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
variable (F : C ⥤ D) (G : D ⥤ E)

variable (C) (D) in
/--
Definition of `IsoCat` / `IsoCat` 的定义

English:
structure IsoCat
  parameters: where
  axioms and operations (4):
    - functor : C ⥤ D
    - inverse : D ⥤ C
    - unit_eq : 𝟭 C = functor ⋙ inverse
    - counit_eq : inverse ⋙ functor = 𝟭 D

中文:
结构 同构范畴
  参数: where
  公理与运算 (4 个):
    - functor : C ⥤ D
    - inverse : D ⥤ C
    - unit_eq : 𝟭 C = functor ⋙ inverse
    - counit_eq : inverse ⋙ functor = 𝟭 D
-/
structure IsoCat where
  /-- The forward functor of an isomorphism of categories. -/
  functor : C ⥤ D
  /-- The inverse functor of an isomorphism of categories. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is equal to the identity. -/
  unit_eq : 𝟭 C = functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is equal to the identity. -/
  counit_eq : inverse ⋙ functor = 𝟭 D

variable (C) in
/-- The identity isomorphism of categories. -/
@[simps, refl]
/--
Definition of `IsoCat.refl` / `IsoCat.refl` 的定义

English:
definition IsoCat.refl
  signature: : IsoCat C C where
  body: 𝟭 C
  inverse := 𝟭 C
  unit_eq := (Functor.comp_id _).symm
  counit_eq := Functor.comp_id _

中文:
定义 同构范畴.refl
  签名: : 同构范畴 C C where
  定义体: 𝟭 C
  inverse := 𝟭 C
  unit_eq := (Functor.comp_id _).symm
  counit_eq := Functor.comp_id _
-/
def IsoCat.refl : IsoCat C C where
  functor := 𝟭 C
  inverse := 𝟭 C
  unit_eq := (Functor.comp_id _).symm
  counit_eq := Functor.comp_id _

/-- The inverse isomorphism of categories, obtained by swapping `functor` and `inverse`. -/
@[simps, symm]
/--
Definition of `IsoCat.symm` / `IsoCat.symm` 的定义

English:
definition IsoCat.symm
  signature: (e : IsoCat C D)
  body: e.inverse
  inverse := e.functor
  unit_eq := e.counit_eq.symm
  counit_eq := e.unit_eq.symm

中文:
定义 同构范畴.symm
  签名: (e : 同构范畴 C D)
  定义体: e.inverse
  inverse := e.functor
  unit_eq := e.counit_eq.symm
  counit_eq := e.unit_eq.symm

Depends on / 依赖: e.inverse, inverse
-/
def IsoCat.symm (e : IsoCat C D) : IsoCat D C where
  functor := e.inverse
  inverse := e.functor
  unit_eq := e.counit_eq.symm
  counit_eq := e.unit_eq.symm

/-- Composition of isomorphisms of categories. -/
@[simps, trans]
/--
Definition of `IsoCat.trans` / `IsoCat.trans` 的定义

English:
definition IsoCat.trans
  signature: (e : IsoCat C D) (f : IsoCat D E)
  body: e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unit_eq := by
    rw [Functor.assoc]; rw [← Functor.assoc f.functor]; rw [← f.unit_eq]; rw [Functor.id_comp]
    exact e.unit_eq
  counit_eq := by
    rw [Functor.assoc]; rw [← Functor.assoc e.inverse]; rw [e.counit_eq]; rw [Functor.id_comp]

中文:
定义 同构范畴.trans
  签名: (e : 同构范畴 C D) (f : 同构范畴 D E)
  定义体: e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unit_eq := by
    rw [Functor.assoc]; rw [← Functor.assoc f.functor]; rw [← f.unit_eq]; rw [Functor.id_comp]
    exact e.unit_eq
  counit_eq := by
    rw [Functor.assoc]; rw [← Functor.assoc e.inverse]; rw [e.counit_eq]; rw [Functor.id_comp]

Depends on / 依赖: e.functor, f.functor, functor
-/
def IsoCat.trans (e : IsoCat C D) (f : IsoCat D E) : IsoCat C E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unit_eq := by
    rw [Functor.assoc]; rw [← Functor.assoc f.functor]; rw [← f.unit_eq]; rw [Functor.id_comp]
    exact e.unit_eq
  counit_eq := by
    rw [Functor.assoc]; rw [← Functor.assoc e.inverse]; rw [e.counit_eq]; rw [Functor.id_comp]
    exact f.counit_eq

namespace Functor

/--
Definition of `IsIso` / `IsIso` 的定义

English:
class IsIso
  parameters: (F : C ⥤ D)
  axioms and operations (3):
    - faithful : F.Faithful  [default: by infer_instance]
    - full : F.Full  [default: by infer_instance]
    - bijective_obj((F)) : F.obj.Bijective

中文:
类 是同构
  参数: (F : C ⥤ D)
  公理与运算 (3 个):
    - faithful : F.忠实  [默认: by infer_instance]
    - full : F.满  [默认: by infer_instance]
    - bijective_obj((F)) : F.obj.双射
-/
protected class IsIso (F : C ⥤ D) : Prop where
  /-- A functor which is an isomorphism of categories is faithful. -/
  faithful : F.Faithful := by infer_instance
  /-- A functor which is an isomorphism of categories is full. -/
  full : F.Full := by infer_instance
  /-- A functor which is an isomorphism of categories is bijective on objects. -/
  bijective_obj (F) : F.obj.Bijective

export Functor.IsIso (bijective_obj)

attribute [instance] Functor.IsIso.faithful Functor.IsIso.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟭 C).IsIso
  body: Function.bijective_id

中文:
实例 :
  签名: (𝟭 C).是同构
  定义体: Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, bijective_id
-/
instance : (𝟭 C).IsIso where
  bijective_obj := Function.bijective_id

variable [F.IsIso] [G.IsIso]

/--
Definition of `objEquiv` / `objEquiv` 的定义

English:
definition objEquiv
  signature: : C ≃ D
  body: .ofBijective _ (F.bijective_obj)

@[simp]

中文:
定义 objEquiv
  签名: : C ≃ D
  定义体: .ofBijective _ (F.bijective_obj)

@[simp]

Depends on / 依赖: F.bijective_obj, bijective_obj, ofBijective
-/
noncomputable def objEquiv : C ≃ D := .ofBijective _ (F.bijective_obj)

@[simp]
/--
lemma `objEquiv_symm_apply_apply` / 引理 `objEquiv_symm_apply_apply`

English:
lemma objEquiv_symm_apply_apply
  given: (X : C)
  proof: F.objEquiv.symm_apply_apply X

@[simp]

中文:
引理 objEquiv_symm_apply_apply
  条件: (X : C)
  证明: F.objEquiv.symm_apply_apply X

@[simp]

Depends on / 依赖: F.objEquiv.symm_apply_apply, objEquiv, symm_apply_apply
-/
lemma objEquiv_symm_apply_apply (X : C) :
    F.objEquiv.symm (F.obj X) = X :=
  F.objEquiv.symm_apply_apply X

@[simp]
/--
lemma `objEquiv_apply_symm_apply` / 引理 `objEquiv_apply_symm_apply`

English:
lemma objEquiv_apply_symm_apply
  given: (Y : D)
  proof: F.objEquiv.apply_symm_apply Y

中文:
引理 objEquiv_apply_symm_apply
  条件: (Y : D)
  证明: F.objEquiv.apply_symm_apply Y

Depends on / 依赖: F.objEquiv.apply_symm_apply, apply_symm_apply, objEquiv
-/
lemma objEquiv_apply_symm_apply (Y : D) :
    F.obj (F.objEquiv.symm Y) = Y :=
  F.objEquiv.apply_symm_apply Y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.IsEquivalence
  body: ⟨fun Y => ⟨F.objEquiv.symm Y, ⟨eqToIso (by simp)⟩⟩⟩

中文:
实例 :
  签名: F.是等价
  定义体: ⟨fun Y => ⟨F.objEquiv.symm Y, ⟨eqToIso (by simp)⟩⟩⟩

Depends on / 依赖: F.objEquiv.symm, eqToIso, objEquiv
-/
instance : F.IsEquivalence where
  essSurj := ⟨fun Y => ⟨F.objEquiv.symm Y, ⟨eqToIso (by simp)⟩⟩⟩

/-- The strict inverse of a functor that is an isomorphism of categories, defined using
`Functor.objEquiv` on objects and `Functor.preimage` on morphisms. -/
@[no_expose]
/--
Definition of `strictInv` / `strictInv` 的定义

English:
definition strictInv
  signature: : D ⥤ C where
  body: F.objEquiv.symm
  map f := F.preimage (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  map_comp _ _ := by simp [← preimage_comp]

中文:
定义 strictInv
  签名: : D ⥤ C where
  定义体: F.objEquiv.symm
  map f := F.preimage (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  map_comp _ _ := by simp [← preimage_comp]

Depends on / 依赖: F.objEquiv.symm, objEquiv
-/
noncomputable def strictInv : D ⥤ C where
  obj := F.objEquiv.symm
  map f := F.preimage (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  map_comp _ _ := by simp [← preimage_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `asIsomorphism` / `asIsomorphism` 的定义

English:
definition asIsomorphism
  signature: : IsoCat C D where
  body: F
  inverse := F.strictInv
  unit_eq :=
    ext (fun x => by simp [strictInv])
      (fun _ _ _ => F.map_injective (by simp [eqToHom_map, strictInv]))
  counit_eq :=
    ext (fun x => by simp [strictInv])
      (fun _ _ _ => by simp [strictInv])

中文:
定义 asIsomorphism
  签名: : 同构范畴 C D where
  定义体: F
  inverse := F.strictInv
  unit_eq :=
    ext (fun x => by simp [strictInv])
      (fun _ _ _ => F.map_injective (by simp [eqToHom_map, strictInv]))
  counit_eq :=
    ext (fun x => by simp [strictInv])
      (fun _ _ _ => by simp [strictInv])
-/
noncomputable def asIsomorphism : IsoCat C D where
  functor := F
  inverse := F.strictInv
  unit_eq :=
    ext (fun x => by simp [strictInv])
      (fun _ _ _ => F.map_injective (by simp [eqToHom_map, strictInv]))
  counit_eq :=
    ext (fun x => by simp [strictInv])
      (fun _ _ _ => by simp [strictInv])

end Functor

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsoCat.toEquivalence` / `IsoCat.toEquivalence` 的定义

English:
definition IsoCat.toEquivalence
  signature: (e : IsoCat C D)
  body: e.functor
  inverse := e.inverse
  unitIso := eqToIso e.unit_eq
  counitIso := eqToIso e.counit_eq
  functor_unitIso_comp X := by simp [eqToHom_map]

中文:
定义 同构范畴.toEquivalence
  签名: (e : 同构范畴 C D)
  定义体: e.functor
  inverse := e.inverse
  unitIso := eqToIso e.unit_eq
  counitIso := eqToIso e.counit_eq
  functor_unitIso_comp X := by simp [eqToHom_map]

Depends on / 依赖: e.functor, functor
-/
def IsoCat.toEquivalence (e : IsoCat C D) : C ≌ D where
  functor := e.functor
  inverse := e.inverse
  unitIso := eqToIso e.unit_eq
  counitIso := eqToIso e.counit_eq
  functor_unitIso_comp X := by simp [eqToHom_map]

/-- Promotes an equivalence of categories `e : C ≌ D` whose unit and counit isomorphisms are
given by equalities of objects into an `IsoCat C D`. -/
@[simps]
/--
Definition of `Equivalence.toIsoCat` / `Equivalence.toIsoCat` 的定义

English:
definition Equivalence.toIsoCat
  signature: (e : C ≌ D)
  body: e.functor
  inverse := e.inverse
  unit_eq := Functor.ext_of_iso e.unitIso (by simp [h])
  counit_eq := Functor.ext_of_iso e.counitIso (by simp [h'])

中文:
定义 等价.toIsoCat
  签名: (e : C ≌ D)
  定义体: e.functor
  inverse := e.inverse
  unit_eq := Functor.ext_of_iso e.unitIso (by simp [h])
  counit_eq := Functor.ext_of_iso e.counitIso (by simp [h'])

Depends on / 依赖: Functor, Functor.ext_of_iso, IsoCat, cat_disch, counitIso, counit_eq, e.counitIso, e.counitIso.hom.app, e.functor, e.inverse, e.unitIso, eqToHom, ext_of_iso, functor, inverse, unitIso, unit_eq
-/
def Equivalence.toIsoCat (e : C ≌ D)
    (h : forall (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h' : forall (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (k : forall (X : C), e.unitIso.hom.app X = eqToHom (h X).symm := by cat_disch)
    (k' : forall (Y : D), e.counitIso.hom.app Y = eqToHom (h' Y) := by cat_disch) : IsoCat C D where
  functor := e.functor
  inverse := e.inverse
  unit_eq := Functor.ext_of_iso e.unitIso (by simp [h])
  counit_eq := Functor.ext_of_iso e.counitIso (by simp [h'])

/--
Instance `IsoCat.isIso_functor` / 实例 `IsoCat.isIso_functor`

English:
instance IsoCat.isIso_functor
  signature: (e : IsoCat C D)
  body: e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unit_eq X).symm,
      Functor.congr_obj e.counit_eq⟩

中文:
实例 同构范畴.isIso_functor
  签名: (e : 同构范畴 C D)
  定义体: e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unit_eq X).symm,
      Functor.congr_obj e.counit_eq⟩

Depends on / 依赖: e.toEquivalence.faithful_functor, faithful_functor, toEquivalence
-/
instance IsoCat.isIso_functor (e : IsoCat C D) : e.functor.IsIso where
  faithful := e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unit_eq X).symm,
      Functor.congr_obj e.counit_eq⟩

instance (e : IsoCat C D) : e.inverse.IsIso := e.symm.isIso_functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsIso]
  signature: : F.strictInv.IsIso
  body: F.asIsomorphism.symm.isIso_functor

中文:
实例 [F.是同构]
  签名: : F.strictInv.是同构
  定义体: F.asIsomorphism.symm.isIso_functor

Depends on / 依赖: F.asIsomorphism.symm.isIso_functor, asIsomorphism, isIso_functor
-/
instance [F.IsIso] : F.strictInv.IsIso := F.asIsomorphism.symm.isIso_functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsIso]
  signature: [G.IsIso]
  body: (F.asIsomorphism.trans G.asIsomorphism).isIso_functor

中文:
实例 [F.是同构]
  签名: [G.是同构]
  定义体: (F.asIsomorphism.trans G.asIsomorphism).isIso_functor

Depends on / 依赖: F.asIsomorphism.trans, G.asIsomorphism, asIsomorphism, isIso_functor
-/
instance [F.IsIso] [G.IsIso] : (F ⋙ G).IsIso :=
  (F.asIsomorphism.trans G.asIsomorphism).isIso_functor

end CategoryTheory
