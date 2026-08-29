/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Under `CommRingCat`

In this file we provide basic API for `Under R` when `R : CommRingCat`. `Under R` is
(equivalent to) the category of commutative `R`-algebras. For not necessarily commutative
algebras, use `AlgCat R` instead.
-/

@[expose] public section

noncomputable section

universe u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (Under R) (Type u)
  body: A.right

中文:
实例 :
  签名: CoeSort (Under R) (类型u)
  定义体: A.right

Depends on / 依赖: A.right
-/
instance : CoeSort (Under R) (Type u) where
  coe A := A.right

instance (A : Under R) : Algebra R A := RingHom.toAlgebra A.hom.hom

/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: {A B : Under R} (f : A ⟶ B)
  body: f.right.hom
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using! this

@[simp]

中文:
定义 toAlgHom
  签名: {A B : Under R} (f : A ⟶ B)
  定义体: f.right.hom
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using! this

@[simp]

Depends on / 依赖: f.right.hom
-/
def toAlgHom {A B : Under R} (f : A ⟶ B) : A ->ₐ[R] B where
  __ := f.right.hom
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using! this

@[simp]
/--
lemma `toAlgHom_id` / 引理 `toAlgHom_id`

English:
lemma toAlgHom_id
  given: (A : Under R)
  statement: toAlgHom (𝟙 A) = AlgHom.id R A
  proof: rfl

@[simp]

中文:
引理 toAlgHom_id
  条件: (A : Under R)
  结论: toAlgHom (𝟙 A) = AlgHom.id R A
  证明: rfl

@[simp]
-/
lemma toAlgHom_id (A : Under R) : toAlgHom (𝟙 A) = AlgHom.id R A := rfl

@[simp]
/--
lemma `toAlgHom_comp` / 引理 `toAlgHom_comp`

English:
lemma toAlgHom_comp
  given: {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C)
  proof: rfl

@[simp]

中文:
引理 toAlgHom_comp
  条件: {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C)
  证明: rfl

@[simp]
-/
lemma toAlgHom_comp {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C) :
    toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f) := rfl

@[simp]
/--
lemma `toAlgHom_apply` / 引理 `toAlgHom_apply`

English:
lemma toAlgHom_apply
  given: {A B : Under R} (f : A ⟶ B) (a : A)
  proof: rfl

中文:
引理 toAlgHom_apply
  条件: {A B : Under R} (f : A ⟶ B) (a : A)
  证明: rfl
-/
lemma toAlgHom_apply {A B : Under R} (f : A ⟶ B) (a : A) :
    toAlgHom f a = f.right a :=
  rfl

variable (R) in
/-- Make an object of `Under R` from an `R`-algebra. -/
@[implicit_reducible, simps! hom, simps! -isSimp right]
/--
Definition of `mkUnder` / `mkUnder` 的定义

English:
definition mkUnder
  signature: (A : Type u) [CommRing A] [Algebra R A]
  body: Under.mk (CommRingCat.ofHom <| algebraMap R A)

@[ext]

中文:
定义 mkUnder
  签名: (A : 类型u) [CommRing A] [Algebra R A]
  定义体: Under.mk (CommRingCat.ofHom <| algebraMap R A)

@[ext]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Under.mk, algebraMap
-/
def mkUnder (A : Type u) [CommRing A] [Algebra R A] : Under R :=
  Under.mk (CommRingCat.ofHom <| algebraMap R A)

@[ext]
/--
lemma `mkUnder_ext` / 引理 `mkUnder_ext`

English:
lemma mkUnder_ext
  statement: {A : Type u} [CommRing A] [Algebra R A] {B : Under R}
  proof: by
  ext x
  exact h x

中文:
引理 mkUnder_ext
  结论: {A : 类型u} [CommRing A] [Algebra R A] {B : Under R}
  证明: by
  ext x
  exact h x
-/
lemma mkUnder_ext {A : Type u} [CommRing A] [Algebra R A] {B : Under R}
    {f g : mkUnder R A ⟶ B} (h : forall a : A, f.right a = g.right a) :
    f = g := by
  ext x
  exact h x

end CommRingCat

namespace AlgHom

/--
Definition of `toUnder` / `toUnder` 的定义

English:
definition toUnder
  signature: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  body: Under.homMk (CommRingCat.ofHom f.toRingHom) by
    ext a
    exact f.commutes' a

@[simp]

中文:
定义 toUnder
  签名: {A B : 类型u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  定义体: Under.homMk (CommRingCat.ofHom f.toRingHom) by
    ext a
    exact f.commutes' a

@[simp]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Under.homMk, commutes, f.commutes, f.toRingHom, toRingHom
-/
def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A ->ₐ[R] B) : CommRingCat.mkUnder R A ⟶ CommRingCat.mkUnder R B :=
Under.homMk (CommRingCat.ofHom f.toRingHom) by
    ext a
    exact f.commutes' a

@[simp]
/--
lemma `toUnder_right` / 引理 `toUnder_right`

English:
lemma toUnder_right
  statement: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
  proof: rfl

@[simp]

中文:
引理 toUnder_right
  结论: {A B : 类型u} [CommRing A] [CommRing B] [Algebra R A]
  证明: rfl

@[simp]
-/
lemma toUnder_right {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ->ₐ[R] B) (a : A) :
    Under.Hom.right f.toUnder a = f a :=
  rfl

@[simp]
/--
lemma `toUnder_comp` / 引理 `toUnder_comp`

English:
lemma toUnder_comp
  statement: {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  proof: rfl

中文:
引理 toUnder_comp
  结论: {A B C : 类型u} [CommRing A] [CommRing B] [CommRing C]
  证明: rfl
-/
lemma toUnder_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) :
    (g.comp f).toUnder = f.toUnder ≫ g.toUnder :=
  rfl

end AlgHom

namespace AlgEquiv

/--
Definition of `toUnder` / `toUnder` 的定义

English:
definition toUnder
  signature: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  body: f.toAlgHom.toUnder
  inv := f.symm.toAlgHom.toUnder

@[simp]

中文:
定义 toUnder
  签名: {A B : 类型u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  定义体: f.toAlgHom.toUnder
  inv := f.symm.toAlgHom.toUnder

@[simp]

Depends on / 依赖: f.toAlgHom.toUnder, toAlgHom, toUnder
-/
def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) :
    CommRingCat.mkUnder R A ≅ CommRingCat.mkUnder R B where
  hom := f.toAlgHom.toUnder
  inv := f.symm.toAlgHom.toUnder

@[simp]
/--
lemma `toUnder_hom_right_apply` / 引理 `toUnder_hom_right_apply`

English:
lemma toUnder_hom_right_apply
  statement: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
  proof: rfl

@[simp]

中文:
引理 toUnder_hom_right_apply
  结论: {A B : 类型u} [CommRing A] [CommRing B] [Algebra R A]
  证明: rfl

@[simp]
-/
lemma toUnder_hom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (a : A) :
    f.toUnder.hom.right a = f a := rfl

@[simp]
/--
lemma `toUnder_inv_right_apply` / 引理 `toUnder_inv_right_apply`

English:
lemma toUnder_inv_right_apply
  statement: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
  proof: rfl

@[simp]

中文:
引理 toUnder_inv_right_apply
  结论: {A B : 类型u} [CommRing A] [CommRing B] [Algebra R A]
  证明: rfl

@[simp]
-/
lemma toUnder_inv_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (b : B) :
    f.toUnder.inv.right b = f.symm b := rfl

@[simp]
/--
lemma `toUnder_trans` / 引理 `toUnder_trans`

English:
lemma toUnder_trans
  statement: {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  proof: rfl

中文:
引理 toUnder_trans
  结论: {A B C : 类型u} [CommRing A] [CommRing B] [CommRing C]
  证明: rfl
-/
lemma toUnder_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (f.trans g).toUnder = f.toUnder ≪≫ g.toUnder :=
  rfl

end AlgEquiv

namespace CommRingCat

variable [Algebra R S]

variable (R S) in
/-- The base change functor `A ↦ S ⊗[R] A`. -/
@[simps! obj_right map_right]
/--
Definition of `tensorProd` / `tensorProd` 的定义

English:
definition tensorProd
  signature: : Under R ⥤ Under S where
  body: mkUnder S (S otimes[R] A)
.toUnder map f := Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f)
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

中文:
定义 tensorProd
  签名: : Under R ⥤ Under S where
  定义体: mkUnder S (S otimes[R] A)
.toUnder map f := Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f)
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

Depends on / 依赖: mkUnder, otimes
-/
def tensorProd : Under R ⥤ Under S where
  obj A := mkUnder S (S otimes[R] A)
.toUnder map f := Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f)
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/--
Definition of `tensorProdObjIsoPushoutObj` / `tensorProdObjIsoPushoutObj` 的定义

English:
definition tensorProdObjIsoPushoutObj
  signature: (A : Under R)
  body: Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout by
    simp only [mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom]
    rfl

中文:
定义 tensorProdObjIsoPushoutObj
  签名: (A : Under R)
  定义体: Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout by
    simp only [mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom]
    rfl

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, CommRingCat, CommRingCat.isPushout_tensorProduct, IsPushout, IsPushout.inr_isoPushout_hom, Under.isoMk, flip.isoPushout, inr_isoPushout_hom, isPushout_tensorProduct, isoPushout, mkUnder_hom, toRingHom_eq_coe
-/
def tensorProdObjIsoPushoutObj (A : Under R) :
    mkUnder S (S otimes[R] A) ≅ (Under.pushout (ofHom <| algebraMap R S)).obj A :=
Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout by
    simp only [mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom]
    rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pushout_inl_tensorProdObjIsoPushoutObj_inv_right` / 引理 `pushout_inl_tensorProdObjIsoPushoutObj_inv_right`

English:
lemma pushout_inl_tensorProdObjIsoPushoutObj_inv_right
  given: (A : Under R)
  proof: by
  simp [tensorProdObjIsoPushoutObj]

中文:
引理 pushout_inl_tensorProdObjIsoPushoutObj_inv_right
  条件: (A : Under R)
  证明: by
  simp [tensorProdObjIsoPushoutObj]

Depends on / 依赖: tensorProdObjIsoPushoutObj
-/
lemma pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inl A.hom (ofHom <| algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right =
      (ofHom <| Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pushout_inr_tensorProdObjIsoPushoutObj_inv_right` / 引理 `pushout_inr_tensorProdObjIsoPushoutObj_inv_right`

English:
lemma pushout_inr_tensorProdObjIsoPushoutObj_inv_right
  given: (A : Under R)
  proof: by
  simp [tensorProdObjIsoPushoutObj]

中文:
引理 pushout_inr_tensorProdObjIsoPushoutObj_inv_right
  条件: (A : Under R)
  证明: by
  simp [tensorProdObjIsoPushoutObj]

Depends on / 依赖: tensorProdObjIsoPushoutObj
-/
lemma pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inr A.hom (ofHom <| algebraMap R S) ≫
      (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/--
Definition of `tensorProdIsoPushout` / `tensorProdIsoPushout` 的定义

English:
definition tensorProdIsoPushout
  signature: : tensorProd R S ≅ Under.pushout (ofHom <| algebraMap R S)
  body: NatIso.ofComponents (fun A => tensorProdObjIsoPushoutObj S A) by
    intro A B f
    dsimp
    rw [← cancel_epi (tensorProdObjIsoPushoutObj S A).inv]
    ext : 1
    apply pushout.hom_ext
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext x
      simp [mkUnder_right]
    ·

中文:
定义 tensorProdIsoPushout
  签名: : tensorProd R S ≅ Under.pushout (ofHom <| algebraMap R S)
  定义体: NatIso.ofComponents (fun A => tensorProdObjIsoPushoutObj S A) by
    intro A B f
    dsimp
    rw [← cancel_epi (tensorProdObjIsoPushoutObj S A).inv]
    ext : 1
    apply pushout.hom_ext
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext x
      simp [mkUnder_right]
    ·

Depends on / 依赖: NatIso, NatIso.ofComponents, cancel_epi, cancel_mono, hom_ext, inv.right, mkUnder_right, ofComponents, pushout, pushout.hom_ext, tensorProdObjIsoPushoutObj
-/
def tensorProdIsoPushout : tensorProd R S ≅ Under.pushout (ofHom <| algebraMap R S) :=
NatIso.ofComponents (fun A => tensorProdObjIsoPushoutObj S A) by
    intro A B f
    dsimp
    rw [← cancel_epi (tensorProdObjIsoPushoutObj S A).inv]
    ext : 1
    apply pushout.hom_ext
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext x
      simp [mkUnder_right]
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext (x : S)
      simp [mkUnder_right]

@[simp]
/--
lemma `tensorProdIsoPushout_app` / 引理 `tensorProdIsoPushout_app`

English:
lemma tensorProdIsoPushout_app
  given: (A : Under R)
  proof: rfl

中文:
引理 tensorProdIsoPushout_app
  条件: (A : Under R)
  证明: rfl
-/
lemma tensorProdIsoPushout_app (A : Under R) :
    (tensorProdIsoPushout R S).app A = tensorProdObjIsoPushoutObj S A :=
  rfl

end CommRingCat
