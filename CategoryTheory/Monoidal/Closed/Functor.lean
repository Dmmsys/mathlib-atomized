/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a Cartesian closed functor: one which (naturally) preserves exponentials.

Define the Frobenius morphism, and show it is an isomorphism iff the exponential comparison is an
isomorphism.

## TODO
Some of the results here are true more generally for closed objects and for closed monoidal
categories, and these could be generalised.

## References
https://ncatlab.org/nlab/show/cartesian+closed+functor
https://ncatlab.org/nlab/show/Frobenius+reciprocity

## Tags
Frobenius reciprocity, Cartesian closed functor

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open Category MonoidalClosed MonoidalCategory CartesianMonoidalCategory TwoSquare

universe v u u'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v} D]
variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
variable (F : C ⥤ D) {L : D ⥤ C}

/--
Definition of `frobeniusMorphism` / `frobeniusMorphism` 的定义

English:
definition frobeniusMorphism
  signature: (h : L ⊣ F) (A : C)
  body: prodComparisonNatTrans L (F.obj A) ≫
    Functor.whiskerLeft _ ((curriedTensor C).map (h.counit.app _))

中文:
定义 frobeniusMorphism
  签名: (h : L ⊣ F) (A : C)
  定义体: prodComparisonNatTrans L (F.obj A) ≫
    Functor.whiskerLeft _ ((curriedTensor C).map (h.counit.app _))

Depends on / 依赖: F.obj, Functor, Functor.whiskerLeft, counit, curriedTensor, h.counit.app, prodComparisonNatTrans, whiskerLeft
-/
def frobeniusMorphism (h : L ⊣ F) (A : C) : TwoSquare (tensorLeft (F.obj A)) L L (tensorLeft A) :=
  prodComparisonNatTrans L (F.obj A) ≫
    Functor.whiskerLeft _ ((curriedTensor C).map (h.counit.app _))

/--
Instance `frobeniusMorphism_iso_of_preserves_binary_products` / 实例 `frobeniusMorphism_iso_of_preserves_binary_products`

English:
instance frobeniusMorphism_iso_of_preserves_binary_products
  signature: (h : L ⊣ F) (A : C)
  body: suffices forall (X : D), IsIso ((frobeniusMorphism F h A).natTrans.app X) from
    NatIso.isIso_of_isIso_app _
  fun B => by dsimp [frobeniusMorphism]; infer_instance

中文:
实例 frobeniusMorphism_iso_of_preserves_binary_products
  签名: (h : L ⊣ F) (A : C)
  定义体: suffices forall (X : D), IsIso ((frobeniusMorphism F h A).natTrans.app X) from
    NatIso.isIso_of_isIso_app _
  fun B => by dsimp [frobeniusMorphism]; infer_instance

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, frobeniusMorphism, infer_instance, isIso_of_isIso_app, natTrans, natTrans.app
-/
instance frobeniusMorphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C)
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L] [F.Full] [F.Faithful] :
    IsIso (frobeniusMorphism F h A).natTrans :=
  suffices forall (X : D), IsIso ((frobeniusMorphism F h A).natTrans.app X) from
    NatIso.isIso_of_isIso_app _
  fun B => by dsimp [frobeniusMorphism]; infer_instance

variable [MonoidalClosed C] [MonoidalClosed D]
variable [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]

/--
Definition of `expComparison` / `expComparison` 的定义

English:
definition expComparison
  signature: (A : C)
  body: mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A)) (prodComparisonNatIso F A).inv

中文:
定义 expComparison
  签名: (A : C)
  定义体: mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A)) (prodComparisonNatIso F A).inv

Depends on / 依赖: F.obj, adjunction, ihom.adjunction, mateEquiv, prodComparisonNatIso
-/
def expComparison (A : C) : TwoSquare (ihom A) F F (ihom (F.obj A)) :=
  mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A)) (prodComparisonNatIso F A).inv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `expComparison_ev` / 定理 `expComparison_ev`

English:
theorem expComparison_ev
  given: (A B : C)
  proof: by
  convert! mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, NatIso.isIso_inv_app,
    IsIso

中文:
定理 expComparison_ev
  条件: (A B : C)
  证明: by
  convert! mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, NatIso.isIso_inv_app,
    IsIso

Depends on / 依赖: IsIso.hom_inv_id, IsIso.inv_eq_of_hom_inv_id, NatIso, NatIso.isIso_inv_app, Porting, community, convert, github, github.com, hom_inv_id, inv_eq_of_hom_inv_id, isIso_inv_app, issues, leanprover, mateEquiv_counit, mathlib4, prodComparisonNatIso, prodComparisonNatIso_inv, prodComparisonNatTrans_app
-/
theorem expComparison_ev (A B : C) :
    F.obj A ◁ ((expComparison F A).natTrans.app B) ≫ (ihom.ev (F.obj A)).app (F.obj B) =
      inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _) := by
  convert! mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, NatIso.isIso_inv_app,
    IsIso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coev_expComparison` / 定理 `coev_expComparison`

English:
theorem coev_expComparison
  given: (A B : C)
  proof: by
  convert! unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp

中文:
定理 coev_expComparison
  条件: (A B : C)
  证明: by
  convert! unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, Porting, community, convert, github, github.com, inv_eq_of_hom_inv_id, issues, leanprover, mathlib4, prodComparisonNatIso, unit_mateEquiv
-/
theorem coev_expComparison (A B : C) :
    F.map ((ihom.coev A).app B) ≫ (expComparison F A).natTrans.app (A otimes B) =
      (ihom.coev _).app (F.obj B) ≫ (ihom (F.obj A)).map (inv (prodComparison F A B)) := by
  convert! unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp

/--
theorem `uncurry_expComparison` / 定理 `uncurry_expComparison`

English:
theorem uncurry_expComparison
  given: (A B : C)
  proof: by
  rw [uncurry_eq]; rw [expComparison_ev]

中文:
定理 uncurry_expComparison
  条件: (A B : C)
  证明: by
  rw [uncurry_eq]; rw [expComparison_ev]

Depends on / 依赖: expComparison_ev, uncurry_eq
-/
theorem uncurry_expComparison (A B : C) :
    MonoidalClosed.uncurry ((expComparison F A).natTrans.app B) =
      inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _) := by
  rw [uncurry_eq]; rw [expComparison_ev]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `expComparison_whiskerLeft` / 定理 `expComparison_whiskerLeft`

English:
theorem expComparison_whiskerLeft
  given: {A A' : C} (f : A' ⟶ A)
  proof: by
  unfold expComparison MonoidalClosed.pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (

中文:
定理 expComparison_whiskerLeft
  条件: {A A' : C} (f : A' ⟶ A)
  证明: by
  unfold expComparison MonoidalClosed.pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (

Depends on / 依赖: F.map, F.obj, MonoidalClosed, MonoidalClosed.pre, TwoSquare, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, adjunction, conjugateEquiv_mateEquiv_vcomp, curriedTensor, expComparison, ihom.adjunction, mateEquiv_conjugateEquiv_vcomp, prodComparisonNatIso, vcomp1, vcomp2, whiskerLeft, whiskerRight
-/
theorem expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) :
    (expComparison F A).whiskerBottom (MonoidalClosed.pre (F.map f)) =
      (expComparison F A').whiskerTop (MonoidalClosed.pre f) := by
  unfold expComparison MonoidalClosed.pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction A') (ihom.adjunction (F.obj A'))
    (((curriedTensor C).map f)) ((prodComparisonNatIso F A').inv)
  rw [← vcomp1]; rw [← vcomp2]
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerRight
  congr 1
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, curriedTensor_obj_obj, prodComparisonNatIso_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, curriedTensor_map_app, NatIso.isIso_inv_app,
    Functor.whiskerRight_app, IsIso.eq_inv_comp, prodComparisonNatTrans_app]
  rw [← prodComparison_inv_natural_whiskerRight F f]
  simp

/--
Definition of `MonoidalClosedFunctor` / `MonoidalClosedFunctor` 的定义

English:
class MonoidalClosedFunctor
  parameters: : Prop where
  axioms and operations (1):
    - comparison_iso : forall A, IsIso (expComparison F A).natTrans

中文:
类 幺半群闭函子
  参数: : 命题 where
  公理与运算 (1 个):
    - comparison_iso : 对任意 A, 是同构 (expComparison F A).natTrans
-/
class MonoidalClosedFunctor : Prop where
  comparison_iso : forall A, IsIso (expComparison F A).natTrans

attribute [instance] MonoidalClosedFunctor.comparison_iso

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `frobeniusMorphism_mate` / 定理 `frobeniusMorphism_mate`

English:
theorem frobeniusMorphism_mate
  given: (h : L ⊣ F) (A : C)
  proof: by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (ihom.adjunction (F.obj A)) (ihom.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫
      Functor.whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  congr 1
  apply con

中文:
定理 frobeniusMorphism_mate
  条件: (h : L ⊣ F) (A : C)
  证明: by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (ihom.adjunction (F.obj A)) (ihom.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫
      Functor.whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  congr 1
  apply con

Depends on / 依赖: Category, Category.assoc, Equiv.coe_fn_mk, F.obj, Functor, Functor.comp_obj, Functor.id_obj, Functor.rightUnitor_i, Functor.whiskerLeft, Functor.whiskerLeft_comp, Functor.whiskerRight_comp, NatTrans, NatTrans.comp_app, adjunction, coe_fn_mk, comp_app, comp_obj, congr_arg, conjeq, counit
-/
theorem frobeniusMorphism_mate (h : L ⊣ F) (A : C) :
    conjugateEquiv (h.comp (ihom.adjunction A)) ((ihom.adjunction (F.obj A)).comp h)
        (frobeniusMorphism F h A).natTrans = (expComparison F A).natTrans := by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (ihom.adjunction (F.obj A)) (ihom.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫
      Functor.whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  congr 1
  apply congr_arg
  ext B
  unfold mateEquiv
  simp only [Functor.comp_obj, curriedTensor_obj_obj, Equiv.coe_fn_mk, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, prodComparisonNatTrans_app,
    curriedTensor_map_app, Functor.comp_map, curriedTensor_obj_map, Functor.leftUnitor_hom_app,
    Category.comp_id, Category.id_comp, prodComparisonNatIso_inv, NatIso.isIso_inv_app]
  rw [← F.map_comp]; rw [← F.map_comp]
  simp only [Functor.map_comp]
  apply IsIso.eq_inv_of_inv_hom_id
  simp only [Category.assoc]
  rw [prodComparison_natural_whiskerLeft]; rw [prodComparison_natural_whiskerRight_assoc]
  slice_lhs 2 3 => rw [← prodComparison_comp]
  simp only [Category.assoc]
  unfold prodComparison
  simp

/--
theorem `frobeniusMorphism_iso_of_expComparison_iso` / 定理 `frobeniusMorphism_iso_of_expComparison_iso`

English:
theorem frobeniusMorphism_iso_of_expComparison_iso
  statement: (h : L ⊣ F) (A : C)
  proof: by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i

中文:
定理 frobeniusMorphism_iso_of_expComparison_iso
  结论: (h : L ⊣ F) (A : C)
  证明: by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i

Depends on / 依赖: conjugateEquiv_of_iso, frobeniusMorphism_mate
-/
theorem frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C)
    [i : IsIso (expComparison F A).natTrans] : IsIso (frobeniusMorphism F h A).natTrans := by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i

/--
theorem `expComparison_iso_of_frobeniusMorphism_iso` / 定理 `expComparison_iso_of_frobeniusMorphism_iso`

English:
theorem expComparison_iso_of_frobeniusMorphism_iso
  statement: (h : L ⊣ F) (A : C)
  proof: by
  rw [← frobeniusMorphism_mate F h]; infer_instance

中文:
定理 expComparison_iso_of_frobeniusMorphism_iso
  结论: (h : L ⊣ F) (A : C)
  证明: by
  rw [← frobeniusMorphism_mate F h]; infer_instance

Depends on / 依赖: frobeniusMorphism_mate, infer_instance
-/
theorem expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C)
    [i : IsIso (frobeniusMorphism F h A)] : IsIso (expComparison F A).natTrans := by
  rw [← frobeniusMorphism_mate F h]; infer_instance

open Limits in
/--
theorem `cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts` / 定理 `cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts`

English:
theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
  statement: (h : L ⊣ F) [F.Full] [F.Faithful]
  proof: expComparison_iso_of_frobeniusMorphism_iso F h _

中文:
定理 cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
  结论: (h : L ⊣ F) [F.满] [F.忠实]
  证明: expComparison_iso_of_frobeniusMorphism_iso F h _

Depends on / 依赖: expComparison_iso_of_frobeniusMorphism_iso
-/
theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) L] : MonoidalClosedFunctor F where
  comparison_iso _ := expComparison_iso_of_frobeniusMorphism_iso F h _

end CategoryTheory
