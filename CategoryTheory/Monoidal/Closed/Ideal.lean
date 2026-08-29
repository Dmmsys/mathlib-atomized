/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Subterminal

/-!
# Exponential ideals

An exponential ideal of a Cartesian closed category `C` is a subcategory `D ⊆ C` such that for any
`B : D` and `A : C`, the exponential `A ⟹ B` is in `D`: resembling ring-theoretic ideals. We
define the notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories to
preserve the principle of equivalence.

We additionally show that if `C` is Cartesian closed and `i : D ⥤ C` is a reflective functor, the
following are equivalent.
* The left adjoint to `i` preserves binary (equivalently, finite) products.
* `i` is an exponential ideal.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category

open scoped CartesianClosed

section Ideal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D] {i : D ⥤ C}
variable (i) [CartesianMonoidalCategory C] [MonoidalClosed C]

/--
Definition of `ExponentialIdeal` / `ExponentialIdeal` 的定义

English:
class ExponentialIdeal
  parameters: : Prop where
  axioms and operations (1):
    - exp_closed : forall {B}, i.essImage B -> forall A, i.essImage (A ⟹ B)

中文:
类 ExponentialIdeal
  参数: : 命题 where
  公理与运算 (1 个):
    - exp_closed : 对任意 {B}, i.essImage B -> 对任意 A, i.essImage (A ⟹ B)
-/
class ExponentialIdeal : Prop where
  exp_closed : forall {B}, i.essImage B -> forall A, i.essImage (A ⟹ B)
attribute [nolint docBlame] ExponentialIdeal.exp_closed

/--
theorem `ExponentialIdeal.mk'` / 定理 `ExponentialIdeal.mk'`

English:
theorem ExponentialIdeal.mk'
  given: (h : forall (B : D) (A : C), i.essImage (A ⟹ i.obj B))
  proof: ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((ihom A).mapIso iB') (h B' A)⟩

中文:
定理 ExponentialIdeal.mk'
  条件: (h : 对任意 (B : D) (A : C), i.essImage (A ⟹ i.obj B))
  证明: ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((ihom A).mapIso iB') (h B' A)⟩

Depends on / 依赖: Functor, Functor.essImage.ofIso, essImage, mapIso
-/
theorem ExponentialIdeal.mk' (h : forall (B : D) (A : C), i.essImage (A ⟹ i.obj B)) :
    ExponentialIdeal i :=
  ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((ihom A).mapIso iB') (h B' A)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ExponentialIdeal (𝟭 C)
  body: ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩

中文:
实例 :
  签名: ExponentialIdeal (𝟭 C)
  定义体: ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩

Depends on / 依赖: ExponentialIdeal, ExponentialIdeal.mk, Iso.refl
-/
instance : ExponentialIdeal (𝟭 C) :=
  ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩

open MonoidalClosed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ExponentialIdeal (subterminalInclusion C)
  body: by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (MonoidalClosed.uncurry g) (MonoidalClosed.uncurry h))

中文:
实例 :
  签名: ExponentialIdeal (subterminalInclusion C)
  定义体: by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (MonoidalClosed.uncurry g) (MonoidalClosed.uncurry h))

Depends on / 依赖: ExponentialIdeal, ExponentialIdeal.mk, Iso.refl, MonoidalClosed, MonoidalClosed.uncurry, uncurry, uncurry_injective
-/
instance : ExponentialIdeal (subterminalInclusion C) := by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (MonoidalClosed.uncurry g) (MonoidalClosed.uncurry h))

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `exponentialIdealReflective` / `exponentialIdealReflective` 的定义

English:
definition exponentialIdealReflective
  signature: (A : C) [Reflective i] [ExponentialIdeal i]
  body: by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

中文:
定义 exponentialIdealReflective
  签名: (A : C) [Reflective i] [ExponentialIdeal i]
  定义体: by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

Depends on / 依赖: ExponentialIdeal, ExponentialIdeal.exp_closed, F.obj, F.property, Functor, Functor.essImage.unit_isIso, NatIso, NatIso.ofComponents, Presheaf, Presheaf.isSheaf_iff_preservesFiniteProducts, essImage, exp_closed, i.obj, i.obj_mem_essImage, isSheaf_iff_preservesFiniteProducts, obj_mem_essImage, ofComponents, property, reflectorAdjunction, unit.app
-/
def exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] :
    i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A := by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

/--
theorem `ExponentialIdeal.mk_of_iso` / 定理 `ExponentialIdeal.mk_of_iso`

English:
theorem ExponentialIdeal.mk_of_iso
  statement: [Reflective i]
  proof: by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

中文:
定理 ExponentialIdeal.mk_of_iso
  结论: [Reflective i]
  证明: by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

Depends on / 依赖: ExponentialIdeal, ExponentialIdeal.mk
-/
theorem ExponentialIdeal.mk_of_iso [Reflective i]
    (h : forall A : C, i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A) : ExponentialIdeal i := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

end Ideal

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D]
variable (i : D ⥤ C)

/--
theorem `reflective_products` / 定理 `reflective_products`

English:
theorem reflective_products
  given: [Limits.HasFiniteProducts C] [Reflective i]
  proof: ⟨fun _ => hasLimitsOfShape_of_reflective i⟩

中文:
定理 reflective_products
  条件: [Limits.HasFiniteProducts C] [Reflective i]
  证明: ⟨fun _ => hasLimitsOfShape_of_reflective i⟩

Depends on / 依赖: hasLimitsOfShape_of_reflective
-/
theorem reflective_products [Limits.HasFiniteProducts C] [Reflective i] :
    Limits.HasFiniteProducts D := ⟨fun _ => hasLimitsOfShape_of_reflective i⟩

open MonoidalClosed MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
open Limits in
-- Note: This is not an instance as one might already have a (different) `CartesianMonoidalCategory`
-- instance on `D` (as for example with sheaves).
-- See note [reducible non-instances]
/--
Definition of `CartesianMonoidalCategory.ofReflective` / `CartesianMonoidalCategory.ofReflective` 的定义

English:
abbreviation CartesianMonoidalCategory.ofReflective
  signature: [CartesianMonoidalCategory C] [Reflective i]
  body: .ofChosenFiniteProducts
    ({ cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
       isLimit := by
         apply isLimitOfReflects i
         apply isLimitChangeEmptyCone _ isTerminalTensorUnit
         letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
           have := reflecti

中文:
缩写 CartesianMonoidalCategory.ofReflective
  签名: [CartesianMonoidalCategory C] [Reflective i]
  定义体: .ofChosenFiniteProducts
    ({ cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
       isLimit := by
         apply isLimitOfReflects i
         apply isLimitChangeEmptyCone _ isTerminalTensorUnit
         letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
           have := reflecti

Depends on / 依赖: Functor, Functor.essImage.unit_isIso, IsLimit, IsLimit.conePointUniqueUpToIso, Limits, Limits.asEmptyCone, PreservesTerminal, PreservesTerminal.iso, asEmptyCone, conePointUniqueUpToIso, essImage, isLimit, isLimitChangeEmptyCone, isLimitOfReflects, isTerminalTensorUnit, limit.isLimit, ofChosenFiniteProducts, reflective_products, reflector, reflectorAdjunction
-/
abbrev CartesianMonoidalCategory.ofReflective [CartesianMonoidalCategory C] [Reflective i] :
    CartesianMonoidalCategory D :=
  .ofChosenFiniteProducts
    ({ cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
       isLimit := by
         apply isLimitOfReflects i
         apply isLimitChangeEmptyCone _ isTerminalTensorUnit
         letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
           have := reflective_products i
.trans ?_⟩⟩ refine Functor.essImage.unit_isIso ⟨terminal D, ⟨PreservesTerminal.iso i
           exact IsLimit.conePointUniqueUpToIso (limit.isLimit _) isTerminalTensorUnit
         exact asIso ((reflectorAdjunction i).unit.app (𝟙_ C)) })
  fun X Y =>
    { cone := BinaryFan.mk
        ((reflector i).map (fst (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
        ((reflector i).map (snd (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
      isLimit := by
        apply isLimitOfReflects i
.invFun apply IsLimit.equivOfNatIsoOfIso (pairComp X Y _) _ _ _
          (tensorProductIsBinaryProduct (i.obj X) (i.obj Y))
        fapply BinaryFan.ext
        · change (reflector i ⋙ i).obj (i.obj X otimes i.obj Y) ≅ (𝟭 C).obj (i.obj X otimes i.obj Y)
          letI : IsIso ((reflectorAdjunction i).unit.app (i.obj X otimes i.obj Y)) := by
            apply Functor.essImage.unit_isIso
            have := reflective_products i
            use Limits.prod X Y
            constructor
.trans apply Limits.PreservesLimitPair.iso i _ _
            refine Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (i.obj X) (i.obj Y)))
              (tensorProductIsBinaryProduct _ _)
.symm exact asIso ((reflectorAdjunction i).unit.app (i.obj X otimes i.obj Y))
        · simp only [BinaryFan.fst, Cone.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc]
        · simp only [BinaryFan.snd, Cone.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc] }

variable [CartesianMonoidalCategory C] [Reflective i] [MonoidalClosed C]
  [CartesianMonoidalCategory D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the reflector preserves binary products, the subcategory is an exponential ideal.
This is the converse of `preservesBinaryProductsOfExponentialIdeal`.
-/
instance (priority := 10) exponentialIdeal_of_preservesBinaryProducts
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (reflector i)] :
    ExponentialIdeal i := by
  let ir := reflectorAdjunction i
  let L : C ⥤ D := reflector i
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit
  apply ExponentialIdeal.mk'
  intro B A
  let q : i.obj (L.obj (A ⟹ i.obj B)) ⟶ A ⟹ i.obj B := by
    apply MonoidalClosed.curry (ir.homEquiv _ _ _)
    apply _ ≫ (ir.homEquiv _ _).symm ((ihom.ev A).app (i.obj B))
    exact prodComparison L A _ ≫ (_ ◁ (ε.app _)) ≫ inv (prodComparison _ _ _)
  have : η.app (A ⟹ i.obj B) ≫ q = 𝟙 (A ⟹ i.obj B) := by
    dsimp
    rw [← curry_natural_left]; rw [curry_eq_iff]; rw [uncurry_id_eq_ev]; rw [← ir.homEquiv_naturality_left]; rw [ir.homEquiv_apply_eq]; rw [Category.assoc]; rw [Category.assoc]; rw [prodComparison_natural_whiskerLeft_assoc]; rw [← whiskerLeft_comp_assoc]; rw [ir.left_triangle_components]; rw [whiskerLeft_id]; rw [Category.id_comp]
    apply IsIso.hom_inv_id_assoc
  have : IsSplitMono (η.app (A ⟹ i.obj B)) := IsSplitMono.mk' ⟨_, this⟩
  apply mem_essImage_of_unit_isSplitMono

variable [ExponentialIdeal i]

set_option backward.defeqAttrib.useBackward true in
/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself Cartesian closed.

To allow for better control of definitional equality, this construction
takes in an explicit choice of lift of the essential image of `i` to `D`, in the form of a functor
`l : i.EssImageSubcategory ⥤ D` and natural isomorphism `φ : l ⋙ i ≅ i.essImage.ι`. When
`l ⋙ i` is defeq to `i.essImage.ι`, images of exponential objects in `D` under `i` will be defeq
to the respective exponential objects in `C`. -/
@[instance_reducible]
/--
Definition of `cartesianClosedOfReflective'` / `cartesianClosedOfReflective'` 的定义

English:
definition cartesianClosedOfReflective'
  signature: (l : i.EssImageSubcategory ⥤ D) (φ : l ⋙ i ≅ i.essImage.ι)
  body: fun B =>
    { rightAdj := i.essImage.lift (i ⋙ ihom (i.obj B))
        (fun X => ExponentialIdeal.exp_closed (i.obj_mem_essImage X) _) ⋙ l
      adj := by
        apply (ihom.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
          i.fullyFaithfulOfReflective
        · symm

中文:
定义 cartesianClosedOfReflective'
  签名: (l : i.EssImageSubcategory ⥤ D) (φ : l ⋙ i ≅ i.essImage.ι)
  定义体: fun B =>
    { rightAdj := i.essImage.lift (i ⋙ ihom (i.obj B))
        (fun X => ExponentialIdeal.exp_closed (i.obj_mem_essImage X) _) ⋙ l
      adj := by
        apply (ihom.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
          i.fullyFaithfulOfReflective
        · symm
-/
def cartesianClosedOfReflective' (l : i.EssImageSubcategory ⥤ D) (φ : l ⋙ i ≅ i.essImage.ι) :
    MonoidalClosed D where
  closed := fun B =>
    { rightAdj := i.essImage.lift (i ⋙ ihom (i.obj B))
        (fun X => ExponentialIdeal.exp_closed (i.obj_mem_essImage X) _) ⋙ l
      adj := by
        apply (ihom.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
          i.fullyFaithfulOfReflective
        · symm
          refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
          · haveI :=
              Adjunction.rightAdjoint_preservesLimits.{0, 0} (reflectorAdjunction i)
            apply asIso (prodComparison i B X)
          · dsimp [asIso]
            rw [prodComparison_natural_whiskerLeft]
· exact (i.essImage.liftCompιIso _ _).symm.trans
            (Functor.isoWhiskerLeft _ φ.symm).trans (Functor.associator _ _ _).symm }

set_option backward.defeqAttrib.useBackward true in
/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself Cartesian closed.

Unlike `cartesianClosedOfReflective'` this construction lifts exponential objects in `C` to
exponential objects in `D` by applying the reflector to them, even though they already lie in the
essential image of `i`; if you need better control over definitional equality, use
`cartesianClosedOfReflective'` instead. -/
@[instance_reducible]
/--
Definition of `cartesianClosedOfReflective` / `cartesianClosedOfReflective` 的定义

English:
definition cartesianClosedOfReflective
  signature: : MonoidalClosed D
  body: cartesianClosedOfReflective' i (i.essImage.ι ⋙ reflector i)
    (NatIso.ofComponents (fun X =>
      have := Functor.essImage.unit_isIso X.2
      (asIso ((reflectorAdjunction i).unit.app X.obj)).symm))

中文:
定义 cartesianClosedOfReflective
  签名: : MonoidalClosed D
  定义体: cartesianClosedOfReflective' i (i.essImage.ι ⋙ reflector i)
    (NatIso.ofComponents (fun X =>
      have := Functor.essImage.unit_isIso X.2
      (asIso ((reflectorAdjunction i).unit.app X.obj)).symm))

Depends on / 依赖: Functor, Functor.essImage.unit_isIso, NatIso, NatIso.ofComponents, X.obj, cartesianClosedOfReflective, essImage, i.essImage, ofComponents, reflector, reflectorAdjunction, unit.app, unit_isIso
-/
def cartesianClosedOfReflective : MonoidalClosed D :=
  cartesianClosedOfReflective' i (i.essImage.ι ⋙ reflector i)
    (NatIso.ofComponents (fun X =>
      have := Functor.essImage.unit_isIso X.2
      (asIso ((reflectorAdjunction i).unit.app X.obj)).symm))

variable [BraidedCategory C]

/--
Definition of `bijection` / `bijection` 的定义

English:
definition bijection
  signature: (A B : C) (X : D)
  body: calc
    _ ≃ (A otimes B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B otimes A ⟶ i.obj X) := (β_ _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (Exponen

中文:
定义 bijection
  签名: (A B : C) (X : D)
  定义体: calc
    _ ≃ (A otimes B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B otimes A ⟶ i.obj X) := (β_ _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (Exponen

Depends on / 依赖: ExponentialIdeal, ExponentialIdeal.exp_closed, Iso.refl, adjunction, exp_closed, homCongr, homEquiv, i.obj, i.obj_mem_essImage, ihom.adjunction, obj_mem_essImage, otimes, reflector, reflectorAdjunction, unitCompPartialBijective
-/
noncomputable def bijection (A B : C) (X : D) :
    ((reflector i).obj (A otimes B) ⟶ X) ≃ ((reflector i).obj A otimes (reflector i).obj B ⟶ X) :=
  calc
    _ ≃ (A otimes B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B otimes A ⟶ i.obj X) := (β_ _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (B otimes i.obj ((reflector i).obj A) ⟶ i.obj X) := ((ihom.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A) otimes B ⟶ i.obj X) :=
      ((β_ _ _).homCongr (Iso.refl _))
    _ ≃ (B ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) := (ihom.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj B) ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (i.obj ((reflector i).obj A) otimes i.obj ((reflector i).obj B) ⟶ i.obj X) :=
      ((ihom.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A otimes (reflector i).obj B) ⟶ i.obj X) :=
      haveI : Limits.PreservesLimits i := (reflectorAdjunction i).rightAdjoint_preservesLimits
      haveI := Limits.preservesSmallestLimits_of_preservesLimits i
      Iso.homCongr (prodComparisonIso _ _ _).symm (Iso.refl (i.obj X))
    _ ≃ ((reflector i).obj A otimes (reflector i).obj B ⟶ X) :=
      i.fullyFaithfulOfReflective.homEquiv.symm

set_option backward.defeqAttrib.useBackward true in
/--
theorem `bijection_symm_apply_id` / 定理 `bijection_symm_apply_id`

English:
theorem bijection_symm_apply_id
  given: (A B : C)
  proof: by
  simp only [bijection, Equiv.trans_def, curriedTensor_obj_obj, Equiv.symm_trans_apply,
    Equiv.symm_symm, Functor.FullyFaithful.homEquiv_apply, Functor.map_id, Iso.homCongr_symm,
    Iso.symm_symm_eq, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    unitCompPartialBijecti

中文:
定理 bijection_symm_apply_id
  条件: (A B : C)
  证明: by
  simp only [bijection, Equiv.trans_def, curriedTensor_obj_obj, Equiv.symm_trans_apply,
    Equiv.symm_symm, Functor.FullyFaithful.homEquiv_apply, Functor.map_id, Iso.homCongr_symm,
    Iso.symm_symm_eq, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    unitCompPartialBijecti

Depends on / 依赖: Category, Category.comp_id, Equiv.symm_symm, Equiv.symm_trans_apply, Equiv.trans_def, FullyFaithful, Functor, Functor.FullyFaithful.homEquiv_apply, Functor.comp_obj, Functor.id_obj, Functor.map_id, Iso.homCongr_apply, Iso.homCongr_symm, Iso.refl_hom, Iso.refl_symm, Iso.symm_inv, Iso.symm_symm_eq, bijection, comp_id, comp_obj
-/
theorem bijection_symm_apply_id (A B : C) :
    (bijection i A B _).symm (𝟙 _) = prodComparison _ _ _ := by
  simp only [bijection, Equiv.trans_def, curriedTensor_obj_obj, Equiv.symm_trans_apply,
    Equiv.symm_symm, Functor.FullyFaithful.homEquiv_apply, Functor.map_id, Iso.homCongr_symm,
    Iso.symm_symm_eq, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    unitCompPartialBijective_symm_apply, Functor.id_obj, Functor.comp_obj, Iso.symm_inv]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  rw [uncurry_natural_left]; rw [uncurry_curry]; rw [uncurry_natural_left]; rw [uncurry_curry]; rw [← BraidedCategory.braiding_naturality_left_assoc]; rw [SymmetricCategory.symmetry_assoc]; rw [← MonoidalCategory.whisker_exchange_assoc]; rw [← tensorHom_def'_assoc]; rw [Adjunction.homEquiv_symm_apply]; rw [← Adjunction.eq_unit_comp_map_iff]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [prodComparisonIso_hom i ((reflector i).obj A) ((reflector i).obj B)]
  apply hom_ext
  · rw [tensorHom_fst, Category.assoc, Category.assoc, prodComparison_fst, ← i.map_comp,
    prodComparison_fst]
    apply (reflectorAdjunction i).unit.naturality
  · rw [tensorHom_snd, Category.assoc, Category.assoc, prodComparison_snd, ← i.map_comp,
    prodComparison_snd]
    apply (reflectorAdjunction i).unit.naturality

set_option backward.defeqAttrib.useBackward true in
/--
theorem `bijection_natural` / 定理 `bijection_natural`

English:
theorem bijection_natural
  given: (A B : C) (X X' : D) (f : (reflector i).obj (A otimes B) ⟶ X) (g : X ⟶ X')
  proof: by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage]; rw

中文:
定理 bijection_natural
  条件: (A B : C) (X X' : D) (f : (reflector i).obj (A otimes B) ⟶ X) (g : X ⟶ X')
  证明: by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage]; rw

Depends on / 依赖: bijection
-/
theorem bijection_natural (A B : C) (X X' : D) (f : (reflector i).obj (A otimes B) ⟶ X) (g : X ⟶ X') :
    bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g := by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage]; rw [i.map_comp]; rw [Adjunction.homEquiv_unit]; rw [Adjunction.homEquiv_unit]
  simp only [Category.comp_id, Functor.map_comp, Functor.FullyFaithful.map_preimage, Category.assoc]
  rw [← Category.assoc]; rw [← Category.assoc]; rw [curry_natural_right _ (i.map g)]; rw [unitCompPartialBijective_natural]; rw [uncurry_natural_right]; rw [← Category.assoc]; rw [curry_natural_right]; rw [unitCompPartialBijective_natural]; rw [uncurry_natural_right]; rw [Category.assoc]

/--
theorem `prodComparison_iso` / 定理 `prodComparison_iso`

English:
theorem prodComparison_iso
  given: (A B : C)
  statement: IsIso
  proof: ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff]; rw [bijection_natural]; rw [← bijection_symm_apply_id]; rw [Equiv.apply_symm_apply]; rw [Category.id_comp],
      by rw [← bijection_natural, Category.id_comp, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply]⟩

中文:
定理 prodComparison_iso
  条件: (A B : C)
  结论: IsIso
  证明: ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff]; rw [bijection_natural]; rw [← bijection_symm_apply_id]; rw [Equiv.apply_symm_apply]; rw [Category.id_comp],
      by rw [← bijection_natural, Category.id_comp, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply]⟩

Depends on / 依赖: Category, Category.id_comp, Equiv.apply_symm_apply, apply_symm_apply, bijection, bijection_natural, bijection_symm_apply_id, eq_iff, id_comp, injective, injective.eq_iff
-/
theorem prodComparison_iso (A B : C) : IsIso
    (prodComparison (reflector i) A B) :=
  ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff]; rw [bijection_natural]; rw [← bijection_symm_apply_id]; rw [Equiv.apply_symm_apply]; rw [Category.id_comp],
      by rw [← bijection_natural, Category.id_comp, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply]⟩⟩

attribute [local instance] prodComparison_iso

open Limits

/--
lemma `preservesBinaryProducts_of_exponentialIdeal` / 引理 `preservesBinaryProducts_of_exponentialIdeal`

English:
lemma preservesBinaryProducts_of_exponentialIdeal
  proof: letI := preservesLimit_pair_of_isIso_prodComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

中文:
引理 preservesBinaryProducts_of_exponentialIdeal
  证明: letI := preservesLimit_pair_of_isIso_prodComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

Depends on / 依赖: K.obj, Limits, Limits.preservesLimit_of_iso_diagram, WalkingPair, WalkingPair.left, WalkingPair.right, diagramIsoPair, preservesLimit_of_iso_diagram, preservesLimit_pair_of_isIso_prodComparison, reflector
-/
lemma preservesBinaryProducts_of_exponentialIdeal :
    PreservesLimitsOfShape (Discrete WalkingPair) (reflector i) where
  preservesLimit {K} :=
    letI := preservesLimit_pair_of_isIso_prodComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

/--
lemma `Limits.PreservesFiniteProducts.of_exponentialIdeal` / 引理 `Limits.PreservesFiniteProducts.of_exponentialIdeal`

English:
lemma Limits.PreservesFiniteProducts.of_exponentialIdeal
  statement: PreservesFiniteProducts (reflector i)
  proof: have := preservesBinaryProducts_of_exponentialIdeal i
  have : PreservesLimitsOfShape _ (reflector i) := leftAdjoint_preservesTerminal_of_reflective.{0} i
  .of_preserves_binary_and_terminal _

中文:
引理 Limits.PreservesFiniteProducts.of_exponentialIdeal
  结论: PreservesFiniteProducts (reflector i)
  证明: have := preservesBinaryProducts_of_exponentialIdeal i
  have : PreservesLimitsOfShape _ (reflector i) := leftAdjoint_preservesTerminal_of_reflective.{0} i
  .of_preserves_binary_and_terminal _

Depends on / 依赖: PreservesLimitsOfShape, leftAdjoint_preservesTerminal_of_reflective, of_preserves_binary_and_terminal, preservesBinaryProducts_of_exponentialIdeal, reflector
-/
lemma Limits.PreservesFiniteProducts.of_exponentialIdeal : PreservesFiniteProducts (reflector i) :=
  have := preservesBinaryProducts_of_exponentialIdeal i
  have : PreservesLimitsOfShape _ (reflector i) := leftAdjoint_preservesTerminal_of_reflective.{0} i
  .of_preserves_binary_and_terminal _

end

end CategoryTheory
