/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `BraidedCategory` another typeclass, but then have `SymmetricCategory` extend this.
The rationale is that we are not carrying any additional data, just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

## References

* [Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, Victor Ostrik, *Tensor categories*][egno15]

-/

@[expose] public section



universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/--
Definition of `BraidedCategory` / `BraidedCategory` 的定义

English:
class BraidedCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  axioms and operations (5):
    - braiding : forall X Y : C, X otimes Y ≅ Y otimes X
    - braiding_naturality_right : forall (X : C) {Y Z : C} (f : Y ⟶ Z), X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X  [default: by cat_disch]
    - braiding_naturality_left : forall {X Y : C} (f : X ⟶ Y) (Z : C), f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f  [default: by cat_disch]
    - hexagon_forward : forall X Y Z : C, (α_ X Y Z).hom ≫ (braiding X (Y otimes Z)).hom ≫ (α_ Y Z X).hom = ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom)  [default: by cat_disch]
    - hexagon_reverse : forall X Y Z : C, (α_ X Y Z).inv ≫ (braiding (X otimes Y) Z).hom ≫ (α_ Z X Y).inv = (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y)  [default: by cat_disch]

中文:
类 辫范畴
  参数: (C : 类型u) [范畴.{v} C] [幺半群范畴.{v} C]
  公理与运算 (5 个):
    - braiding : 对任意 X Y : C, X otimes Y ≅ Y otimes X
    - braiding_naturality_right : 对任意 (X : C) {Y Z : C} (f : Y ⟶ Z), X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X  [默认: by cat_disch]
    - braiding_naturality_left : 对任意 {X Y : C} (f : X ⟶ Y) (Z : C), f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f  [默认: by cat_disch]
    - hexagon_forward : 对任意 X Y Z : C, (α_ X Y Z).hom ≫ (braiding X (Y otimes Z)).hom ≫ (α_ Y Z X).hom = ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom)  [默认: by cat_disch]
    - hexagon_reverse : 对任意 X Y Z : C, (α_ X Y Z).inv ≫ (braiding (X otimes Y) Z).hom ≫ (α_ Z X Y).inv = (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y)  [默认: by cat_disch]

Depends on / 依赖: braiding, braiding_naturality_left, cat_disch
-/
class BraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  /-- The braiding natural isomorphism. -/
  braiding : forall X Y : C, X otimes Y ≅ Y otimes X
  braiding_naturality_right :
    forall (X : C) {Y Z : C} (f : Y ⟶ Z),
      X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
    cat_disch
  braiding_naturality_left :
    forall {X Y : C} (f : X ⟶ Y) (Z : C),
      f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
    cat_disch
  /-- The first hexagon identity. -/
  hexagon_forward :
    forall X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y otimes Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    cat_disch
  /-- The second hexagon identity. -/
  hexagon_reverse :
    forall X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X otimes Y) Z).hom ≫ (α_ Z X Y).inv =
        (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
    cat_disch

attribute [reassoc (attr := simp)]
  BraidedCategory.braiding_naturality_left
  BraidedCategory.braiding_naturality_right
attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open BraidedCategory

@[inherit_doc]
notation "β_" => BraidedCategory.braiding

namespace BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]

@[simp, reassoc]
/--
theorem `braiding_tensor_left_hom` / 定理 `braiding_tensor_left_hom`

English:
theorem braiding_tensor_left_hom
  given: (X Y Z : C)
  proof: by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[simp, reassoc]

中文:
定理 braiding_tensor_left_hom
  条件: (X Y Z : C)
  证明: by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[simp, reassoc]

Depends on / 依赖: cancel_epi, cancel_mono, hexagon_reverse
-/
theorem braiding_tensor_left_hom (X Y Z : C) :
    (β_ (X otimes Y) Z).hom =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫
        (β_ X Z).hom ▷ Y ≫ (α_ Z X Y).hom := by
  apply (cancel_epi (α_ X Y Z).inv).1
  apply (cancel_mono (α_ Z X Y).inv).1
  simp [hexagon_reverse]

@[simp, reassoc]
/--
theorem `braiding_tensor_right_hom` / 定理 `braiding_tensor_right_hom`

English:
theorem braiding_tensor_right_hom
  given: (X Y Z : C)
  proof: by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[simp, reassoc]

中文:
定理 braiding_tensor_right_hom
  条件: (X Y Z : C)
  证明: by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[simp, reassoc]

Depends on / 依赖: Subtype, Subtype.ext, cancel_epi, cancel_mono, hexagon_forward, isLocallyInjective_of_injective
-/
theorem braiding_tensor_right_hom (X Y Z : C) :
    (β_ X (Y otimes Z)).hom =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv := by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply (cancel_mono (α_ Y Z X).hom).1
  simp [hexagon_forward]

@[simp, reassoc]
/--
theorem `braiding_tensor_left_inv` / 定理 `braiding_tensor_left_inv`

English:
theorem braiding_tensor_left_inv
  given: (X Y Z : C)
  proof: eq_of_inv_eq_inv (by simp)

@[simp, reassoc]

中文:
定理 braiding_tensor_left_inv
  条件: (X Y Z : C)
  证明: eq_of_inv_eq_inv (by simp)

@[simp, reassoc]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem braiding_tensor_left_inv (X Y Z : C) :
    (β_ (X otimes Y) Z).inv =
      (α_ Z X Y).inv ≫ (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫
        X ◁ (β_ Y Z).inv ≫ (α_ X Y Z).inv :=
  eq_of_inv_eq_inv (by simp)

@[simp, reassoc]
/--
theorem `braiding_tensor_right_inv` / 定理 `braiding_tensor_right_inv`

English:
theorem braiding_tensor_right_inv
  given: (X Y Z : C)
  proof: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

中文:
定理 braiding_tensor_right_inv
  条件: (X Y Z : C)
  证明: eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_inv_eq_inv
-/
theorem braiding_tensor_right_inv (X Y Z : C) :
    (β_ X (Y otimes Z)).inv =
      (α_ Y Z X).hom ≫ Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫
        (β_ X Y).inv ▷ Z ≫ (α_ X Y Z).hom :=
  eq_of_inv_eq_inv (by simp)

@[reassoc (attr := simp)]
/--
theorem `braiding_naturality` / 定理 `braiding_naturality`

English:
theorem braiding_naturality
  given: {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  proof: by
  rw [tensorHom_def' f g]; rw [tensorHom_def g f]
  simp_rw [Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc]

@[reassoc (attr := simp)]

中文:
定理 braiding_naturality
  条件: {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  证明: by
  rw [tensorHom_def' f g]; rw [tensorHom_def g f]
  simp_rw [Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc, simp_rw, tensorHom_def
-/
theorem braiding_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f otimesₘ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g otimesₘ f) := by
  rw [tensorHom_def' f g]; rw [tensorHom_def g f]
  simp_rw [Category.assoc, braiding_naturality_left, braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
/--
theorem `braiding_inv_naturality_right` / 定理 `braiding_inv_naturality_right`

English:
theorem braiding_inv_naturality_right
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  proof: CommSq.w .vert_inv .mk braiding_naturality_left f X

@[reassoc (attr := simp)]

中文:
定理 braiding_inv_naturality_right
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  证明: CommSq.w .vert_inv .mk braiding_naturality_left f X

@[reassoc (attr := simp)]

Depends on / 依赖: CommSq, CommSq.w, braiding_naturality_left, vert_inv
-/
theorem braiding_inv_naturality_right (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ f ≫ (β_ Z X).inv = (β_ Y X).inv ≫ f ▷ X :=
CommSq.w .vert_inv .mk braiding_naturality_left f X

@[reassoc (attr := simp)]
/--
theorem `braiding_inv_naturality_left` / 定理 `braiding_inv_naturality_left`

English:
theorem braiding_inv_naturality_left
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: CommSq.w .vert_inv .mk braiding_naturality_right Z f

@[reassoc (attr := simp)]

中文:
定理 braiding_inv_naturality_left
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: CommSq.w .vert_inv .mk braiding_naturality_right Z f

@[reassoc (attr := simp)]

Depends on / 依赖: CommSq, CommSq.w, braiding_naturality_right, vert_inv
-/
theorem braiding_inv_naturality_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z ≫ (β_ Z Y).inv = (β_ Z X).inv ≫ Z ◁ f :=
CommSq.w .vert_inv .mk braiding_naturality_right Z f

@[reassoc (attr := simp)]
/--
theorem `braiding_inv_naturality` / 定理 `braiding_inv_naturality`

English:
theorem braiding_inv_naturality
  given: {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  proof: CommSq.w .vert_inv .mk braiding_naturality g f

中文:
定理 braiding_inv_naturality
  条件: {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  证明: CommSq.w .vert_inv .mk braiding_naturality g f

Depends on / 依赖: CommSq, CommSq.w, braiding_naturality, vert_inv
-/
theorem braiding_inv_naturality {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f otimesₘ g) ≫ (β_ Y' Y).inv = (β_ X' X).inv ≫ (g otimesₘ f) :=
CommSq.w .vert_inv .mk braiding_naturality g f

set_option backward.defeqAttrib.useBackward true in
/-- In a braided monoidal category, the functors `tensorLeft X` and
`tensorRight X` are isomorphic. -/
@[simps]
/--
Definition of `tensorLeftIsoTensorRight` / `tensorLeftIsoTensorRight` 的定义

English:
definition tensorLeftIsoTensorRight
  signature: (X : C)
  body: { app Y := (β_ X Y).hom }
  inv := { app Y := (β_ X Y).inv }

中文:
定义 tensorLeftIsoTensorRight
  签名: (X : C)
  定义体: { app Y := (β_ X Y).hom }
  inv := { app Y := (β_ X Y).inv }
-/
def tensorLeftIsoTensorRight (X : C) :
    tensorLeft X ≅ tensorRight X where
  hom := { app Y := (β_ X Y).hom }
  inv := { app Y := (β_ X Y).inv }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The braiding isomorphism as a natural isomorphism of bifunctors `C ⥤ C ⥤ C`. -/
@[simps!]
/--
Definition of `curriedBraidingNatIso` / `curriedBraidingNatIso` 的定义

English:
definition curriedBraidingNatIso
  signature: : curriedTensor C ≅ (curriedTensor C).flip
  body: NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => β_ X Y))

@[reassoc]

中文:
定义 curriedBraiding自然数Iso
  签名: : curriedTensor C ≅ (curriedTensor C).flip
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => β_ X Y))

@[reassoc]

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def curriedBraidingNatIso : curriedTensor C ≅ (curriedTensor C).flip :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => β_ X Y))

@[reassoc]
/--
theorem `yang_baxter` / 定理 `yang_baxter`

English:
theorem yang_baxter
  given: (X Y Z : C)
  proof: by
  rw [← braiding_tensor_right_hom_assoc X Y Z]; rw [← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id]; rw [comp_id]; rw [← braiding_naturality_right]; rw [braiding_tensor_right_hom]

中文:
定理 yang_baxter
  条件: (X Y Z : C)
  证明: by
  rw [← braiding_tensor_right_hom_assoc X Y Z]; rw [← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id]; rw [comp_id]; rw [← braiding_naturality_right]; rw [braiding_tensor_right_hom]

Depends on / 依赖: Iso.hom_inv_id, braiding_naturality_right, braiding_tensor_right_hom, braiding_tensor_right_hom_assoc, cancel_mono, comp_id, hom_inv_id, repeat
-/
theorem yang_baxter (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
    Y ◁ (β_ X Z).hom ≫ (α_ Y Z X).inv ≫ (β_ Y Z).hom ▷ X ≫ (α_ Z Y X).hom =
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫
      (α_ Z X Y).hom ≫ Z ◁ (β_ X Y).hom := by
  rw [← braiding_tensor_right_hom_assoc X Y Z]; rw [← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id]; rw [comp_id]; rw [← braiding_naturality_right]; rw [braiding_tensor_right_hom]

/--
theorem `yang_baxter'` / 定理 `yang_baxter'`

English:
theorem yang_baxter'
  given: (X Y Z : C)
  proof: by
  rw [← cancel_epi (α_ X Y Z).inv]; rw [← cancel_mono (α_ Z Y X).hom]
  convert! yang_baxter X Y Z using 1
  all_goals monoidal

中文:
定理 yang_baxter'
  条件: (X Y Z : C)
  证明: by
  rw [← cancel_epi (α_ X Y Z).inv]; rw [← cancel_mono (α_ Z Y X).hom]
  convert! yang_baxter X Y Z using 1
  all_goals monoidal

Depends on / 依赖: all_goals, cancel_epi, cancel_mono, convert, monoidal, yang_baxter
-/
theorem yang_baxter' (X Y Z : C) :
    (β_ X Y).hom ▷ Z otimes≫ Y ◁ (β_ X Z).hom otimes≫ (β_ Y Z).hom ▷ X =
      𝟙 _ otimes≫ (X ◁ (β_ Y Z).hom otimes≫ (β_ X Z).hom ▷ Y otimes≫ Z ◁ (β_ X Y).hom) otimes≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv]; rw [← cancel_mono (α_ Z Y X).hom]
  convert! yang_baxter X Y Z using 1
  all_goals monoidal

/--
theorem `yang_baxter_iso` / 定理 `yang_baxter_iso`

English:
theorem yang_baxter_iso
  given: (X Y Z : C)
  proof: Iso.ext (yang_baxter X Y Z)

中文:
定理 yang_baxter_iso
  条件: (X Y Z : C)
  证明: Iso.ext (yang_baxter X Y Z)

Depends on / 依赖: Iso.ext, Sheaf.image, infer_instance, yang_baxter
-/
theorem yang_baxter_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫
    whiskerLeftIso Y (β_ X Z) ≪≫ (α_ Y Z X).symm ≪≫
    whiskerRightIso (β_ Y Z) X ≪≫ (α_ Z Y X) =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫
      whiskerRightIso (β_ X Z) Y ≪≫ α_ Z X Y ≪≫
      whiskerLeftIso Z (β_ X Y) := Iso.ext (yang_baxter X Y Z)

/--
theorem `hexagon_forward_iso` / 定理 `hexagon_forward_iso`

English:
theorem hexagon_forward_iso
  given: (X Y Z : C)
  proof: Iso.ext (hexagon_forward X Y Z)

中文:
定理 hexagon_forward_iso
  条件: (X Y Z : C)
  证明: Iso.ext (hexagon_forward X Y Z)

Depends on / 依赖: Iso.ext, hexagon_forward
-/
theorem hexagon_forward_iso (X Y Z : C) :
    α_ X Y Z ≪≫ β_ X (Y otimes Z) ≪≫ α_ Y Z X =
      whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) :=
  Iso.ext (hexagon_forward X Y Z)

/--
theorem `hexagon_reverse_iso` / 定理 `hexagon_reverse_iso`

English:
theorem hexagon_reverse_iso
  given: (X Y Z : C)
  proof: Iso.ext (hexagon_reverse X Y Z)

@[reassoc]

中文:
定理 hexagon_reverse_iso
  条件: (X Y Z : C)
  证明: Iso.ext (hexagon_reverse X Y Z)

@[reassoc]

Depends on / 依赖: Iso.ext, hexagon_reverse
-/
theorem hexagon_reverse_iso (X Y Z : C) :
    (α_ X Y Z).symm ≪≫ β_ (X otimes Y) Z ≪≫ (α_ Z X Y).symm =
      whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm ≪≫ whiskerRightIso (β_ X Z) Y :=
  Iso.ext (hexagon_reverse X Y Z)

@[reassoc]
/--
theorem `hexagon_forward_inv` / 定理 `hexagon_forward_inv`

English:
theorem hexagon_forward_inv
  given: (X Y Z : C)
  proof: by
  simp

@[reassoc]

中文:
定理 hexagon_forward_inv
  条件: (X Y Z : C)
  证明: by
  simp

@[reassoc]
-/
theorem hexagon_forward_inv (X Y Z : C) :
    (α_ Y Z X).inv ≫ (β_ X (Y otimes Z)).inv ≫ (α_ X Y Z).inv =
      Y ◁ (β_ X Z).inv ≫ (α_ Y X Z).inv ≫ (β_ X Y).inv ▷ Z := by
  simp

@[reassoc]
/--
theorem `hexagon_reverse_inv` / 定理 `hexagon_reverse_inv`

English:
theorem hexagon_reverse_inv
  given: (X Y Z : C)
  proof: by
  simp

中文:
定理 hexagon_reverse_inv
  条件: (X Y Z : C)
  证明: by
  simp
-/
theorem hexagon_reverse_inv (X Y Z : C) :
    (α_ Z X Y).hom ≫ (β_ (X otimes Y) Z).inv ≫ (α_ X Y Z).hom =
      (β_ X Z).inv ▷ Y ≫ (α_ X Z Y).hom ≫ X ◁ (β_ Y Z).inv := by
  simp

end BraidedCategory

-- FIXME: `reassoc_of%` should unfold `autoParam`.
/--
Verifying the axioms for a braiding by checking that the candidate braiding is sent to a braiding
by a faithful monoidal functor.
-/
@[instance_reducible]
/--
Definition of `BraidedCategory.ofFaithful` / `BraidedCategory.ofFaithful` 的定义

English:
definition BraidedCategory.ofFaithful
  signature: {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
  body: β
  braiding_naturality_left := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp]; rw [← μ_natural_left_assoc]; rw [w]; rw [Functor.map_comp]; rw [reassoc_of% w]; rw [braiding_naturality_left_assoc]; rw [μ_natural_right]
  braiding_naturality_right := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp]; rw [← μ_natural_right_assoc]; rw [w]; rw [Functor.map_comp]; rw [reassoc_of% w]; rw [braiding_naturality_right_assoc]; rw [μ_natural_left]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (μ F _ _ ▷ _)).1 ?_
    rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [←
      μ_natural_left_assoc]; rw [← comp_whiskerRight_assoc]; rw [w]; rw [comp_whiskerRight_assoc]; rw [Functor.LaxMonoidal.associativity_assoc]; rw [Functor.LaxMonoidal.associativity_assoc]; rw [← μ_natural_right]; rw [←
      whiskerLeft_comp_assoc]; rw [w]; rw [whiskerLeft_comp_assoc]; rw [reassoc_of% w]; rw [braiding_naturality_right_assoc]; rw [Functor.LaxMonoidal.associativity]; rw [hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (_ ◁ μ F _ _)).1 ?_
    rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [←
      μ_natural_right_assoc]; rw [← whiskerLeft_comp_assoc]; rw [w]; rw [whiskerLeft_comp_assoc]; rw [Functor.LaxMonoidal.associativity_inv_assoc]; rw [Functor.LaxMonoidal.associativity_inv_assoc]; rw [← μ_natural_left]; rw [← comp_whiskerRight_assoc]; rw [w]; rw [comp_whiskerRight_assoc]; rw [reassoc_of% w]; rw [braiding_naturality_left_assoc]; rw [Functor.LaxMonoidal.associativity_inv]; rw [hexagon_reverse_assoc]

中文:
定义 辫范畴.ofFaithful
  签名: {C D : 类型} [范畴* C] [范畴* D] [幺半群范畴 C]
  定义体: β
  braiding_naturality_left := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp]; rw [← μ_natural_left_assoc]; rw [w]; rw [Functor.map_comp]; rw [reassoc_of% w]; rw [braiding_naturality_left_assoc]; rw [μ_natural_right]
  braiding_naturality_right := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp]; rw [← μ_natural_right_assoc]; rw [w]; rw [Functor.map_comp]; rw [reassoc_of% w]; rw [braiding_naturality_right_assoc]; rw [μ_natural_left]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (μ F _ _ ▷ _)).1 ?_
    rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [←
      μ_natural_left_assoc]; rw [← comp_whiskerRight_assoc]; rw [w]; rw [comp_whiskerRight_assoc]; rw [Functor.LaxMonoidal.associativity_assoc]; rw [Functor.LaxMonoidal.associativity_assoc]; rw [← μ_natural_right]; rw [←
      whiskerLeft_comp_assoc]; rw [w]; rw [whiskerLeft_comp_assoc]; rw [reassoc_of% w]; rw [braiding_naturality_right_assoc]; rw [Functor.LaxMonoidal.associativity]; rw [hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (_ ◁ μ F _ _)).1 ?_
    rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [←
      μ_natural_right_assoc]; rw [← whiskerLeft_comp_assoc]; rw [w]; rw [whiskerLeft_comp_assoc]; rw [Functor.LaxMonoidal.associativity_inv_assoc]; rw [Functor.LaxMonoidal.associativity_inv_assoc]; rw [← μ_natural_left]; rw [← comp_whiskerRight_assoc]; rw [w]; rw [comp_whiskerRight_assoc]; rw [reassoc_of% w]; rw [braiding_naturality_left_assoc]; rw [Functor.LaxMonoidal.associativity_inv]; rw [hexagon_reverse_assoc]

Depends on / 依赖: BraidedCategory, F.map_injective, Functor, Functor.map_comp, braiding, braiding_naturality_left, braiding_naturality_left_assoc, braiding_naturality_right, cancel_epi, cat_disch, intros, map_comp, map_injective, reassoc_of
-/
def BraidedCategory.ofFaithful {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Faithful] [BraidedCategory D]
    (β : forall X Y : C, X otimes Y ≅ Y otimes X)
    (w : forall X Y, μ F _ _ ≫ F.map (β X Y).hom = (β_ _ _).hom ≫ μ F _ _ := by cat_disch) :
    BraidedCategory C where
  braiding := β
  braiding_naturality_left := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp]; rw [← μ_natural_left_assoc]; rw [w]; rw [Functor.map_comp]; rw [reassoc_of% w]; rw [braiding_naturality_left_assoc]; rw [μ_natural_right]
  braiding_naturality_right := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F ?_ ?_)).1 ?_
    rw [Functor.map_comp]; rw [← μ_natural_right_assoc]; rw [w]; rw [Functor.map_comp]; rw [reassoc_of% w]; rw [braiding_naturality_right_assoc]; rw [μ_natural_left]
  hexagon_forward := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (μ F _ _ ▷ _)).1 ?_
    rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [←
      μ_natural_left_assoc]; rw [← comp_whiskerRight_assoc]; rw [w]; rw [comp_whiskerRight_assoc]; rw [Functor.LaxMonoidal.associativity_assoc]; rw [Functor.LaxMonoidal.associativity_assoc]; rw [← μ_natural_right]; rw [←
      whiskerLeft_comp_assoc]; rw [w]; rw [whiskerLeft_comp_assoc]; rw [reassoc_of% w]; rw [braiding_naturality_right_assoc]; rw [Functor.LaxMonoidal.associativity]; rw [hexagon_forward_assoc]
  hexagon_reverse := by
    intros
    apply F.map_injective
    refine (cancel_epi (μ F _ _)).1 ?_
    refine (cancel_epi (_ ◁ μ F _ _)).1 ?_
    rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [←
      μ_natural_right_assoc]; rw [← whiskerLeft_comp_assoc]; rw [w]; rw [whiskerLeft_comp_assoc]; rw [Functor.LaxMonoidal.associativity_inv_assoc]; rw [Functor.LaxMonoidal.associativity_inv_assoc]; rw [← μ_natural_left]; rw [← comp_whiskerRight_assoc]; rw [w]; rw [comp_whiskerRight_assoc]; rw [reassoc_of% w]; rw [braiding_naturality_left_assoc]; rw [Functor.LaxMonoidal.associativity_inv]; rw [hexagon_reverse_assoc]

/-- Pull back a braiding along a fully faithful monoidal functor. -/
@[instance_reducible]
/--
Definition of `BraidedCategory.ofFullyFaithful` / `BraidedCategory.ofFullyFaithful` 的定义

English:
definition BraidedCategory.ofFullyFaithful
  signature: {C D : Type*} [Category* C] [Category* D]
  body: .ofFaithful F fun X Y => F.preimageIso ((μIso F _ _).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ μIso F _ _)

中文:
定义 辫范畴.ofFullyFaithful
  签名: {C D : 类型} [范畴* C] [范畴* D]
  定义体: .ofFaithful F fun X Y => F.preimageIso ((μIso F _ _).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ μIso F _ _)

Depends on / 依赖: F.obj, F.preimageIso, ofFaithful, preimageIso
-/
noncomputable def BraidedCategory.ofFullyFaithful {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [BraidedCategory D] : BraidedCategory C :=
  .ofFaithful F fun X Y => F.preimageIso ((μIso F _ _).symm ≪≫ β_ (F.obj X) (F.obj Y) ≪≫ μIso F _ _)

section

/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories", Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

/--
theorem `braiding_leftUnitor_aux₁` / 定理 `braiding_leftUnitor_aux₁`

English:
theorem braiding_leftUnitor_aux₁
  given: (X : C)
  proof: by
  monoidal

中文:
定理 braiding_leftUnitor_aux₁
  条件: (X : C)
  证明: by
  monoidal

Depends on / 依赖: monoidal
-/
theorem braiding_leftUnitor_aux₁ (X : C) :
    (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
        (𝟙_ C ◁ (β_ X (𝟙_ C)).inv) ≫ (α_ _ X _).inv ≫ ((fun_ X).hom ▷ _) =
      ((fun_ _).hom ▷ X) ≫ (β_ X (𝟙_ C)).inv := by
  monoidal

/--
theorem `braiding_leftUnitor_aux₂` / 定理 `braiding_leftUnitor_aux₂`

English:
theorem braiding_leftUnitor_aux₂
  given: (X : C)
  proof: calc
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((fun_ X).hom ▷ 𝟙_ C) =
      ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((fun_ X).hom ▷ 𝟙_ C) := by
      simp
    _ = ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).hom) ≫
          (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((fun_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((fun_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((fun_ _).hom ▷ X) ≫ (β_ X _).inv := by
      rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (fun_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_right]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (fun_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by rw [triangle]

@[reassoc]

中文:
定理 braiding_leftUnitor_aux₂
  条件: (X : C)
  证明: calc
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((fun_ X).hom ▷ 𝟙_ C) =
      ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((fun_ X).hom ▷ 𝟙_ C) := by
      simp
    _ = ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).hom) ≫
          (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((fun_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((fun_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((fun_ _).hom ▷ X) ≫ (β_ X _).inv := by
      rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (fun_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_right]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (fun_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by rw [triangle]

@[reassoc]

Depends on / 依赖: fun_
-/
theorem braiding_leftUnitor_aux₂ (X : C) :
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((fun_ X).hom ▷ 𝟙_ C) = (ρ_ X).hom ▷ 𝟙_ C :=
  calc
    ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ ((fun_ X).hom ▷ 𝟙_ C) =
      ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ ((fun_ X).hom ▷ 𝟙_ C) := by
      simp
    _ = ((β_ X (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).hom) ≫
          (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫ ((fun_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ (α_ _ _ _).hom ≫ (_ ◁ (β_ X _).inv) ≫ (α_ _ _ _).inv ≫
          ((fun_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ _ _ _).hom ≫ (β_ _ _).hom ≫ ((fun_ _).hom ▷ X) ≫ (β_ X _).inv := by
      rw [braiding_leftUnitor_aux₁]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (fun_ _).hom) ≫ (β_ _ _).hom ≫ (β_ X _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_right]); simp only [assoc]
    _ = (α_ _ _ _).hom ≫ (_ ◁ (fun_ _).hom) := by rw [Iso.hom_inv_id, comp_id]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by rw [triangle]

@[reassoc]
/--
theorem `braiding_leftUnitor` / 定理 `braiding_leftUnitor`

English:
theorem braiding_leftUnitor
  given: (X : C)
  statement: (β_ X (𝟙_ C)).hom ≫ (fun_ X).hom = (ρ_ X).hom
  proof: by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [braiding_leftUnitor_aux₂]

中文:
定理 braiding_leftUnitor
  条件: (X : C)
  结论: (β_ X (𝟙_ C)).hom ≫ (fun_ X).hom = (ρ_ X).hom
  证明: by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [braiding_leftUnitor_aux₂]

Depends on / 依赖: comp_whiskerRight, imageSieve_mem, whiskerRight_iff
-/
theorem braiding_leftUnitor (X : C) : (β_ X (𝟙_ C)).hom ≫ (fun_ X).hom = (ρ_ X).hom := by
  rw [← whiskerRight_iff]; rw [comp_whiskerRight]; rw [braiding_leftUnitor_aux₂]

/--
theorem `braiding_rightUnitor_aux₁` / 定理 `braiding_rightUnitor_aux₁`

English:
theorem braiding_rightUnitor_aux₁
  given: (X : C)
  proof: by
  simp

中文:
定理 braiding_rightUnitor_aux₁
  条件: (X : C)
  证明: by
  simp
-/
theorem braiding_rightUnitor_aux₁ (X : C) :
    (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
        ((β_ (𝟙_ C) X).inv ▷ 𝟙_ C) ≫ (α_ _ X _).hom ≫ (_ ◁ (ρ_ X).hom) =
      (X ◁ (ρ_ _).hom) ≫ (β_ (𝟙_ C) X).inv := by
  simp

/--
theorem `braiding_rightUnitor_aux₂` / 定理 `braiding_rightUnitor_aux₂`

English:
theorem braiding_rightUnitor_aux₂
  given: (X : C)
  proof: calc
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ▷ _) ≫
          ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫
          (𝟙_ C ◁ (ρ_ X).hom) := by
      (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (X ◁ (ρ_ _).hom) ≫ (β_ _ X).inv := by simp
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_left]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙_ C ◁ (fun_ X).hom := by rw [triangle_assoc_comp_right]

@[reassoc]

中文:
定理 braiding_rightUnitor_aux₂
  条件: (X : C)
  证明: calc
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ▷ _) ≫
          ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫
          (𝟙_ C ◁ (ρ_ X).hom) := by
      (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (X ◁ (ρ_ _).hom) ≫ (β_ _ X).inv := by simp
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_left]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙_ C ◁ (fun_ X).hom := by rw [triangle_assoc_comp_right]

@[reassoc]

Depends on / 依赖: hexagon_reverse, slice_lhs
-/
theorem braiding_rightUnitor_aux₂ (X : C) :
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) = 𝟙_ C ◁ (fun_ X).hom :=
  calc
    (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (𝟙_ C ◁ (β_ (𝟙_ C) X).hom) ≫ (α_ _ _ _).inv ≫ ((β_ _ X).hom ▷ _) ≫
          ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      simp
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (α_ _ _ _).inv ≫ ((β_ _ X).inv ▷ _) ≫ (α_ _ _ _).hom ≫
          (𝟙_ C ◁ (ρ_ X).hom) := by
      (slice_lhs 1 3 => rw [← hexagon_reverse]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ (β_ _ _).hom ≫ (X ◁ (ρ_ _).hom) ≫ (β_ _ X).inv := by simp
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) ≫ (β_ _ X).hom ≫ (β_ _ _).inv := by
      (slice_lhs 2 3 => rw [← braiding_naturality_left]); simp only [assoc]
    _ = (α_ _ _ _).inv ≫ ((ρ_ _).hom ▷ _) := by rw [Iso.hom_inv_id, comp_id]
    _ = 𝟙_ C ◁ (fun_ X).hom := by rw [triangle_assoc_comp_right]

@[reassoc]
/--
theorem `braiding_rightUnitor` / 定理 `braiding_rightUnitor`

English:
theorem braiding_rightUnitor
  given: (X : C)
  statement: (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (fun_ X).hom
  proof: by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [braiding_rightUnitor_aux₂]

@[reassoc, simp]

中文:
定理 braiding_rightUnitor
  条件: (X : C)
  结论: (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (fun_ X).hom
  证明: by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [braiding_rightUnitor_aux₂]

@[reassoc, simp]

Depends on / 依赖: whiskerLeft_comp, whiskerLeft_iff
-/
theorem braiding_rightUnitor (X : C) : (β_ (𝟙_ C) X).hom ≫ (ρ_ X).hom = (fun_ X).hom := by
  rw [← whiskerLeft_iff]; rw [whiskerLeft_comp]; rw [braiding_rightUnitor_aux₂]

@[reassoc, simp]
/--
theorem `braiding_tensorUnit_left` / 定理 `braiding_tensorUnit_left`

English:
theorem braiding_tensorUnit_left
  given: (X : C)
  statement: (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
  proof: by
  simp [← braiding_rightUnitor]

@[reassoc, simp]

中文:
定理 braiding_tensorUnit_left
  条件: (X : C)
  结论: (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
  证明: by
  simp [← braiding_rightUnitor]

@[reassoc, simp]

Depends on / 依赖: braiding_rightUnitor
-/
theorem braiding_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv := by
  simp [← braiding_rightUnitor]

@[reassoc, simp]
/--
theorem `braiding_inv_tensorUnit_left` / 定理 `braiding_inv_tensorUnit_left`

English:
theorem braiding_inv_tensorUnit_left
  given: (X : C)
  statement: (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (fun_ X).inv
  proof: by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_left]
  monoidal

@[reassoc]

中文:
定理 braiding_inv_tensorUnit_left
  条件: (X : C)
  结论: (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (fun_ X).inv
  证明: by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_left]
  monoidal

@[reassoc]

Depends on / 依赖: Iso.inv_ext, braiding_tensorUnit_left, inv_ext, monoidal
-/
theorem braiding_inv_tensorUnit_left (X : C) : (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (fun_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_left]
  monoidal

@[reassoc]
/--
theorem `leftUnitor_inv_braiding` / 定理 `leftUnitor_inv_braiding`

English:
theorem leftUnitor_inv_braiding
  given: (X : C)
  statement: (fun_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv
  proof: by
  simp

@[reassoc]

中文:
定理 leftUnitor_inv_braiding
  条件: (X : C)
  结论: (fun_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv
  证明: by
  simp

@[reassoc]
-/
theorem leftUnitor_inv_braiding (X : C) : (fun_ X).inv ≫ (β_ (𝟙_ C) X).hom = (ρ_ X).inv := by
  simp

@[reassoc]
/--
theorem `rightUnitor_inv_braiding` / 定理 `rightUnitor_inv_braiding`

English:
theorem rightUnitor_inv_braiding
  given: (X : C)
  statement: (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (fun_ X).inv
  proof: by
  apply (cancel_mono (fun_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]

@[reassoc, simp]

中文:
定理 rightUnitor_inv_braiding
  条件: (X : C)
  结论: (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (fun_ X).inv
  证明: by
  apply (cancel_mono (fun_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]

@[reassoc, simp]

Depends on / 依赖: Iso.inv_hom_id, braiding_leftUnitor, cancel_mono, fun_, inv_hom_id
-/
theorem rightUnitor_inv_braiding (X : C) : (ρ_ X).inv ≫ (β_ X (𝟙_ C)).hom = (fun_ X).inv := by
  apply (cancel_mono (fun_ X).hom).1
  simp only [assoc, braiding_leftUnitor, Iso.inv_hom_id]

@[reassoc, simp]
/--
theorem `braiding_tensorUnit_right` / 定理 `braiding_tensorUnit_right`

English:
theorem braiding_tensorUnit_right
  given: (X : C)
  statement: (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
  proof: by
  simp [← rightUnitor_inv_braiding]

@[reassoc, simp]

中文:
定理 braiding_tensorUnit_right
  条件: (X : C)
  结论: (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
  证明: by
  simp [← rightUnitor_inv_braiding]

@[reassoc, simp]

Depends on / 依赖: rightUnitor_inv_braiding
-/
theorem braiding_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv := by
  simp [← rightUnitor_inv_braiding]

@[reassoc, simp]
/--
theorem `braiding_inv_tensorUnit_right` / 定理 `braiding_inv_tensorUnit_right`

English:
theorem braiding_inv_tensorUnit_right
  given: (X : C)
  statement: (β_ X (𝟙_ C)).inv = (fun_ X).hom ≫ (ρ_ X).inv
  proof: by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_right]
  monoidal

中文:
定理 braiding_inv_tensorUnit_right
  条件: (X : C)
  结论: (β_ X (𝟙_ C)).inv = (fun_ X).hom ≫ (ρ_ X).inv
  证明: by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_right]
  monoidal

Depends on / 依赖: Iso.inv_ext, braiding_tensorUnit_right, inv_ext, monoidal
-/
theorem braiding_inv_tensorUnit_right (X : C) : (β_ X (𝟙_ C)).inv = (fun_ X).hom ≫ (ρ_ X).inv := by
  rw [Iso.inv_ext]
  rw [braiding_tensorUnit_right]
  monoidal

end

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric. -/
@[stacks 0FFW]
/--
Definition of `SymmetricCategory` / `SymmetricCategory` 的定义

English:
class SymmetricCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  axioms and operations (1):
    - symmetry : forall X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X otimes Y)  [default: by cat_disch]

中文:
类 对称范畴
  参数: (C : 类型u) [范畴.{v} C] [幺半群范畴.{v} C]
  公理与运算 (1 个):
    - symmetry : 对任意 X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X otimes Y)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class SymmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    BraidedCategory.{v} C where
  -- braiding symmetric:
  symmetry : forall X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X otimes Y) := by cat_disch

attribute [reassoc (attr := simp)] SymmetricCategory.symmetry

/--
lemma `SymmetricCategory.braiding_swap_eq_inv_braiding` / 引理 `SymmetricCategory.braiding_swap_eq_inv_braiding`

English:
lemma SymmetricCategory.braiding_swap_eq_inv_braiding
  statement: {C : Type u₁}
  proof: Iso.inv_ext' (symmetry X Y)

中文:
引理 对称范畴.braiding_swap_eq_inv_braiding
  结论: {C : 类型u₁}
  证明: Iso.inv_ext' (symmetry X Y)

Depends on / 依赖: Iso.inv_ext, inv_ext, symmetry
-/
lemma SymmetricCategory.braiding_swap_eq_inv_braiding {C : Type u₁}
    [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C] (X Y : C) :
    (β_ Y X).hom = (β_ X Y).inv := Iso.inv_ext' (symmetry X Y)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

/--
Definition of `Functor.LaxBraided` / `Functor.LaxBraided` 的定义

English:
class Functor.LaxBraided
  parameters: (F : C ⥤ D)
  extends: F.LaxMonoidal
  axioms and operations (1):
    - braided : forall X Y : C, μ X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ Y X  [default: by cat_disch]

中文:
类 函子.松弛辫
  参数: (F : C ⥤ D)
  继承: F.松弛幺半群
  公理与运算 (1 个):
    - braided : 对任意 X Y : C, μ X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ Y X  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class Functor.LaxBraided (F : C ⥤ D) extends F.LaxMonoidal where
  braided : forall X Y : C, μ X Y ≫ F.map (β_ X Y).hom =
    (β_ (F.obj X) (F.obj Y)).hom ≫ μ Y X := by cat_disch

namespace Functor.LaxBraided

attribute [reassoc] braided

/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : (𝟭 C).LaxBraided where

中文:
实例 id
  签名: : (𝟭 C).松弛辫 where
-/
instance id : (𝟭 C).LaxBraided where

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) (G : D ⥤ E) [F.LaxBraided] [G.LaxBraided] :
    (F ⋙ G).LaxBraided where
  braided X Y := by
    dsimp
    slice_lhs 2 3 =>
      rw [← CategoryTheory.Functor.map_comp]; rw [braided]; rw [CategoryTheory.Functor.map_comp]
    slice_lhs 1 2 => rw [braided]
    simp only [Category.assoc]

/--
Given two lax monoidal, monoidally isomorphic functors, if one is lax braided, so is the other.
-/
@[instance_reducible]
/--
Definition of `ofNatIso` / `ofNatIso` 的定义

English:
definition ofNatIso
  signature: {F G : C ⥤ D} (i : F ≅ G) [F.LaxBraided] [G.LaxMonoidal]
  body: by
    have (X Y : C) : μ G X Y = (i.inv.app X otimesₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app _ := by
      simp [NatTrans.IsMonoidal.tensor X Y, tensorHom_comp_tensorHom_assoc]
    rw [this X Y]; rw [this Y X]; rw [← braiding_naturality_assoc]; rw [← Functor.LaxBraided.braided_assoc]
    simp

中文:
定义 of自然数Iso
  签名: {F G : C ⥤ D} (i : F ≅ G) [F.松弛辫] [G.松弛幺半群]
  定义体: by
    have (X Y : C) : μ G X Y = (i.inv.app X otimesₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app _ := by
      simp [NatTrans.IsMonoidal.tensor X Y, tensorHom_comp_tensorHom_assoc]
    rw [this X Y]; rw [this Y X]; rw [← braiding_naturality_assoc]; rw [← Functor.LaxBraided.braided_assoc]
    simp

Depends on / 依赖: Functor, Functor.LaxBraided.braided_assoc, IsMonoidal, LaxBraided, NatTrans, NatTrans.IsMonoidal.tensor, braided_assoc, braiding_naturality_assoc, i.hom.app, i.inv.app, tensor, tensorHom_comp_tensorHom_assoc
-/
def ofNatIso {F G : C ⥤ D} (i : F ≅ G) [F.LaxBraided] [G.LaxMonoidal]
    [NatTrans.IsMonoidal i.hom] : G.LaxBraided where
  braided X Y := by
    have (X Y : C) : μ G X Y = (i.inv.app X otimesₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app _ := by
      simp [NatTrans.IsMonoidal.tensor X Y, tensorHom_comp_tensorHom_assoc]
    rw [this X Y]; rw [this Y X]; rw [← braiding_naturality_assoc]; rw [← Functor.LaxBraided.braided_assoc]
    simp

/-- Copy of a lax braided structure on a functor `F` with new `ε` and `μ` fields equal to the old
ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {F : C ⥤ D} (hF : F.LaxBraided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  body: hF.toLaxMonoidal.copy ε' μ' hε hμ
  braided X Y := hμ ▸ hF.braided X Y

中文:
定义 copy
  签名: {F : C ⥤ D} (hF : F.松弛辫) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  定义体: hF.toLaxMonoidal.copy ε' μ' hε hμ
  braided X Y := hμ ▸ hF.braided X Y

Depends on / 依赖: F.LaxBraided, LaxBraided, braided, cat_disch, hF.braided, hF.toLaxMonoidal.copy, toLaxMonoidal
-/
def copy {F : C ⥤ D} (hF : F.LaxBraided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y))
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch) : F.LaxBraided where
  __ := hF.toLaxMonoidal.copy ε' μ' hε hμ
  braided X Y := hμ ▸ hF.braided X Y

end Functor.LaxBraided

section

variable (C D)

/--
Definition of `LaxBraidedFunctor` / `LaxBraidedFunctor` 的定义

English:
structure LaxBraidedFunctor
  parameters: extends C ⥤ D
  extends: C ⥤ D
  axioms and operations (1):
    - laxBraided : toFunctor.LaxBraided  [default: by infer_instance]

中文:
结构 松弛辫函子
  参数: extends C ⥤ D
  继承: C ⥤ D
  公理与运算 (1 个):
    - laxBraided : toFunctor.松弛辫  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure LaxBraidedFunctor extends C ⥤ D where
  laxBraided : toFunctor.LaxBraided := by infer_instance

namespace LaxBraidedFunctor

variable {C D}

attribute [instance] laxBraided

/-- Constructor for `LaxBraidedFunctor C D`. -/
@[simps toFunctor]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (F : C ⥤ D) [F.LaxBraided]
  body: F

中文:
定义 of
  签名: (F : C ⥤ D) [F.松弛辫]
  定义体: F
-/
def of (F : C ⥤ D) [F.LaxBraided] : LaxBraidedFunctor C D where
  toFunctor := F

/-- The lax monoidal functor induced by a lax braided functor. -/
@[simps toFunctor]
/--
Definition of `toLaxMonoidalFunctor` / `toLaxMonoidalFunctor` 的定义

English:
definition toLaxMonoidalFunctor
  signature: (F : LaxBraidedFunctor C D)
  body: F.toFunctor

中文:
定义 toLaxMonoidalFunctor
  签名: (F : 松弛辫函子 C D)
  定义体: F.toFunctor

Depends on / 依赖: F.toFunctor, J.superset_covering, Subtype, Subtype.ext, superset_covering, toFunctor
-/
def toLaxMonoidalFunctor (F : LaxBraidedFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (LaxBraidedFunctor C D)
  body: inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

@[simp]

中文:
实例 :
  签名: 范畴 (松弛辫函子 C D)
  定义体: inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

@[simp]

Depends on / 依赖: Category, InducedCategory, toLaxMonoidalFunctor
-/
instance : Category (LaxBraidedFunctor C D) :=
  inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (F : LaxBraidedFunctor C D)
  proof: rfl

@[reassoc, simp]

中文:
引理 id_hom
  条件: (F : 松弛辫函子 C D)
  证明: rfl

@[reassoc, simp]
-/
lemma id_hom (F : LaxBraidedFunctor C D) :
    LaxMonoidalFunctor.Hom.hom (InducedCategory.Hom.hom (𝟙 F)) = 𝟙 _ := rfl

@[reassoc, simp]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {F G H : LaxBraidedFunctor C D} (α : F ⟶ G) (β : G ⟶ H)
  proof: rfl

@[ext]

中文:
引理 comp_hom
  条件: {F G H : 松弛辫函子 C D} (α : F ⟶ G) (β : G ⟶ H)
  证明: rfl

@[ext]
-/
lemma comp_hom {F G H : LaxBraidedFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom)
  proof: InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

中文:
引理 hom_ext
  条件: {F G : 松弛辫函子 C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom)
  证明: InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, LaxMonoidalFunctor, LaxMonoidalFunctor.hom_ext, hom_ext
-/
lemma hom_ext {F G : LaxBraidedFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) :
    α = β :=
  InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for morphisms in the category `LaxBraidedFunctor C D`. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {F G : LaxBraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f]
  body: ⟨f, inferInstance⟩

中文:
定义 homMk
  签名: {F G : 松弛辫函子 C D} (f : F.toFunctor ⟶ G.toFunctor) [自然变换.是幺半群 f]
  定义体: ⟨f, inferInstance⟩
-/
def homMk {F G : LaxBraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G := ⟨f, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for isomorphisms in the category `LaxBraidedFunctor C D`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {F G : LaxBraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
  body: homMk e.hom
  inv := homMk e.inv

中文:
定义 isoMk
  签名: {F G : 松弛辫函子 C D} (e : F.toFunctor ≅ G.toFunctor)
  定义体: homMk e.hom
  inv := homMk e.inv

Depends on / 依赖: e.hom
-/
def isoMk {F G : LaxBraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] :
    F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

/-- The forgetful functor from lax braided functors to lax monoidal functors. -/
@[simps! obj map]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : LaxBraidedFunctor C D ⥤ LaxMonoidalFunctor C D
  body: inducedFunctor _

中文:
定义 forget
  签名: : 松弛辫函子 C D ⥤ 松弛幺半群函子 C D
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def forget : LaxBraidedFunctor C D ⥤ LaxMonoidalFunctor C D :=
  inducedFunctor _

/--
Definition of `fullyFaithfulForget` / `fullyFaithfulForget` 的定义

English:
definition fullyFaithfulForget
  signature: : (forget (C := C) (D := D)).FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulForget
  签名: : (forget (C := C) (D := D)).满忠实
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: FullyFaithful
-/
def fullyFaithfulForget : (forget (C := C) (D := D)).FullyFaithful :=
  fullyFaithfulInducedFunctor _

section

variable {F G : LaxBraidedFunctor C D} (e : forall X, F.obj X ≅ G.obj X)
    (naturality : forall {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : forall X Y, μ F.toFunctor X Y ≫ (e (X otimes Y)).hom =
      ((e X).hom otimesₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `isoOfComponents` / `isoOfComponents` 的定义

English:
definition isoOfComponents
  signature: :
  body: fullyFaithfulForget.preimageIso
    (LaxMonoidalFunctor.isoOfComponents e naturality unit tensor)

中文:
定义 isoOfComponents
  签名: :
  定义体: fullyFaithfulForget.preimageIso
    (LaxMonoidalFunctor.isoOfComponents e naturality unit tensor)

Depends on / 依赖: LaxMonoidalFunctor, LaxMonoidalFunctor.isoOfComponents, Sheaf.toImage, fullyFaithfulForget, fullyFaithfulForget.preimageIso, infer_instance, isoOfComponents, naturality, preimageIso, tensor, toImage
-/
def isoOfComponents :
    F ≅ G :=
  fullyFaithfulForget.preimageIso
    (LaxMonoidalFunctor.isoOfComponents e naturality unit tensor)

set_option backward.privateInPublic true in
@[simp]
/--
lemma `isoOfComponents_hom_hom_hom_app` / 引理 `isoOfComponents_hom_hom_hom_app`

English:
lemma isoOfComponents_hom_hom_hom_app
  given: (X : C)
  proof: rfl

中文:
引理 isoOfComponents_hom_hom_hom_app
  条件: (X : C)
  证明: rfl
-/
lemma isoOfComponents_hom_hom_hom_app (X : C) :
    (isoOfComponents e naturality unit tensor).hom.hom.hom.app X = (e X).hom := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `isoOfComponents_inv_hom_hom_app` / 引理 `isoOfComponents_inv_hom_hom_app`

English:
lemma isoOfComponents_inv_hom_hom_app
  given: (X : C)
  proof: rfl

中文:
引理 isoOfComponents_inv_hom_hom_app
  条件: (X : C)
  证明: rfl
-/
lemma isoOfComponents_inv_hom_hom_app (X : C) :
    (isoOfComponents e naturality unit tensor).inv.hom.hom.app X = (e X).inv := rfl

end

end LaxBraidedFunctor

end

/-- A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
@[ext]
/--
Definition of `Functor.Braided` / `Functor.Braided` 的定义

English:
class Functor.Braided
  parameters: (F : C ⥤ D)
  extends: F.Monoidal, F.LaxBraided
  axioms and operations (1):
    - @[simp, : reassoc]

中文:
类 函子.辫
  参数: (F : C ⥤ D)
  继承: F.幺半群, F.松弛辫
  公理与运算 (1 个):
    - @[simp, : reassoc]
-/
class Functor.Braided (F : C ⥤ D) extends F.Monoidal, F.LaxBraided where

@[simp, reassoc]
/--
lemma `Functor.map_braiding` / 引理 `Functor.map_braiding`

English:
lemma Functor.map_braiding
  given: (F : C ⥤ D) (X Y : C) [F.Braided]
  proof: by
  rw [← Functor.Braided.braided]; rw [δ_μ_assoc]

中文:
引理 函子.map_braiding
  条件: (F : C ⥤ D) (X Y : C) [F.辫]
  证明: by
  rw [← Functor.Braided.braided]; rw [δ_μ_assoc]

Depends on / 依赖: Braided, Functor, Functor.Braided.braided, braided
-/
lemma Functor.map_braiding (F : C ⥤ D) (X Y : C) [F.Braided] :
    F.map (β_ X Y).hom =
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← Functor.Braided.braided]; rw [δ_μ_assoc]

/--
A braided category with a faithful braided functor to a symmetric category is itself symmetric.
-/
@[instance_reducible]
/--
Definition of `SymmetricCategory.ofFaithful` / `SymmetricCategory.ofFaithful` 的定义

English:
definition SymmetricCategory.ofFaithful
  signature: {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
  body: F.map_injective (by simp)

中文:
定义 对称范畴.ofFaithful
  签名: {C D : 类型} [范畴* C] [范畴* D] [幺半群范畴 C]
  定义体: F.map_injective (by simp)

Depends on / 依赖: F.map_injective, map_injective
-/
def SymmetricCategory.ofFaithful {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [SymmetricCategory D] (F : C ⥤ D) [F.Braided]
    [F.Faithful] : SymmetricCategory C where
  symmetry X Y := F.map_injective (by simp)

/-- Pull back a symmetric braiding along a fully faithful monoidal functor. -/
@[instance_reducible]
/--
Definition of `SymmetricCategory.ofFullyFaithful` / `SymmetricCategory.ofFullyFaithful` 的定义

English:
definition SymmetricCategory.ofFullyFaithful
  signature: {C D : Type*} [Category* C] [Category* D]
  body: let h : BraidedCategory C := BraidedCategory.ofFullyFaithful F
  let _ : F.Braided := {
    braided X Y := by
      simp +instances [h, BraidedCategory.ofFullyFaithful, BraidedCategory.ofFaithful] }
  .ofFaithful F

中文:
定义 对称范畴.ofFullyFaithful
  签名: {C D : 类型} [范畴* C] [范畴* D]
  定义体: let h : BraidedCategory C := BraidedCategory.ofFullyFaithful F
  let _ : F.Braided := {
    braided X Y := by
      simp +instances [h, BraidedCategory.ofFullyFaithful, BraidedCategory.ofFaithful] }
  .ofFaithful F

Depends on / 依赖: Braided, BraidedCategory, BraidedCategory.ofFaithful, BraidedCategory.ofFullyFaithful, F.Braided, braided, instances, ofFaithful, ofFullyFaithful
-/
noncomputable def SymmetricCategory.ofFullyFaithful {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [SymmetricCategory D] : SymmetricCategory C :=
  let h : BraidedCategory C := BraidedCategory.ofFullyFaithful F
  let _ : F.Braided := {
    braided X Y := by
      simp +instances [h, BraidedCategory.ofFullyFaithful, BraidedCategory.ofFaithful] }
  .ofFaithful F

namespace Functor.Braided

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟭 C).Braided

中文:
实例 :
  签名: (𝟭 C).辫
-/
instance : (𝟭 C).Braided where

instance (F : C ⥤ D) (G : D ⥤ E) [F.Braided] [G.Braided] : (F ⋙ G).Braided where

/--
lemma `toMonoidal_injective` / 引理 `toMonoidal_injective`

English:
lemma toMonoidal_injective
  given: (F : C ⥤ D)
  statement: Function.Injective
  proof: by rintro ⟨⟩ ⟨⟩ rfl; rfl

中文:
引理 toMonoidal_injective
  条件: (F : C ⥤ D)
  结论: 函数.单射
  证明: by rintro ⟨⟩ ⟨⟩ rfl; rfl
-/
lemma toMonoidal_injective (F : C ⥤ D) : Function.Injective
    (@Braided.toMonoidal _ _ _ _ _ _ _ _ _ : F.Braided -> F.Monoidal) := by rintro ⟨⟩ ⟨⟩ rfl; rfl

/-- Copy of a braided structure on a functor `F` with new `ε`, `μ`, `η` and `δ` fields equal to the
old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {F : C ⥤ D} (hF : F.Braided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  body: hF.toMonoidal.copy ε' μ' η' δ' hε hμ hη hδ
  braided X Y := hμ ▸ hF.braided X Y

中文:
定义 copy
  签名: {F : C ⥤ D} (hF : F.辫) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  定义体: hF.toMonoidal.copy ε' μ' η' δ' hε hμ hη hδ
  braided X Y := hμ ▸ hF.braided X Y

Depends on / 依赖: Braided, F.Braided, braided, cat_disch, hF.braided, hF.toMonoidal.copy, toMonoidal
-/
def copy {F : C ⥤ D} (hF : F.Braided) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (δ' : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y)
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch)
    (hη : η' = η F := by cat_disch) (hδ : δ' = δ F := by cat_disch) : F.Braided where
  __ := hF.toMonoidal.copy ε' μ' η' δ' hε hμ hη hδ
  braided X Y := hμ ▸ hF.braided X Y

end Functor.Braided

section CommMonoid

variable (M : Type u) [CommMonoid M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (Discrete M)
  body: Discrete.eqToIso (mul_comm X.as Y.as)

中文:
实例 :
  签名: 辫范畴 (离散 M)
  定义体: Discrete.eqToIso (mul_comm X.as Y.as)

Depends on / 依赖: Discrete, Discrete.eqToIso, X.as, Y.as, eqToIso, mul_comm
-/
instance : BraidedCategory (Discrete M) where
  braiding X Y := Discrete.eqToIso (mul_comm X.as Y.as)

variable {M} {N : Type u} [CommMonoid N]

/--
Instance `Discrete.monoidalFunctorBraided` / 实例 `Discrete.monoidalFunctorBraided`

English:
instance Discrete.monoidalFunctorBraided
  signature: (F : M ->* N)

中文:
实例 离散.monoidalFunctorBraided
  签名: (F : M ->* N)
-/
instance Discrete.monoidalFunctorBraided (F : M ->* N) :
    (Discrete.monoidalFunctor F).Braided where

end CommMonoid

namespace MonoidalCategory

section Tensor

/--
Definition of `tensorμ` / `tensorμ` 的定义

English:
definition tensorμ
  signature: (X₁ X₂ Y₁ Y₂ : C)
  body: (α_ X₁ X₂ (Y₁ otimes Y₂)).hom ≫
    (X₁ ◁ (α_ X₂ Y₁ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂) ≫
        (X₁ ◁ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ otimes Y₂)).inv

中文:
定义 tensorμ
  签名: (X₁ X₂ Y₁ Y₂ : C)
  定义体: (α_ X₁ X₂ (Y₁ otimes Y₂)).hom ≫
    (X₁ ◁ (α_ X₂ Y₁ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂) ≫
        (X₁ ◁ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ otimes Y₂)).inv

Depends on / 依赖: otimes
-/
def tensorμ (X₁ X₂ Y₁ Y₂ : C) : (X₁ otimes X₂) otimes Y₁ otimes Y₂ ⟶ (X₁ otimes Y₁) otimes X₂ otimes Y₂ :=
  (α_ X₁ X₂ (Y₁ otimes Y₂)).hom ≫
    (X₁ ◁ (α_ X₂ Y₁ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂) ≫
        (X₁ ◁ (α_ Y₁ X₂ Y₂).hom) ≫ (α_ X₁ Y₁ (X₂ otimes Y₂)).inv

/--
Definition of `tensorδ` / `tensorδ` 的定义

English:
definition tensorδ
  signature: (X₁ X₂ Y₁ Y₂ : C)
  body: (α_ X₁ Y₁ (X₂ otimes Y₂)).hom ≫
    (X₁ ◁ (α_ Y₁ X₂ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).inv ▷ Y₂) ≫
        (X₁ ◁ (α_ X₂ Y₁ Y₂).hom) ≫
          (α_ X₁ X₂ (Y₁ otimes Y₂)).inv

@[reassoc (attr := simp)]

中文:
定义 tensorδ
  签名: (X₁ X₂ Y₁ Y₂ : C)
  定义体: (α_ X₁ Y₁ (X₂ otimes Y₂)).hom ≫
    (X₁ ◁ (α_ Y₁ X₂ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).inv ▷ Y₂) ≫
        (X₁ ◁ (α_ X₂ Y₁ Y₂).hom) ≫
          (α_ X₁ X₂ (Y₁ otimes Y₂)).inv

@[reassoc (attr := simp)]

Depends on / 依赖: otimes
-/
def tensorδ (X₁ X₂ Y₁ Y₂ : C) : (X₁ otimes Y₁) otimes X₂ otimes Y₂ ⟶ (X₁ otimes X₂) otimes Y₁ otimes Y₂ :=
  (α_ X₁ Y₁ (X₂ otimes Y₂)).hom ≫
    (X₁ ◁ (α_ Y₁ X₂ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).inv ▷ Y₂) ≫
        (X₁ ◁ (α_ X₂ Y₁ Y₂).hom) ≫
          (α_ X₁ X₂ (Y₁ otimes Y₂)).inv

@[reassoc (attr := simp)]
/--
lemma `tensorμ_tensorδ` / 引理 `tensorμ_tensorδ`

English:
lemma tensorμ_tensorδ
  given: (X₁ X₂ Y₁ Y₂ : C)
  proof: by
  simp only [tensorμ, ← whiskerLeft_comp_assoc, tensorδ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc (attr := simp)]

中文:
引理 tensorμ_tensorδ
  条件: (X₁ X₂ Y₁ Y₂ : C)
  证明: by
  simp only [tensorμ, ← whiskerLeft_comp_assoc, tensorδ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, hom_inv_id, hom_inv_id_assoc, hom_inv_whiskerRight_assoc, id_comp, inv_hom_id, inv_hom_id_assoc, whiskerLeft_comp_assoc, whiskerLeft_id
-/
lemma tensorμ_tensorδ (X₁ X₂ Y₁ Y₂ : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ≫ tensorδ X₁ X₂ Y₁ Y₂ = 𝟙 _ := by
  simp only [tensorμ, ← whiskerLeft_comp_assoc, tensorδ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc (attr := simp)]
/--
lemma `tensorδ_tensorμ` / 引理 `tensorδ_tensorμ`

English:
lemma tensorδ_tensorμ
  given: (X₁ X₂ Y₁ Y₂ : C)
  proof: by
  simp only [tensorδ, ← whiskerLeft_comp_assoc, tensorμ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc]

中文:
引理 tensorδ_tensorμ
  条件: (X₁ X₂ Y₁ Y₂ : C)
  证明: by
  simp only [tensorδ, ← whiskerLeft_comp_assoc, tensorμ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, hom_inv_id, hom_inv_id_assoc, id_comp, inv_hom_id, inv_hom_id_assoc, inv_hom_whiskerRight_assoc, whiskerLeft_comp_assoc, whiskerLeft_id
-/
lemma tensorδ_tensorμ (X₁ X₂ Y₁ Y₂ : C) :
    tensorδ X₁ X₂ Y₁ Y₂ ≫ tensorμ X₁ X₂ Y₁ Y₂ = 𝟙 _ := by
  simp only [tensorδ, ← whiskerLeft_comp_assoc, tensorμ, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.hom_inv_id]

@[reassoc]
/--
theorem `tensorμ_natural` / 定理 `tensorμ_natural`

English:
theorem tensorμ_natural
  statement: {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
  proof: by
  dsimp only [tensorμ]
  simp_rw [← id_tensorHom, ← tensorHom_id]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [associator_inv_naturality]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 3 4 =>
    rw [tensorHom_comp_tensorHom]; rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [comp_id g₂]; rw [← id_comp g₂]; rw [braiding_naturality]; rw [← tensorHom_comp_tensorHom]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 4 5 =>
    rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [associator_naturality]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  simp only [assoc]

@[reassoc]

中文:
定理 tensorμ_natural
  结论: {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
  证明: by
  dsimp only [tensorμ]
  simp_rw [← id_tensorHom, ← tensorHom_id]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [associator_inv_naturality]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 3 4 =>
    rw [tensorHom_comp_tensorHom]; rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [comp_id g₂]; rw [← id_comp g₂]; rw [braiding_naturality]; rw [← tensorHom_comp_tensorHom]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 4 5 =>
    rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [associator_naturality]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  simp only [assoc]

@[reassoc]

Depends on / 依赖: associator_inv_naturality, associator_naturality, braiding_naturality, comp_id, id_comp, id_tensorHom, simp_rw, slice_lhs, tensorHom_comp_tensorHom, tensorHom_id
-/
theorem tensorμ_natural {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : U₁ ⟶ V₁)
    (g₂ : U₂ ⟶ V₂) :
    ((f₁ otimesₘ f₂) otimesₘ g₁ otimesₘ g₂) ≫ tensorμ Y₁ Y₂ V₁ V₂ =
      tensorμ X₁ X₂ U₁ U₂ ≫ ((f₁ otimesₘ g₁) otimesₘ f₂ otimesₘ g₂) := by
  dsimp only [tensorμ]
  simp_rw [← id_tensorHom, ← tensorHom_id]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [associator_inv_naturality]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 3 4 =>
    rw [tensorHom_comp_tensorHom]; rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [comp_id g₂]; rw [← id_comp g₂]; rw [braiding_naturality]; rw [← tensorHom_comp_tensorHom]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 4 5 =>
    rw [tensorHom_comp_tensorHom]; rw [comp_id f₁]; rw [← id_comp f₁]; rw [associator_naturality]; rw [← tensorHom_comp_tensorHom]
  slice_lhs 5 6 => rw [associator_inv_naturality]
  simp only [assoc]

@[reassoc]
/--
theorem `tensorμ_natural_left` / 定理 `tensorμ_natural_left`

English:
theorem tensorμ_natural_left
  given: {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C)
  proof: by
  convert! tensorμ_natural f₁ f₂ (𝟙 Z₁) (𝟙 Z₂) using 1 <;> simp

@[reassoc]

中文:
定理 tensorμ_natural_left
  条件: {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C)
  证明: by
  convert! tensorμ_natural f₁ f₂ (𝟙 Z₁) (𝟙 Z₂) using 1 <;> simp

@[reassoc]

Depends on / 依赖: convert
-/
theorem tensorμ_natural_left {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C) :
    (f₁ otimesₘ f₂) ▷ (Z₁ otimes Z₂) ≫ tensorμ Y₁ Y₂ Z₁ Z₂ =
      tensorμ X₁ X₂ Z₁ Z₂ ≫ (f₁ ▷ Z₁ otimesₘ f₂ ▷ Z₂) := by
  convert! tensorμ_natural f₁ f₂ (𝟙 Z₁) (𝟙 Z₂) using 1 <;> simp

@[reassoc]
/--
theorem `tensorμ_natural_right` / 定理 `tensorμ_natural_right`

English:
theorem tensorμ_natural_right
  given: (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  proof: by
  convert! tensorμ_natural (𝟙 Z₁) (𝟙 Z₂) f₁ f₂ using 1 <;> simp

@[reassoc]

中文:
定理 tensorμ_natural_right
  条件: (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  证明: by
  convert! tensorμ_natural (𝟙 Z₁) (𝟙 Z₂) f₁ f₂ using 1 <;> simp

@[reassoc]

Depends on / 依赖: convert
-/
theorem tensorμ_natural_right (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (Z₁ otimes Z₂) ◁ (f₁ otimesₘ f₂) ≫ tensorμ Z₁ Z₂ Y₁ Y₂ =
      tensorμ Z₁ Z₂ X₁ X₂ ≫ (Z₁ ◁ f₁ otimesₘ Z₂ ◁ f₂) := by
  convert! tensorμ_natural (𝟙 Z₁) (𝟙 Z₂) f₁ f₂ using 1 <;> simp

@[reassoc]
/--
theorem `tensor_left_unitality` / 定理 `tensor_left_unitality`

English:
theorem tensor_left_unitality
  given: (X₁ X₂ : C)
  proof: by
  dsimp only [tensorμ]
  have :
    ((fun_ (𝟙_ C)).inv ▷ (X₁ otimes X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ otimes X₂)).hom ≫ (𝟙_ C ◁ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙_ C ◁ (fun_ X₁).inv ▷ X₂ := by
    simp
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    leftUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]

中文:
定理 tensor_left_unitality
  条件: (X₁ X₂ : C)
  证明: by
  dsimp only [tensorμ]
  have :
    ((fun_ (𝟙_ C)).inv ▷ (X₁ otimes X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ otimes X₂)).hom ≫ (𝟙_ C ◁ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙_ C ◁ (fun_ X₁).inv ▷ X₂ := by
    simp
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    leftUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: comp_whiskerRight, fun_, leftUnitor_inv_braiding, otimes, slice_rhs, tensorHom_def, whiskerLeft_comp
-/
theorem tensor_left_unitality (X₁ X₂ : C) :
    (fun_ (X₁ otimes X₂)).hom =
      ((fun_ (𝟙_ C)).inv ▷ (X₁ otimes X₂)) ≫
        tensorμ (𝟙_ C) (𝟙_ C) X₁ X₂ ≫ ((fun_ X₁).hom otimesₘ (fun_ X₂).hom) := by
  dsimp only [tensorμ]
  have :
    ((fun_ (𝟙_ C)).inv ▷ (X₁ otimes X₂)) ≫
        (α_ (𝟙_ C) (𝟙_ C) (X₁ otimes X₂)).hom ≫ (𝟙_ C ◁ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙_ C ◁ (fun_ X₁).inv ▷ X₂ := by
    simp
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 1 2 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    leftUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]
/--
theorem `tensor_right_unitality` / 定理 `tensor_right_unitality`

English:
theorem tensor_right_unitality
  given: (X₁ X₂ : C)
  proof: by
  dsimp only [tensorμ]
  have :
    ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C otimes 𝟙_ C)).hom ≫ (X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (X₁ ◁ (ρ_ X₂).inv ▷ 𝟙_ C) := by
    monoidal
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    rightUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]

中文:
定理 tensor_right_unitality
  条件: (X₁ X₂ : C)
  证明: by
  dsimp only [tensorμ]
  have :
    ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C otimes 𝟙_ C)).hom ≫ (X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (X₁ ◁ (ρ_ X₂).inv ▷ 𝟙_ C) := by
    monoidal
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    rightUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: comp_whiskerRight, fun_, monoidal, otimes, rightUnitor_inv_braiding, slice_rhs, tensorHom_def, whiskerLeft_comp
-/
theorem tensor_right_unitality (X₁ X₂ : C) :
    (ρ_ (X₁ otimes X₂)).hom =
      ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).inv) ≫
        tensorμ X₁ X₂ (𝟙_ C) (𝟙_ C) ≫ ((ρ_ X₁).hom otimesₘ (ρ_ X₂).hom) := by
  dsimp only [tensorμ]
  have :
    ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).inv) ≫
        (α_ X₁ X₂ (𝟙_ C otimes 𝟙_ C)).hom ≫ (X₁ ◁ (α_ X₂ (𝟙_ C) (𝟙_ C)).inv) =
      (α_ X₁ X₂ (𝟙_ C)).hom ≫ (X₁ ◁ (ρ_ X₂).inv ▷ 𝟙_ C) := by
    monoidal
  slice_rhs 1 3 => rw [this]
  clear this
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ← comp_whiskerRight,
    rightUnitor_inv_braiding]
  simp [tensorHom_def]

@[reassoc]
/--
theorem `tensor_associativity` / 定理 `tensor_associativity`

English:
theorem tensor_associativity
  given: (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C)
  proof: by
  dsimp only [tensor_obj, prodMonoidal_tensorObj, tensorμ]
  simp only [braiding_tensor_left_hom, braiding_tensor_right_hom]
  calc
    _ = 𝟙 _ otimes≫
      X₁ ◁ ((β_ X₂ Y₁).hom ▷ (Y₂ otimes Z₁) ≫ (Y₁ otimes X₂) ◁ (β_ Y₂ Z₁).hom) ▷ Z₂ otimes≫
        X₁ ◁ Y₁ ◁ (β_ X₂ Z₁).hom ▷ Y₂ ▷ Z₂ otimes≫ 𝟙 _ := by monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

中文:
定理 tensor_associativity
  条件: (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C)
  证明: by
  dsimp only [tensor_obj, prodMonoidal_tensorObj, tensorμ]
  simp only [braiding_tensor_left_hom, braiding_tensor_right_hom]
  calc
    _ = 𝟙 _ otimes≫
      X₁ ◁ ((β_ X₂ Y₁).hom ▷ (Y₂ otimes Z₁) ≫ (Y₁ otimes X₂) ◁ (β_ Y₂ Z₁).hom) ▷ Z₂ otimes≫
        X₁ ◁ Y₁ ◁ (β_ X₂ Z₁).hom ▷ Y₂ ▷ Z₂ otimes≫ 𝟙 _ := by monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

Depends on / 依赖: braiding_tensor_left_hom, braiding_tensor_right_hom, monoidal, otimes, prodMonoidal_tensorObj, tensor_obj, whisker_exchange
-/
theorem tensor_associativity (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    (tensorμ X₁ X₂ Y₁ Y₂ ▷ (Z₁ otimes Z₂)) ≫
        tensorμ (X₁ otimes Y₁) (X₂ otimes Y₂) Z₁ Z₂ ≫ ((α_ X₁ Y₁ Z₁).hom otimesₘ (α_ X₂ Y₂ Z₂).hom) =
      (α_ (X₁ otimes X₂) (Y₁ otimes Y₂) (Z₁ otimes Z₂)).hom ≫
        ((X₁ otimes X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) ≫ tensorμ X₁ X₂ (Y₁ otimes Z₁) (Y₂ otimes Z₂) := by
  dsimp only [tensor_obj, prodMonoidal_tensorObj, tensorμ]
  simp only [braiding_tensor_left_hom, braiding_tensor_right_hom]
  calc
    _ = 𝟙 _ otimes≫
      X₁ ◁ ((β_ X₂ Y₁).hom ▷ (Y₂ otimes Z₁) ≫ (Y₁ otimes X₂) ◁ (β_ Y₂ Z₁).hom) ▷ Z₂ otimes≫
        X₁ ◁ Y₁ ◁ (β_ X₂ Z₁).hom ▷ Y₂ ▷ Z₂ otimes≫ 𝟙 _ := by monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

set_option backward.defeqAttrib.useBackward true in
/--
Instance `tensorMonoidal` / 实例 `tensorMonoidal`

English:
instance tensorMonoidal
  signature: : (tensor C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
      { εIso := (fun_ (𝟙_ C)).symm
        μIso := fun X Y =>
          { hom := tensorμ X.1 X.2 Y.1 Y.2
            inv := tensorδ X.1 X.2 Y.1 Y.2 }
        μIso_hom_natural_left := fun f Z => tensorμ_natural_left f.1 f.2 Z.1 Z.2
        μIso_hom_natural_right := fun Z f => tensorμ_natural_right Z.1 Z.2 f.1 f.2
        associativity := fun X Y Z => tensor_associativity X.1 X.2 Y.1 Y.2 Z.1 Z.2
        left_unitality := fun ⟨X₁, X₂⟩ => tensor_left_unitality X₁ X₂
        right_unitality := fun ⟨X₁, X₂⟩ => tensor_right_unitality X₁ X₂ }

中文:
实例 tensorMonoidal
  签名: : (tensor C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
      { εIso := (fun_ (𝟙_ C)).symm
        μIso := fun X Y =>
          { hom := tensorμ X.1 X.2 Y.1 Y.2
            inv := tensorδ X.1 X.2 Y.1 Y.2 }
        μIso_hom_natural_left := fun f Z => tensorμ_natural_left f.1 f.2 Z.1 Z.2
        μIso_hom_natural_right := fun Z f => tensorμ_natural_right Z.1 Z.2 f.1 f.2
        associativity := fun X Y Z => tensor_associativity X.1 X.2 Y.1 Y.2 Z.1 Z.2
        left_unitality := fun ⟨X₁, X₂⟩ => tensor_left_unitality X₁ X₂
        right_unitality := fun ⟨X₁, X₂⟩ => tensor_right_unitality X₁ X₂ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, associativity, fun_, left_unitality, right_unitality, tensor_associativity, tensor_left_unitality, tensor_right_unitality, toMonoidal
-/
instance tensorMonoidal : (tensor C).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := (fun_ (𝟙_ C)).symm
        μIso := fun X Y =>
          { hom := tensorμ X.1 X.2 Y.1 Y.2
            inv := tensorδ X.1 X.2 Y.1 Y.2 }
        μIso_hom_natural_left := fun f Z => tensorμ_natural_left f.1 f.2 Z.1 Z.2
        μIso_hom_natural_right := fun Z f => tensorμ_natural_right Z.1 Z.2 f.1 f.2
        associativity := fun X Y Z => tensor_associativity X.1 X.2 Y.1 Y.2 Z.1 Z.2
        left_unitality := fun ⟨X₁, X₂⟩ => tensor_left_unitality X₁ X₂
        right_unitality := fun ⟨X₁, X₂⟩ => tensor_right_unitality X₁ X₂ }

/--
lemma `tensor_ε` / 引理 `tensor_ε`

English:
lemma tensor_ε
  statement: ε (tensor C) = (fun_ (𝟙_ C)).inv
  proof: rfl

中文:
引理 tensor_ε
  结论: ε (tensor C) = (fun_ (𝟙_ C)).inv
  证明: rfl
-/
@[simp] lemma tensor_ε : ε (tensor C) = (fun_ (𝟙_ C)).inv := rfl
/--
lemma `tensor_η` / 引理 `tensor_η`

English:
lemma tensor_η
  statement: η (tensor C) = (fun_ (𝟙_ C)).hom
  proof: rfl

中文:
引理 tensor_η
  结论: η (tensor C) = (fun_ (𝟙_ C)).hom
  证明: rfl
-/
@[simp] lemma tensor_η : η (tensor C) = (fun_ (𝟙_ C)).hom := rfl
/--
lemma `tensor_μ` / 引理 `tensor_μ`

English:
lemma tensor_μ
  given: (X Y : C × C)
  statement: μ (tensor C) X Y = tensorμ X.1 X.2 Y.1 Y.2
  proof: rfl

中文:
引理 tensor_μ
  条件: (X Y : C × C)
  结论: μ (tensor C) X Y = tensorμ X.1 X.2 Y.1 Y.2
  证明: rfl
-/
@[simp] lemma tensor_μ (X Y : C × C) : μ (tensor C) X Y = tensorμ X.1 X.2 Y.1 Y.2 := rfl
/--
lemma `tensor_δ` / 引理 `tensor_δ`

English:
lemma tensor_δ
  given: (X Y : C × C)
  statement: δ (tensor C) X Y = tensorδ X.1 X.2 Y.1 Y.2
  proof: rfl

@[reassoc]

中文:
引理 tensor_δ
  条件: (X Y : C × C)
  结论: δ (tensor C) X Y = tensorδ X.1 X.2 Y.1 Y.2
  证明: rfl

@[reassoc]
-/
@[simp] lemma tensor_δ (X Y : C × C) : δ (tensor C) X Y = tensorδ X.1 X.2 Y.1 Y.2 := rfl

@[reassoc]
/--
theorem `leftUnitor_monoidal` / 定理 `leftUnitor_monoidal`

English:
theorem leftUnitor_monoidal
  given: (X₁ X₂ : C)
  proof: by
  dsimp only [tensorμ]
  have :
    (fun_ X₁).hom otimesₘ (fun_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C otimes X₂)).hom ≫
        (𝟙_ C ◁ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (fun_ ((X₁ otimes 𝟙_ C) otimes X₂)).hom ≫ ((ρ_ X₁).hom ▷ X₂) := by
    monoidal
  simp [this]

@[reassoc]

中文:
定理 leftUnitor_monoidal
  条件: (X₁ X₂ : C)
  证明: by
  dsimp only [tensorμ]
  have :
    (fun_ X₁).hom otimesₘ (fun_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C otimes X₂)).hom ≫
        (𝟙_ C ◁ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (fun_ ((X₁ otimes 𝟙_ C) otimes X₂)).hom ≫ ((ρ_ X₁).hom ▷ X₂) := by
    monoidal
  simp [this]

@[reassoc]

Depends on / 依赖: fun_, monoidal, otimes
-/
theorem leftUnitor_monoidal (X₁ X₂ : C) :
    (fun_ X₁).hom otimesₘ (fun_ X₂).hom =
      tensorμ (𝟙_ C) X₁ (𝟙_ C) X₂ ≫ ((fun_ (𝟙_ C)).hom ▷ (X₁ otimes X₂)) ≫ (fun_ (X₁ otimes X₂)).hom := by
  dsimp only [tensorμ]
  have :
    (fun_ X₁).hom otimesₘ (fun_ X₂).hom =
      (α_ (𝟙_ C) X₁ (𝟙_ C otimes X₂)).hom ≫
        (𝟙_ C ◁ (α_ X₁ (𝟙_ C) X₂).inv) ≫ (fun_ ((X₁ otimes 𝟙_ C) otimes X₂)).hom ≫ ((ρ_ X₁).hom ▷ X₂) := by
    monoidal
  simp [this]

@[reassoc]
/--
theorem `rightUnitor_monoidal` / 定理 `rightUnitor_monoidal`

English:
theorem rightUnitor_monoidal
  given: (X₁ X₂ : C)
  proof: by
  dsimp only [tensorμ]
  have :
    (ρ_ X₁).hom otimesₘ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ otimes 𝟙_ C)).hom ≫
        (X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (X₁ ◁ (ρ_ (𝟙_ C otimes X₂)).hom) ≫ (X₁ ◁ (fun_ X₂).hom) := by
    monoidal
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  monoidal

@[reassoc]

中文:
定理 rightUnitor_monoidal
  条件: (X₁ X₂ : C)
  证明: by
  dsimp only [tensorμ]
  have :
    (ρ_ X₁).hom otimesₘ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ otimes 𝟙_ C)).hom ≫
        (X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (X₁ ◁ (ρ_ (𝟙_ C otimes X₂)).hom) ≫ (X₁ ◁ (fun_ X₂).hom) := by
    monoidal
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  monoidal

@[reassoc]

Depends on / 依赖: braiding_rightUnitor, fun_, monoidal, otimes
-/
theorem rightUnitor_monoidal (X₁ X₂ : C) :
    (ρ_ X₁).hom otimesₘ (ρ_ X₂).hom =
      tensorμ X₁ (𝟙_ C) X₂ (𝟙_ C) ≫ ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).hom) ≫ (ρ_ (X₁ otimes X₂)).hom := by
  dsimp only [tensorμ]
  have :
    (ρ_ X₁).hom otimesₘ (ρ_ X₂).hom =
      (α_ X₁ (𝟙_ C) (X₂ otimes 𝟙_ C)).hom ≫
        (X₁ ◁ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫ (X₁ ◁ (ρ_ (𝟙_ C otimes X₂)).hom) ≫ (X₁ ◁ (fun_ X₂).hom) := by
    monoidal
  rw [this]; clear this
  rw [← braiding_rightUnitor]
  monoidal

@[reassoc]
/--
theorem `associator_monoidal` / 定理 `associator_monoidal`

English:
theorem associator_monoidal
  given: (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C)
  proof: by
  dsimp only [tensorμ]
  calc
    _ = 𝟙 _ otimes≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ otimes≫
      X₁ ◁ ((X₂ otimes Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ otimes X₃)) ▷ Y₃ otimes≫ 𝟙 _ := by
          rw [braiding_tensor_right_hom]; monoidal
    _ = _ := by rw [whisker_exchange, braiding_tensor_left_hom]; monoidal

@[reassoc]

中文:
定理 associator_monoidal
  条件: (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C)
  证明: by
  dsimp only [tensorμ]
  calc
    _ = 𝟙 _ otimes≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ otimes≫
      X₁ ◁ ((X₂ otimes Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ otimes X₃)) ▷ Y₃ otimes≫ 𝟙 _ := by
          rw [braiding_tensor_right_hom]; monoidal
    _ = _ := by rw [whisker_exchange, braiding_tensor_left_hom]; monoidal

@[reassoc]

Depends on / 依赖: braiding_tensor_left_hom, braiding_tensor_right_hom, monoidal, otimes, whisker_exchange
-/
theorem associator_monoidal (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensorμ (X₁ otimes X₂) X₃ (Y₁ otimes Y₂) Y₃ ≫
        (tensorμ X₁ X₂ Y₁ Y₂ ▷ (X₃ otimes Y₃)) ≫ (α_ (X₁ otimes Y₁) (X₂ otimes Y₂) (X₃ otimes Y₃)).hom =
      ((α_ X₁ X₂ X₃).hom otimesₘ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensorμ X₁ (X₂ otimes X₃) Y₁ (Y₂ otimes Y₃) ≫ ((X₁ otimes Y₁) ◁ tensorμ X₂ X₃ Y₂ Y₃) := by
  dsimp only [tensorμ]
  calc
    _ = 𝟙 _ otimes≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ otimes≫
      X₁ ◁ ((X₂ otimes Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ otimes X₃)) ▷ Y₃ otimes≫ 𝟙 _ := by
          rw [braiding_tensor_right_hom]; monoidal
    _ = _ := by rw [whisker_exchange, braiding_tensor_left_hom]; monoidal

@[reassoc]
/--
lemma `tensorμ_comp_μ_tensorHom_μ_comp_μ` / 引理 `tensorμ_comp_μ_tensorHom_μ_comp_μ`

English:
lemma tensorμ_comp_μ_tensorHom_μ_comp_μ
  given: (F : C ⥤ D) [F.LaxBraided] (W X Y Z : C)
  proof: by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_comp_μ]; rw [associator_inv_naturality_left_assoc]; rw [← pentagon_inv_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [Category.assoc]; rw [μ_whiskerRight_comp_μ]; rw [whiskerLeft_hom_inv_assoc]; rw [Iso.inv_hom_id_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [μ_natural_left_assoc]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [← MonoidalCategory.whiskerLeft_comp]; rw [← Functor.LaxBraided.braided]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [μ_natural_right]; rw [whiskerLeft_μ_comp_μ_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [pentagon_inv_assoc]; rw [μ_natural_left_assoc]; rw [μ_natural_left_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [μ_whiskerRight_comp_μ_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← tensorHom_def_assoc]
  simp only [← Functor.map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

中文:
引理 tensorμ_comp_μ_tensorHom_μ_comp_μ
  条件: (F : C ⥤ D) [F.松弛辫] (W X Y Z : C)
  证明: by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_comp_μ]; rw [associator_inv_naturality_left_assoc]; rw [← pentagon_inv_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [Category.assoc]; rw [μ_whiskerRight_comp_μ]; rw [whiskerLeft_hom_inv_assoc]; rw [Iso.inv_hom_id_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [μ_natural_left_assoc]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [← MonoidalCategory.whiskerLeft_comp]; rw [← Functor.LaxBraided.braided]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [μ_natural_right]; rw [whiskerLeft_μ_comp_μ_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [pentagon_inv_assoc]; rw [μ_natural_left_assoc]; rw [μ_natural_left_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [μ_whiskerRight_comp_μ_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← tensorHom_def_assoc]
  simp only [← Functor.map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, associator_inv_naturality_left_assoc, associator_inv_naturality_middle_assoc, comp_whiskerRight_assoc, inv_hom_id_assoc, pentagon_inv_assoc, tensorHom_def, whiskerLeft_hom_inv_assoc
-/
lemma tensorμ_comp_μ_tensorHom_μ_comp_μ (F : C ⥤ D) [F.LaxBraided] (W X Y Z : C) :
    tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) ≫
      (μ F W Y otimesₘ μ F X Z) ≫ μ F (W otimes Y) (X otimes Z) =
      (μ F W X otimesₘ μ F Y Z) ≫ μ F (W otimes X) (Y otimes Z) ≫ F.map (tensorμ W X Y Z) := by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_comp_μ]; rw [associator_inv_naturality_left_assoc]; rw [← pentagon_inv_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [Category.assoc]; rw [μ_whiskerRight_comp_μ]; rw [whiskerLeft_hom_inv_assoc]; rw [Iso.inv_hom_id_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [μ_natural_left_assoc]; rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [← MonoidalCategory.whiskerLeft_comp]; rw [← Functor.LaxBraided.braided]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [μ_natural_right]; rw [whiskerLeft_μ_comp_μ_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [pentagon_inv_assoc]; rw [μ_natural_left_assoc]; rw [μ_natural_left_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [μ_whiskerRight_comp_μ_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← tensorHom_def_assoc]
  simp only [← Functor.map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

end Tensor

end MonoidalCategory

@[reassoc]
/--
theorem `SymmetricCategory.tensorμ_braid_swap` / 定理 `SymmetricCategory.tensorμ_braid_swap`

English:
theorem SymmetricCategory.tensorμ_braid_swap
  proof: by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X, tensorHom_def]

中文:
定理 对称范畴.tensorμ_braid_swap
  证明: by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X, tensorHom_def]

Depends on / 依赖: SymmetricCategory, SymmetricCategory.braiding_swap_eq_inv_braiding, braiding_swap_eq_inv_braiding, tensorHom_def
-/
theorem SymmetricCategory.tensorμ_braid_swap
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    (X Y : C) :
    tensorμ X X Y Y ≫ (β_ (X otimes Y) (X otimes Y)).hom =
      ((β_ X X).hom otimesₘ (β_ Y Y).hom) ≫ tensorμ X X Y Y := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y X, tensorHom_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory Cᵒᵖ
  body: (β_ Y.unop X.unop).op
braiding_naturality_right X {_ _} f := Quiver.Hom.unop_inj by simp
braiding_naturality_left {_ _} f Z := Quiver.Hom.unop_inj by simp

中文:
实例 :
  签名: 辫范畴 Cᵒᵖ
  定义体: (β_ Y.unop X.unop).op
braiding_naturality_right X {_ _} f := Quiver.Hom.unop_inj by simp
braiding_naturality_left {_ _} f Z := Quiver.Hom.unop_inj by simp

Depends on / 依赖: X.unop, Y.unop
-/
instance : BraidedCategory Cᵒᵖ where
  braiding X Y := (β_ Y.unop X.unop).op
braiding_naturality_right X {_ _} f := Quiver.Hom.unop_inj by simp
braiding_naturality_left {_ _} f Z := Quiver.Hom.unop_inj by simp

section OppositeLemmas

open Opposite

/--
lemma `op_braiding` / 引理 `op_braiding`

English:
lemma op_braiding
  given: (X Y : C)
  statement: (β_ X Y).op = β_ (op Y) (op X)
  proof: rfl

中文:
引理 op_braiding
  条件: (X Y : C)
  结论: (β_ X Y).op = β_ (op Y) (op X)
  证明: rfl
-/
@[simp] lemma op_braiding (X Y : C) : (β_ X Y).op = β_ (op Y) (op X) := rfl
/--
lemma `unop_braiding` / 引理 `unop_braiding`

English:
lemma unop_braiding
  given: (X Y : Cᵒᵖ)
  statement: (β_ X Y).unop = β_ (unop Y) (unop X)
  proof: rfl

中文:
引理 unop_braiding
  条件: (X Y : Cᵒᵖ)
  结论: (β_ X Y).unop = β_ (unop Y) (unop X)
  证明: rfl
-/
@[simp] lemma unop_braiding (X Y : Cᵒᵖ) : (β_ X Y).unop = β_ (unop Y) (unop X) := rfl

/--
lemma `op_hom_braiding` / 引理 `op_hom_braiding`

English:
lemma op_hom_braiding
  given: (X Y : C)
  statement: (β_ X Y).hom.op = (β_ (op Y) (op X)).hom
  proof: rfl

中文:
引理 op_hom_braiding
  条件: (X Y : C)
  结论: (β_ X Y).hom.op = (β_ (op Y) (op X)).hom
  证明: rfl
-/
@[simp] lemma op_hom_braiding (X Y : C) : (β_ X Y).hom.op = (β_ (op Y) (op X)).hom := rfl
/--
lemma `unop_hom_braiding` / 引理 `unop_hom_braiding`

English:
lemma unop_hom_braiding
  given: (X Y : Cᵒᵖ)
  statement: (β_ X Y).hom.unop = (β_ (unop Y) (unop X)).hom
  proof: rfl

中文:
引理 unop_hom_braiding
  条件: (X Y : Cᵒᵖ)
  结论: (β_ X Y).hom.unop = (β_ (unop Y) (unop X)).hom
  证明: rfl
-/
@[simp] lemma unop_hom_braiding (X Y : Cᵒᵖ) : (β_ X Y).hom.unop = (β_ (unop Y) (unop X)).hom := rfl

/--
lemma `op_inv_braiding` / 引理 `op_inv_braiding`

English:
lemma op_inv_braiding
  given: (X Y : C)
  statement: (β_ X Y).inv.op = (β_ (op Y) (op X)).inv
  proof: rfl

中文:
引理 op_inv_braiding
  条件: (X Y : C)
  结论: (β_ X Y).inv.op = (β_ (op Y) (op X)).inv
  证明: rfl
-/
@[simp] lemma op_inv_braiding (X Y : C) : (β_ X Y).inv.op = (β_ (op Y) (op X)).inv := rfl
/--
lemma `unop_inv_braiding` / 引理 `unop_inv_braiding`

English:
lemma unop_inv_braiding
  given: (X Y : Cᵒᵖ)
  statement: (β_ X Y).inv.unop = (β_ (unop Y) (unop X)).inv
  proof: rfl

中文:
引理 unop_inv_braiding
  条件: (X Y : Cᵒᵖ)
  结论: (β_ X Y).inv.unop = (β_ (unop Y) (unop X)).inv
  证明: rfl
-/
@[simp] lemma unop_inv_braiding (X Y : Cᵒᵖ) : (β_ X Y).inv.unop = (β_ (unop Y) (unop X)).inv := rfl

end OppositeLemmas

namespace MonoidalOpposite

/--
Instance `instBraiding` / 实例 `instBraiding`

English:
instance instBraiding
  signature: : BraidedCategory Cᴹᵒᵖ where
  body: (β_ Y.unmop X.unmop).mop
braiding_naturality_right X {_ _} f := Quiver.Hom.unmop_inj by simp
braiding_naturality_left {_ _} f Z := Quiver.Hom.unmop_inj by simp

中文:
实例 instBraiding
  签名: : 辫范畴 Cᴹᵒᵖ where
  定义体: (β_ Y.unmop X.unmop).mop
braiding_naturality_right X {_ _} f := Quiver.Hom.unmop_inj by simp
braiding_naturality_left {_ _} f Z := Quiver.Hom.unmop_inj by simp

Depends on / 依赖: X.unmop, Y.unmop
-/
instance instBraiding : BraidedCategory Cᴹᵒᵖ where
  braiding X Y := (β_ Y.unmop X.unmop).mop
braiding_naturality_right X {_ _} f := Quiver.Hom.unmop_inj by simp
braiding_naturality_left {_ _} f Z := Quiver.Hom.unmop_inj by simp

section MonoidalOppositeLemmas

/--
lemma `mop_braiding` / 引理 `mop_braiding`

English:
lemma mop_braiding
  given: (X Y : C)
  statement: (β_ X Y).mop = β_ (mop Y) (mop X)
  proof: rfl

中文:
引理 mop_braiding
  条件: (X Y : C)
  结论: (β_ X Y).mop = β_ (mop Y) (mop X)
  证明: rfl
-/
@[simp] lemma mop_braiding (X Y : C) : (β_ X Y).mop = β_ (mop Y) (mop X) := rfl
/--
lemma `unmop_braiding` / 引理 `unmop_braiding`

English:
lemma unmop_braiding
  given: (X Y : Cᴹᵒᵖ)
  statement: (β_ X Y).unmop = β_ (unmop Y) (unmop X)
  proof: rfl

中文:
引理 unmop_braiding
  条件: (X Y : Cᴹᵒᵖ)
  结论: (β_ X Y).unmop = β_ (unmop Y) (unmop X)
  证明: rfl
-/
@[simp] lemma unmop_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).unmop = β_ (unmop Y) (unmop X) := rfl

/--
lemma `mop_hom_braiding` / 引理 `mop_hom_braiding`

English:
lemma mop_hom_braiding
  given: (X Y : C)
  statement: (β_ X Y).hom.mop = (β_ (mop Y) (mop X)).hom
  proof: rfl
@[simp]

中文:
引理 mop_hom_braiding
  条件: (X Y : C)
  结论: (β_ X Y).hom.mop = (β_ (mop Y) (mop X)).hom
  证明: rfl
@[simp]
-/
@[simp] lemma mop_hom_braiding (X Y : C) : (β_ X Y).hom.mop = (β_ (mop Y) (mop X)).hom := rfl
@[simp]
/--
lemma `unmop_hom_braiding` / 引理 `unmop_hom_braiding`

English:
lemma unmop_hom_braiding
  given: (X Y : Cᴹᵒᵖ)
  statement: (β_ X Y).hom.unmop = (β_ (unmop Y) (unmop X)).hom
  proof: rfl

中文:
引理 unmop_hom_braiding
  条件: (X Y : Cᴹᵒᵖ)
  结论: (β_ X Y).hom.unmop = (β_ (unmop Y) (unmop X)).hom
  证明: rfl
-/
lemma unmop_hom_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).hom.unmop = (β_ (unmop Y) (unmop X)).hom := rfl

/--
lemma `mop_inv_braiding` / 引理 `mop_inv_braiding`

English:
lemma mop_inv_braiding
  given: (X Y : C)
  statement: (β_ X Y).inv.mop = (β_ (mop Y) (mop X)).inv
  proof: rfl
@[simp]

中文:
引理 mop_inv_braiding
  条件: (X Y : C)
  结论: (β_ X Y).inv.mop = (β_ (mop Y) (mop X)).inv
  证明: rfl
@[simp]
-/
@[simp] lemma mop_inv_braiding (X Y : C) : (β_ X Y).inv.mop = (β_ (mop Y) (mop X)).inv := rfl
@[simp]
/--
lemma `unmop_inv_braiding` / 引理 `unmop_inv_braiding`

English:
lemma unmop_inv_braiding
  given: (X Y : Cᴹᵒᵖ)
  statement: (β_ X Y).inv.unmop = (β_ (unmop Y) (unmop X)).inv
  proof: rfl

中文:
引理 unmop_inv_braiding
  条件: (X Y : Cᴹᵒᵖ)
  结论: (β_ X Y).inv.unmop = (β_ (unmop Y) (unmop X)).inv
  证明: rfl
-/
lemma unmop_inv_braiding (X Y : Cᴹᵒᵖ) : (β_ X Y).inv.unmop = (β_ (unmop Y) (unmop X)).inv := rfl

end MonoidalOppositeLemmas

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (mopFunctor C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y => β_ (mop X) (mop Y)
      associativity := fun X Y Z => by simp [← yang_baxter_assoc] }

中文:
实例 :
  签名: (mopFunctor C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y => β_ (mop X) (mop Y)
      associativity := fun X Y Z => by simp [← yang_baxter_assoc] }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, associativity, toMonoidal, yang_baxter_assoc
-/
instance : (mopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y => β_ (mop X) (mop Y)
      associativity := fun X Y Z => by simp [← yang_baxter_assoc] }

/--
lemma `mopFunctor_ε` / 引理 `mopFunctor_ε`

English:
lemma mopFunctor_ε
  statement: ε (mopFunctor C) = 𝟙 _
  proof: rfl

中文:
引理 mopFunctor_ε
  结论: ε (mopFunctor C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma mopFunctor_ε : ε (mopFunctor C) = 𝟙 _ := rfl
/--
lemma `mopFunctor_η` / 引理 `mopFunctor_η`

English:
lemma mopFunctor_η
  statement: η (mopFunctor C) = 𝟙 _
  proof: rfl

中文:
引理 mopFunctor_η
  结论: η (mopFunctor C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma mopFunctor_η : η (mopFunctor C) = 𝟙 _ := rfl
/--
lemma `mopFunctor_μ` / 引理 `mopFunctor_μ`

English:
lemma mopFunctor_μ
  given: (X Y : C)
  statement: μ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).hom
  proof: rfl

中文:
引理 mopFunctor_μ
  条件: (X Y : C)
  结论: μ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).hom
  证明: rfl
-/
@[simp] lemma mopFunctor_μ (X Y : C) : μ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).hom := rfl
/--
lemma `mopFunctor_δ` / 引理 `mopFunctor_δ`

English:
lemma mopFunctor_δ
  given: (X Y : C)
  statement: δ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).inv
  proof: rfl

中文:
引理 mopFunctor_δ
  条件: (X Y : C)
  结论: δ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).inv
  证明: rfl
-/
@[simp] lemma mopFunctor_δ (X Y : C) : δ (mopFunctor C) X Y = (β_ (mop X) (mop Y)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unmopFunctor C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y => β_ (unmop X) (unmop Y)
      associativity := fun X Y Z => by simp [← yang_baxter_assoc] }

中文:
实例 :
  签名: (unmopFunctor C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y => β_ (unmop X) (unmop Y)
      associativity := fun X Y Z => by simp [← yang_baxter_assoc] }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, associativity, toMonoidal, yang_baxter_assoc
-/
instance : (unmopFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun X Y => β_ (unmop X) (unmop Y)
      associativity := fun X Y Z => by simp [← yang_baxter_assoc] }

/--
lemma `unmopFunctor_ε` / 引理 `unmopFunctor_ε`

English:
lemma unmopFunctor_ε
  statement: ε (unmopFunctor C) = 𝟙 _
  proof: rfl

中文:
引理 unmopFunctor_ε
  结论: ε (unmopFunctor C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma unmopFunctor_ε : ε (unmopFunctor C) = 𝟙 _ := rfl
/--
lemma `unmopFunctor_η` / 引理 `unmopFunctor_η`

English:
lemma unmopFunctor_η
  statement: η (unmopFunctor C) = 𝟙 _
  proof: rfl

中文:
引理 unmopFunctor_η
  结论: η (unmopFunctor C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma unmopFunctor_η : η (unmopFunctor C) = 𝟙 _ := rfl
/--
lemma `unmopFunctor_μ` / 引理 `unmopFunctor_μ`

English:
lemma unmopFunctor_μ
  given: (X Y : Cᴹᵒᵖ)
  proof: rfl

中文:
引理 unmopFunctor_μ
  条件: (X Y : Cᴹᵒᵖ)
  证明: rfl
-/
@[simp] lemma unmopFunctor_μ (X Y : Cᴹᵒᵖ) :
    μ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).hom := rfl
/--
lemma `unmopFunctor_δ` / 引理 `unmopFunctor_δ`

English:
lemma unmopFunctor_δ
  given: (X Y : Cᴹᵒᵖ)
  proof: rfl

中文:
引理 unmopFunctor_δ
  条件: (X Y : Cᴹᵒᵖ)
  证明: rfl
-/
@[simp] lemma unmopFunctor_δ (X Y : Cᴹᵒᵖ) :
    δ (unmopFunctor C) X Y = (β_ (unmop X) (unmop Y)).inv := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (mopFunctor C).Braided

中文:
实例 :
  签名: (mopFunctor C).辫
-/
instance : (mopFunctor C).Braided where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unmopFunctor C).Braided

中文:
实例 :
  签名: (unmopFunctor C).辫
-/
instance : (unmopFunctor C).Braided where

end MonoidalOpposite

variable (C)

/--
Definition of `reverseBraiding` / `reverseBraiding` 的定义

English:
abbreviation reverseBraiding
  signature: : BraidedCategory C where
  body: (β_ Y X).symm
  braiding_naturality_right X {_ _} f := by simp
  braiding_naturality_left {_ _} f Z := by simp

中文:
缩写 reverseBraiding
  签名: : 辫范畴 C where
  定义体: (β_ Y X).symm
  braiding_naturality_right X {_ _} f := by simp
  braiding_naturality_left {_ _} f Z := by simp
-/
abbrev reverseBraiding : BraidedCategory C where
  braiding X Y := (β_ Y X).symm
  braiding_naturality_right X {_ _} f := by simp
  braiding_naturality_left {_ _} f Z := by simp

/--
lemma `SymmetricCategory.reverseBraiding_eq` / 引理 `SymmetricCategory.reverseBraiding_eq`

English:
lemma SymmetricCategory.reverseBraiding_eq
  statement: (C : Type u₁) [Category.{v₁} C]
  proof: by
  dsimp only [reverseBraiding]
  congr
  funext X Y
  exact Iso.ext (braiding_swap_eq_inv_braiding Y X).symm

中文:
引理 对称范畴.reverseBraiding_eq
  结论: (C : 类型u₁) [范畴.{v₁} C]
  证明: by
  dsimp only [reverseBraiding]
  congr
  funext X Y
  exact Iso.ext (braiding_swap_eq_inv_braiding Y X).symm

Depends on / 依赖: Iso.ext, braiding_swap_eq_inv_braiding, reverseBraiding
-/
lemma SymmetricCategory.reverseBraiding_eq (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [i : SymmetricCategory C] :
    reverseBraiding C = i.toBraidedCategory := by
  dsimp only [reverseBraiding]
  congr
  funext X Y
  exact Iso.ext (braiding_swap_eq_inv_braiding Y X).symm

/-- The identity functor from `C` to `C`, where the codomain is given the
reversed braiding, upgraded to a braided functor. -/
@[instance_reducible]
/--
Definition of `SymmetricCategory.equivReverseBraiding` / `SymmetricCategory.equivReverseBraiding` 的定义

English:
definition SymmetricCategory.equivReverseBraiding
  signature: (C : Type u₁) [Category.{v₁} C]
  body: @Functor.Braided.mk C _ _ _ C _ _ (reverseBraiding C) (𝟭 C) _ by
    simp +instances [reverseBraiding, braiding_swap_eq_inv_braiding]

中文:
定义 对称范畴.equivReverseBraiding
  签名: (C : 类型u₁) [范畴.{v₁} C]
  定义体: @Functor.Braided.mk C _ _ _ C _ _ (reverseBraiding C) (𝟭 C) _ by
    simp +instances [reverseBraiding, braiding_swap_eq_inv_braiding]

Depends on / 依赖: Braided, Functor, Functor.Braided.mk, braiding_swap_eq_inv_braiding, instances, reverseBraiding
-/
def SymmetricCategory.equivReverseBraiding (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [SymmetricCategory C] :=
@Functor.Braided.mk C _ _ _ C _ _ (reverseBraiding C) (𝟭 C) _ by
    simp +instances [reverseBraiding, braiding_swap_eq_inv_braiding]

end CategoryTheory
