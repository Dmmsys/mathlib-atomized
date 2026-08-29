/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Skeletal

/-!
# The monoid on the skeleton of a monoidal category

The skeleton of a monoidal category is a monoid.

## Main results

* `Skeleton.instMonoid`, for monoidal categories.
* `Skeleton.instCommMonoid`, for braided monoidal categories.

-/

@[expose] public section


namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/--
Definition of `monoidOfSkeletalMonoidal` / `monoidOfSkeletalMonoidal` 的定义

English:
abbreviation monoidOfSkeletalMonoidal
  signature: (hC : Skeletal C)
  body: X otimes Y
  one := 𝟙_ C
  one_mul X := hC ⟨fun_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

中文:
缩写 monoidOfSkeletalMonoidal
  签名: (hC : Skeletal C)
  定义体: X otimes Y
  one := 𝟙_ C
  one_mul X := hC ⟨fun_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

Depends on / 依赖: otimes
-/
abbrev monoidOfSkeletalMonoidal (hC : Skeletal C) : Monoid C where
  mul X Y := X otimes Y
  one := 𝟙_ C
  one_mul X := hC ⟨fun_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

/--
Definition of `commMonoidOfSkeletalBraided` / `commMonoidOfSkeletalBraided` 的定义

English:
abbreviation commMonoidOfSkeletalBraided
  signature: [BraidedCategory C] (hC : Skeletal C)
  body: { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

中文:
缩写 commMonoidOfSkeletalBraided
  签名: [辫范畴 C] (hC : Skeletal C)
  定义体: { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

Depends on / 依赖: monoidOfSkeletalMonoidal, mul_comm
-/
abbrev commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMonoid C :=
  { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

namespace Skeleton

/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (Skeleton C)
  body: Monoidal.transport (skeletonEquivalence C).symm

中文:
实例 instMonoidalCategory
  签名: : 幺半群范畴 (Skeleton C)
  定义体: Monoidal.transport (skeletonEquivalence C).symm

Depends on / 依赖: Monoidal, Monoidal.transport, skeletonEquivalence, transport
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (Skeleton C) :=
  Monoidal.transport (skeletonEquivalence C).symm

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (Skeleton C)
  body: monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel

中文:
实例 instMonoid
  签名: : 幺半群 (Skeleton C)
  定义体: monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel

Depends on / 依赖: monoidOfSkeletalMonoidal, skeleton_isSkeleton
-/
noncomputable instance instMonoid : Monoid (Skeleton C) :=
  monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel

/--
theorem `mul_eq` / 定理 `mul_eq`

English:
theorem mul_eq
  given: (X Y : Skeleton C)
  statement: X * Y = toSkeleton (X.out otimes Y.out)
  proof: rfl

中文:
定理 mul_eq
  条件: (X Y : Skeleton C)
  结论: X * Y = toSkeleton (X.out otimes Y.out)
  证明: rfl
-/
theorem mul_eq (X Y : Skeleton C) : X * Y = toSkeleton (X.out otimes Y.out) := rfl
/--
theorem `one_eq` / 定理 `one_eq`

English:
theorem one_eq
  statement: (1 : Skeleton C) = toSkeleton (𝟙_ C)
  proof: rfl

中文:
定理 one_eq
  结论: (1 : Skeleton C) = toSkeleton (𝟙_ C)
  证明: rfl
-/
theorem one_eq : (1 : Skeleton C) = toSkeleton (𝟙_ C) := rfl

/--
theorem `toSkeleton_tensorObj` / 定理 `toSkeleton_tensorObj`

English:
theorem toSkeleton_tensorObj
  given: (X Y : C)
  statement: toSkeleton (X otimes Y) = toSkeleton X * toSkeleton Y
  proof: let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X otimesᵢ φ Y⟩

中文:
定理 toSkeleton_tensorObj
  条件: (X Y : C)
  结论: toSkeleton (X otimes Y) = toSkeleton X * toSkeleton Y
  证明: let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X otimesᵢ φ Y⟩

Depends on / 依赖: Quotient, Quotient.sound, skeletonEquivalence, symm.unitIso.app, unitIso
-/
theorem toSkeleton_tensorObj (X Y : C) : toSkeleton (X otimes Y) = toSkeleton X * toSkeleton Y :=
  let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X otimesᵢ φ Y⟩

/--
Instance `instBraidedCategory` / 实例 `instBraidedCategory`

English:
instance instBraidedCategory
  signature: [BraidedCategory C]
  body: (BraidedCategory.ofFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse :)

中文:
实例 instBraidedCategory
  签名: [辫范畴 C]
  定义体: (BraidedCategory.ofFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse :)

Depends on / 依赖: BraidedCategory, BraidedCategory.ofFullyFaithful, Monoidal, Monoidal.equivalenceTransported, equivalenceTransported, inverse, ofFullyFaithful, skeletonEquivalence
-/
noncomputable instance instBraidedCategory [BraidedCategory C] : BraidedCategory (Skeleton C) :=
  (BraidedCategory.ofFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse :)

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [BraidedCategory C]
  body: commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

中文:
实例 instCommMonoid
  签名: [辫范畴 C]
  定义体: commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

Depends on / 依赖: commMonoidOfSkeletalBraided, skeleton_isSkeleton
-/
noncomputable instance instCommMonoid [BraidedCategory C] : CommMonoid (Skeleton C) :=
  commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

end Skeleton

open CategoryTheory.Functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (skeletonEquivalence C).functor.Monoidal
  body: inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse.Monoidal

中文:
实例 :
  签名: (skeletonEquivalence C).functor.幺半群
  定义体: inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse.Monoidal

Depends on / 依赖: Monoidal, Monoidal.equivalenceTransported, equivalenceTransported, inverse, inverse.Monoidal, skeletonEquivalence
-/
noncomputable instance : (skeletonEquivalence C).functor.Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse.Monoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (skeletonEquivalence C).inverse.Monoidal
  body: inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).functor.Monoidal

中文:
实例 :
  签名: (skeletonEquivalence C).inverse.幺半群
  定义体: inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).functor.Monoidal

Depends on / 依赖: Monoidal, Monoidal.equivalenceTransported, equivalenceTransported, functor, functor.Monoidal, skeletonEquivalence
-/
noncomputable instance : (skeletonEquivalence C).inverse.Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).functor.Monoidal

variable {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D) (e : C ≌ D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.LaxMonoidal]
  signature: : F.mapSkeleton.LaxMonoidal
  body: .comp ..

中文:
实例 [F.松弛幺半群]
  签名: : F.mapSkeleton.松弛幺半群
  定义体: .comp ..
-/
noncomputable instance [F.LaxMonoidal] : F.mapSkeleton.LaxMonoidal := .comp ..
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.OplaxMonoidal]
  signature: : F.mapSkeleton.OplaxMonoidal
  body: .comp ..

中文:
实例 [F.反松弛幺半群]
  签名: : F.mapSkeleton.反松弛幺半群
  定义体: .comp ..
-/
noncomputable instance [F.OplaxMonoidal] : F.mapSkeleton.OplaxMonoidal := .comp ..
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Monoidal]
  signature: : F.mapSkeleton.Monoidal
  body: .instComp ..

中文:
实例 [F.幺半群]
  签名: : F.mapSkeleton.幺半群
  定义体: .instComp ..

Depends on / 依赖: instComp
-/
noncomputable instance [F.Monoidal] : F.mapSkeleton.Monoidal := .instComp ..

/--
Definition of `Skeletal.monoidHom` / `Skeletal.monoidHom` 的定义

English:
definition Skeletal.monoidHom
  signature: [F.Monoidal] (hC : Skeletal C) (hD : Skeletal D)
  body: monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ->* D := by
  intros; exact
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

中文:
定义 Skeletal.monoidHom
  签名: [F.幺半群] (hC : Skeletal C) (hD : Skeletal D)
  定义体: monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ->* D := by
  intros; exact
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

Depends on / 依赖: monoidOfSkeletalMonoidal
-/
def Skeletal.monoidHom [F.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ->* D := by
  intros; exact
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

/--
Definition of `Skeleton.monoidHom` / `Skeleton.monoidHom` 的定义

English:
definition Skeleton.monoidHom
  signature: [F.Monoidal]
  body: (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

中文:
定义 Skeleton.monoidHom
  签名: [F.幺半群]
  定义体: (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

Depends on / 依赖: F.mapSkeleton, mapSkeleton, monoidHom, skeleton_skeletal
-/
noncomputable def Skeleton.monoidHom [F.Monoidal] : Skeleton C ->* Skeleton D :=
  (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

/--
Definition of `Skeletal.mulEquiv` / `Skeletal.mulEquiv` 的定义

English:
definition Skeletal.mulEquiv
  signature: [e.functor.Monoidal] (hC : Skeletal C) (hD : Skeletal D)
  body: monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D := by
  intros; exact
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

中文:
定义 Skeletal.mulEquiv
  签名: [e.functor.幺半群] (hC : Skeletal C) (hD : Skeletal D)
  定义体: monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D := by
  intros; exact
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

Depends on / 依赖: monoidOfSkeletalMonoidal
-/
def Skeletal.mulEquiv [e.functor.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D := by
  intros; exact
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

/--
Definition of `Skeleton.mulEquiv` / `Skeleton.mulEquiv` 的定义

English:
definition Skeleton.mulEquiv
  signature: [e.functor.Monoidal]
  body: (skeleton_skeletal C).mulEquiv
    (((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm) (skeleton_skeletal D)

中文:
定义 Skeleton.mulEquiv
  签名: [e.functor.幺半群]
  定义体: (skeleton_skeletal C).mulEquiv
    (((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm) (skeleton_skeletal D)

Depends on / 依赖: mulEquiv, skeletonEquivalence, skeleton_skeletal
-/
noncomputable def Skeleton.mulEquiv [e.functor.Monoidal] : Skeleton C ≃* Skeleton D :=
  (skeleton_skeletal C).mulEquiv
    (((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm) (skeleton_skeletal D)

end CategoryTheory
