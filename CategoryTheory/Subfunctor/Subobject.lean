/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Comparison between `Subfunctor`, `MonoOver` and `Subobject`

Given a type-valued functor `F : C ⥤ Type w`, we define an equivalence
of categories `Subfunctor.equivalenceMonoOver F : Subfunctor F ≌ MonoOver F`
and an order isomorphism `Subfunctor.orderIsoSubject F : Subfunctor F ≃o Subobject F`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

namespace Subfunctor

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `Subfunctor F ≌ MonoOver F`. -/
@[simps]
/--
Definition of `equivalenceMonoOver` / `equivalenceMonoOver` 的定义

English:
definition equivalenceMonoOver
  signature: : Subfunctor F ≌ MonoOver F where
  body: { obj A := MonoOver.mk A.ι
      map {A B} f := MonoOver.homMk (Subfunctor.homOfLe (leOfHom f)) }
  inverse :=
    { obj X := Subfunctor.range X.arrow
      map {X Y} f := homOfLE (by
        rw [← MonoOver.w f]
        apply range_comp_le) }
  unitIso := NatIso.ofComponents (fun A => eqToIso (by si

中文:
定义 equivalenceMonoOver
  签名: : Subfunctor F ≌ MonoOver F where
  定义体: { obj A := MonoOver.mk A.ι
      map {A B} f := MonoOver.homMk (Subfunctor.homOfLe (leOfHom f)) }
  inverse :=
    { obj X := Subfunctor.range X.arrow
      map {X Y} f := homOfLE (by
        rw [← MonoOver.w f]
        apply range_comp_le) }
  unitIso := NatIso.ofComponents (fun A => eqToIso (by si

Depends on / 依赖: MonoOver, MonoOver.homMk, MonoOver.isoMk, MonoOver.mk, MonoOver.w, NatIso, NatIso.ofComponents, Subfunctor, Subfunctor.homOfLe, Subfunctor.range, X.arrow, counitIso, eqToIso, homOfLE, homOfLe, inverse, leOfHom, ofComponents, range_comp_le, toRange
-/
noncomputable def equivalenceMonoOver : Subfunctor F ≌ MonoOver F where
  functor :=
    { obj A := MonoOver.mk A.ι
      map {A B} f := MonoOver.homMk (Subfunctor.homOfLe (leOfHom f)) }
  inverse :=
    { obj X := Subfunctor.range X.arrow
      map {X Y} f := homOfLE (by
        rw [← MonoOver.w f]
        apply range_comp_le) }
  unitIso := NatIso.ofComponents (fun A => eqToIso (by simp))
  counitIso := NatIso.ofComponents
    (fun X => MonoOver.isoMk ((asIso (toRange X.arrow)).symm))

variable {F} in
@[simp]
/--
lemma `range_subobjectMk_ι` / 引理 `range_subobjectMk_ι`

English:
lemma range_subobjectMk_ι
  given: (A : Subfunctor F)
  proof: (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).unitIso.app A).to_eq.symm

中文:
引理 range_subobjectMk_ι
  条件: (A : Subfunctor F)
  证明: (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).unitIso.app A).to_eq.symm

Depends on / 依赖: ThinSkeleton, ThinSkeleton.equivalence, equivalence, equivalenceMonoOver, to_eq, to_eq.symm, unitIso, unitIso.app
-/
lemma range_subobjectMk_ι (A : Subfunctor F) :
    range (Subobject.mk A.ι).arrow = A :=
  (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).unitIso.app A).to_eq.symm

variable {F} in
@[simp]
/--
lemma `subobjectMk_range_arrow` / 引理 `subobjectMk_range_arrow`

English:
lemma subobjectMk_range_arrow
  given: (X : Subobject F)
  proof: (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).counitIso.app X).to_eq

中文:
引理 subobjectMk_range_arrow
  条件: (X : Subobject F)
  证明: (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).counitIso.app X).to_eq

Depends on / 依赖: ThinSkeleton, ThinSkeleton.equivalence, counitIso, counitIso.app, equivalence, equivalenceMonoOver, to_eq
-/
lemma subobjectMk_range_arrow (X : Subobject F) :
    Subobject.mk (range X.arrow).ι = X :=
  (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).counitIso.app X).to_eq

/-- The order isomorphism `Subfunctor F ≃o MonoOver F`. -/
@[simps]
/--
Definition of `orderIsoSubobject` / `orderIsoSubobject` 的定义

English:
definition orderIsoSubobject
  signature: : Subfunctor F ≃o Subobject F where
  body: Subobject.mk A.ι
  invFun X := Subfunctor.range X.arrow
  left_inv A := by simp
  right_inv X := by simp
  map_rel_iff' {A B} := by
    constructor
    · intro h
      have : range (Subobject.mk A.ι).arrow <= range (Subobject.mk B.ι).arrow :=
        leOfHom (((equivalenceMonoOver F).trans
         

中文:
定义 orderIsoSubobject
  签名: : Subfunctor F ≃o Subobject F where
  定义体: Subobject.mk A.ι
  invFun X := Subfunctor.range X.arrow
  left_inv A := by simp
  right_inv X := by simp
  map_rel_iff' {A B} := by
    constructor
    · intro h
      have : range (Subobject.mk A.ι).arrow <= range (Subobject.mk B.ι).arrow :=
        leOfHom (((equivalenceMonoOver F).trans
         

Depends on / 依赖: Subobject, Subobject.mk
-/
noncomputable def orderIsoSubobject : Subfunctor F ≃o Subobject F where
  toFun A := Subobject.mk A.ι
  invFun X := Subfunctor.range X.arrow
  left_inv A := by simp
  right_inv X := by simp
  map_rel_iff' {A B} := by
    constructor
    · intro h
      have : range (Subobject.mk A.ι).arrow <= range (Subobject.mk B.ι).arrow :=
        leOfHom (((equivalenceMonoOver F).trans
          (ThinSkeleton.equivalence _).symm).inverse.map (homOfLE h))
      simpa using this
    · intro h
      exact leOfHom (((equivalenceMonoOver F).trans
        (ThinSkeleton.equivalence _).symm).functor.map (homOfLE h))

end Subfunctor

end CategoryTheory
