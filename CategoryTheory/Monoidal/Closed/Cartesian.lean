/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian closed categories

A cartesian closed category is a category with `CartesianMonoidalCategory` and `MonoidalClosed`
instances. There used to be a separate definition `CartesianClosed`, with its own API, but over time
this ended up as a duplicate of the former. Now, `CartesianClosed` and the surrounding API has been
deprecated, and the API for `MonoidalClosed` should be used instead. This file now contains a few
basic constructions for cartesian closed categories.

-/

@[expose] public section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X X' Y Y' Z : C}

/--
Instance `CartesianMonoidalCategory.isLeftAdjoint_prod_functor` / 实例 `CartesianMonoidalCategory.isLeftAdjoint_prod_functor`

English:
instance CartesianMonoidalCategory.isLeftAdjoint_prod_functor
  body: Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A)

中文:
实例 CartesianMonoidal范畴.isLeftAdjoint_prod_functor
  定义体: Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A)

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.tensorLeftIsoProd, Functor, Functor.isLeftAdjoint_of_iso, isLeftAdjoint_of_iso, tensorLeftIsoProd
-/
instance CartesianMonoidalCategory.isLeftAdjoint_prod_functor
    (A : C) [Closed A] :
    (prod.functor.obj A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A)

namespace CartesianClosed

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms obtained using an exponentiable object. -/
scoped notation:20 A " ⟹ " B:19 => (ihom A).obj B

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Functor.obj` -/
@[app_delab Functor.obj]
meta def delabFunctorObjExp : Delab :=
whenPPOption getPPNotation withOverApp 6 do
  let e ← getExpr
guard e.isAppOfArity' ``Functor.obj 6
  let A ← withNaryArg 4 do
    let e ← getExpr
guard e.isAppOfArity' ``ihom 5
    withNaryArg 3 delab
  let B ← withNaryArg 5 delab
  `($A ⟹ $B)

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms from an exponentiable object. -/
scoped notation:30 B " ^^ " A:30 => (ihom A).obj B

end CartesianClosed

open CartesianClosed

/--
Definition of `internalizeHom` / `internalizeHom` 的定义

English:
definition internalizeHom
  signature: {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A Y : C} [Closed A]
  body: MonoidalClosed.curry (fst _ _ ≫ f)

中文:
定义 internalizeHom
  签名: {C : 类型u} [范畴.{v} C] [CartesianMonoidal范畴 C] {A Y : C} [闭 A]
  定义体: MonoidalClosed.curry (fst _ _ ≫ f)

Depends on / 依赖: MonoidalClosed, MonoidalClosed.curry
-/
def internalizeHom {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A Y : C} [Closed A]
    (f : A ⟶ Y) : 𝟙_ C ⟶ A ⟹ Y :=
  MonoidalClosed.curry (fst _ _ ≫ f)

variable {A B : C} [Closed A]

open MonoidalClosed

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
/--
Definition of `zeroMul` / `zeroMul` 的定义

English:
definition zeroMul
  signature: {I : C} (t : IsInitial I)
  body: snd _ _
  inv := t.to _
  hom_inv_id := by
    have : snd A I = uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this]; rw [← uncurry_natural_right]; rw [← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

中文:
定义 zeroMul
  签名: {I : C} (t : IsInitial I)
  定义体: snd _ _
  inv := t.to _
  hom_inv_id := by
    have : snd A I = uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this]; rw [← uncurry_natural_right]; rw [← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _
-/
def zeroMul {I : C} (t : IsInitial I) : A otimes I ≅ I where
  hom := snd _ _
  inv := t.to _
  hom_inv_id := by
    have : snd A I = uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this]; rw [← uncurry_natural_right]; rw [← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

/--
Definition of `mulZero` / `mulZero` 的定义

English:
definition mulZero
  signature: [BraidedCategory C] {I : C} (t : IsInitial I)
  body: β_ _ _ ≪≫ zeroMul t

中文:
定义 mulZero
  签名: [辫范畴 C] {I : C} (t : IsInitial I)
  定义体: β_ _ _ ≪≫ zeroMul t

Depends on / 依赖: zeroMul
-/
def mulZero [BraidedCategory C] {I : C} (t : IsInitial I) : I otimes A ≅ I :=
  β_ _ _ ≪≫ zeroMul t

/--
Definition of `powZero` / `powZero` 的定义

English:
definition powZero
  signature: [BraidedCategory C] {I : C} (t : IsInitial I) [MonoidalClosed C]
  body: default
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left]; rw [curry_eq_iff]; rw [← cancel_epi (mulZero t).inv]
    apply t.hom_ext

中文:
定义 powZero
  签名: [辫范畴 C] {I : C} (t : IsInitial I) [幺半群闭 C]
  定义体: default
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left]; rw [curry_eq_iff]; rw [← cancel_epi (mulZero t).inv]
    apply t.hom_ext
-/
def powZero [BraidedCategory C] {I : C} (t : IsInitial I) [MonoidalClosed C] : I ⟹ B ≅ 𝟙_ C where
  hom := default
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left]; rw [curry_eq_iff]; rw [← cancel_epi (mulZero t).inv]
    apply t.hom_ext

/--
theorem `strict_initial` / 定理 `strict_initial`

English:
theorem strict_initial
  given: {I : C} (t : IsInitial I) (f : A ⟶ I)
  statement: IsIso f
  proof: by
  have : Mono f := by
    rw [← lift_snd (𝟙 A) f]; rw [← zeroMul_hom t]
    exact mono_comp _ _
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

中文:
定理 strict_initial
  条件: {I : C} (t : IsInitial I) (f : A ⟶ I)
  结论: 是同构 f
  证明: by
  have : Mono f := by
    rw [← lift_snd (𝟙 A) f]; rw [← zeroMul_hom t]
    exact mono_comp _ _
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, hom_ext, isIso_of_mono_of_isSplitEpi, lift_snd, mono_comp, t.hom_ext, t.to, zeroMul_hom
-/
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  have : Mono f := by
    rw [← lift_snd (𝟙 A) f]; rw [← zeroMul_hom t]
    exact mono_comp _ _
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

/--
Instance `to_initial_isIso` / 实例 `to_initial_isIso`

English:
instance to_initial_isIso
  signature: [HasInitial C] (f : A ⟶ ⊥_ C)
  body: strict_initial initialIsInitial _

中文:
实例 to_initial_isIso
  签名: [HasInitial C] (f : A ⟶ ⊥_ C)
  定义体: strict_initial initialIsInitial _

Depends on / 依赖: initialIsInitial, strict_initial
-/
instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _

/--
theorem `initial_mono` / 定理 `initial_mono`

English:
theorem initial_mono
  given: {I : C} (B : C) (t : IsInitial I) [MonoidalClosed C]
  statement: Mono (t.to B)
  proof: ⟨fun g h _ => by
    have := strict_initial t g
    have := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

中文:
定理 initial_mono
  条件: {I : C} (B : C) (t : IsInitial I) [幺半群闭 C]
  结论: 单态射 (t.to B)
  证明: ⟨fun g h _ => by
    have := strict_initial t g
    have := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

Depends on / 依赖: eq_of_inv_eq_inv, hom_ext, strict_initial, t.hom_ext
-/
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [MonoidalClosed C] : Mono (t.to B) :=
  ⟨fun g h _ => by
    have := strict_initial t g
    have := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

/--
Instance `Initial.mono_to` / 实例 `Initial.mono_to`

English:
instance Initial.mono_to
  signature: [HasInitial C] (B : C) [MonoidalClosed C]
  body: initial_mono B initialIsInitial

中文:
实例 初始.mono_to
  签名: [HasInitial C] (B : C) [幺半群闭 C]
  定义体: initial_mono B initialIsInitial

Depends on / 依赖: initialIsInitial, initial_mono
-/
instance Initial.mono_to [HasInitial C] (B : C) [MonoidalClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial

variable {D : Type u₂} [Category.{v₂} D]

section Functor

variable [CartesianMonoidalCategory D]

/-- Transport the property of being Cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prodComparison` isomorphism.
-/
@[instance_reducible]
/--
Definition of `cartesianClosedOfEquiv` / `cartesianClosedOfEquiv` 的定义

English:
definition cartesianClosedOfEquiv
  signature: (e : C ≌ D) [MonoidalClosed C]
  body: letI : e.inverse.Monoidal := .ofChosenFiniteProducts _
  MonoidalClosed.ofEquiv e.inverse e.symm.toAdjunction

中文:
定义 cartesianClosedOfEquiv
  签名: (e : C ≌ D) [幺半群闭 C]
  定义体: letI : e.inverse.Monoidal := .ofChosenFiniteProducts _
  MonoidalClosed.ofEquiv e.inverse e.symm.toAdjunction

Depends on / 依赖: Monoidal, MonoidalClosed, MonoidalClosed.ofEquiv, e.inverse, e.inverse.Monoidal, e.symm.toAdjunction, inverse, ofChosenFiniteProducts, ofEquiv, toAdjunction
-/
noncomputable def cartesianClosedOfEquiv (e : C ≌ D) [MonoidalClosed C] : MonoidalClosed D :=
  letI : e.inverse.Monoidal := .ofChosenFiniteProducts _
  MonoidalClosed.ofEquiv e.inverse e.symm.toAdjunction

end Functor

end CategoryTheory
