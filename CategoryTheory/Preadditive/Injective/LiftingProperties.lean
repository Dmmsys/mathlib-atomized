/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Characterization of injective objects in terms of lifting properties

An object `I` is injective iff the morphism `I ⟶ 0` has the
right lifting property with respect to monomorphisms,
`injective_iff_rlp_monomorphisms_zero`.

-/

public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace Injective

/--
lemma `hasLiftingProperty_of_isZero` / 引理 `hasLiftingProperty_of_isZero`

English:
lemma hasLiftingProperty_of_isZero
  proof: ⟨⟨{
    l := Injective.factorThru f i
    fac_right := hZ.eq_of_tgt _ _ }⟩⟩

中文:
引理 hasLiftingProperty_of_isZero
  证明: ⟨⟨{
    l := Injective.factorThru f i
    fac_right := hZ.eq_of_tgt _ _ }⟩⟩
-/
lemma hasLiftingProperty_of_isZero
    {A B I Z : C} (i : A ⟶ B) [Mono i] [Injective I] (p : I ⟶ Z) (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Injective.factorThru f i
    fac_right := hZ.eq_of_tgt _ _ }⟩⟩

instance {A B I : C} (i : A ⟶ B) [Mono i] [Injective I] [HasZeroObject C] (p : I ⟶ 0) :
    HasLiftingProperty i (p : I ⟶ 0) :=
  Injective.hasLiftingProperty_of_isZero i p (isZero_zero C)

end Injective

/--
lemma `injective_iff_rlp_monomorphisms_of_isZero` / 引理 `injective_iff_rlp_monomorphisms_of_isZero`

English:
lemma injective_iff_rlp_monomorphisms_of_isZero
  proof: by
  obtain rfl := hZ.eq_of_tgt p 0
  constructor
  · intro _ A B i (_ : Mono i)
    exact Injective.hasLiftingProperty_of_isZero i 0 hZ
  · intro h
    constructor
    intro A B f i hi
    have := h _ hi
    have sq : CommSq f i (0 : I ⟶ Z) 0 := ⟨by simp⟩
    exact ⟨sq.lift, by simp⟩

中文:
引理 injective_iff_rlp_monomorphisms_of_isZero
  证明: by
  obtain rfl := hZ.eq_of_tgt p 0
  constructor
  · intro _ A B i (_ : Mono i)
    exact Injective.hasLiftingProperty_of_isZero i 0 hZ
  · intro h
    constructor
    intro A B f i hi
    have := h _ hi
    have sq : CommSq f i (0 : I ⟶ Z) 0 := ⟨by simp⟩
    exact ⟨sq.lift, by simp⟩

Depends on / 依赖: CommSq, Injective, Injective.hasLiftingProperty_of_isZero, eq_of_tgt, hZ.eq_of_tgt, hasLiftingProperty_of_isZero, sq.lift
-/
lemma injective_iff_rlp_monomorphisms_of_isZero
    [HasZeroMorphisms C] {I Z : C} (p : I ⟶ Z) (hZ : IsZero Z) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp p := by
  obtain rfl := hZ.eq_of_tgt p 0
  constructor
  · intro _ A B i (_ : Mono i)
    exact Injective.hasLiftingProperty_of_isZero i 0 hZ
  · intro h
    constructor
    intro A B f i hi
    have := h _ hi
    have sq : CommSq f i (0 : I ⟶ Z) 0 := ⟨by simp⟩
    exact ⟨sq.lift, by simp⟩

/--
lemma `injective_iff_rlp_monomorphisms_zero` / 引理 `injective_iff_rlp_monomorphisms_zero`

English:
lemma injective_iff_rlp_monomorphisms_zero
  proof: injective_iff_rlp_monomorphisms_of_isZero _ (isZero_zero C)

中文:
引理 injective_iff_rlp_monomorphisms_zero
  证明: injective_iff_rlp_monomorphisms_of_isZero _ (isZero_zero C)

Depends on / 依赖: injective_iff_rlp_monomorphisms_of_isZero, isZero_zero
-/
lemma injective_iff_rlp_monomorphisms_zero
    [HasZeroMorphisms C] [HasZeroObject C] (I : C) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
  injective_iff_rlp_monomorphisms_of_isZero _ (isZero_zero C)

end CategoryTheory
