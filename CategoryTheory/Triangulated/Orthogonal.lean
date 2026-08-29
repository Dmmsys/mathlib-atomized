/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Local

/-!
# Orthogonal of triangulated subcategories

Let `P` be a triangulated subcategory of a pretriangulated category `C`. We show
that `P.rightOrthogonal` (which consists of objects `Y` with no nonzero
map `X ⟶ Y` with `X` satisfying `P`) is a triangulated subcategory. The dual result
for `P.leftOrthogonal` is also obtained.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits Pretriangulated

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (P : ObjectProperty C)

section

variable {M : Type*} [AddGroup M] [HasShift C M] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: M] : P.rightOrthogonal.IsStableUnderShift M where
  body: ⟨fun Y hY X f hX => by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).surjective f
    simp [hY g (P.le_shift (-n) _ hX), Adjunction.homEquiv_unit]⟩

中文:
实例 [P.IsStableUnderShift
  签名: M] : P.rightOrthogonal.IsStableUnderShift M where
  定义体: ⟨fun Y hY X f hX => by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).surjective f
    simp [hY g (P.le_shift (-n) _ hX), Adjunction.homEquiv_unit]⟩

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, P.le_shift, homEquiv, homEquiv_unit, le_shift, shiftEquiv, surjective, symm.toAdjunction.homEquiv, toAdjunction
-/
instance [P.IsStableUnderShift M] : P.rightOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun Y hY X f hX => by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).surjective f
    simp [hY g (P.le_shift (-n) _ hX), Adjunction.homEquiv_unit]⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: M] : P.leftOrthogonal.IsStableUnderShift M where
  body: ⟨fun X hX Y f hY => by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv _ _).symm.surjective f
    simp [hX g (P.le_shift (-n) _ hY), Adjunction.homEquiv_counit]⟩

中文:
实例 [P.IsStableUnderShift
  签名: M] : P.leftOrthogonal.IsStableUnderShift M where
  定义体: ⟨fun X hX Y f hY => by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv _ _).symm.surjective f
    simp [hX g (P.le_shift (-n) _ hY), Adjunction.homEquiv_counit]⟩

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, P.le_shift, homEquiv, homEquiv_counit, le_shift, shiftEquiv, surjective, symm.surjective, toAdjunction, toAdjunction.homEquiv
-/
instance [P.IsStableUnderShift M] : P.leftOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun X hX Y f hY => by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv _ _).symm.surjective f
    simp [hX g (P.le_shift (-n) _ hY), Adjunction.homEquiv_counit]⟩

end

variable [HasZeroObject C] [HasShift C Int] [Preadditive C]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.rightOrthogonal.IsTriangulatedClosed₂
  body: .mk' (fun T hT h₁ h₃ X f hX => by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ _ hX)
    simp [h₁ g hX])

中文:
实例 :
  签名: P.rightOrthogonal.IsTriangulatedClosed₂
  定义体: .mk' (fun T hT h₁ h₃ X f hX => by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ _ hX)
    simp [h₁ g hX])

Depends on / 依赖: Pretriangulated, Pretriangulated.Triangle.coyoneda_exact, Triangle
-/
instance : P.rightOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ X f hX => by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ _ hX)
    simp [h₁ g hX])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.leftOrthogonal.IsTriangulatedClosed₂
  body: .mk' (fun T hT h₁ h₃ Y f hY => by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁ _ hY)
    simp [h₃ g hY])

中文:
实例 :
  签名: P.leftOrthogonal.IsTriangulatedClosed₂
  定义体: .mk' (fun T hT h₁ h₃ Y f hY => by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁ _ hY)
    simp [h₃ g hY])

Depends on / 依赖: Pretriangulated, Pretriangulated.Triangle.yoneda_exact, Triangle
-/
instance : P.leftOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ Y f hY => by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁ _ hY)
    simp [h₃ g hY])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: Int] : P.rightOrthogonal.IsTriangulated where

中文:
实例 [P.IsStableUnderShift
  签名: 整数] : P.rightOrthogonal.IsTriangulated where
-/
instance [P.IsStableUnderShift Int] : P.rightOrthogonal.IsTriangulated where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: Int] : P.leftOrthogonal.IsTriangulated where
  body: inferInstance

example [P.IsTriangulated] : P.leftOrthogonal.IsTriangulated := inferInstance

中文:
实例 [P.IsStableUnderShift
  签名: 整数] : P.leftOrthogonal.IsTriangulated where
  定义体: inferInstance

example [P.IsTriangulated] : P.leftOrthogonal.IsTriangulated := inferInstance
-/
instance [P.IsStableUnderShift Int] : P.leftOrthogonal.IsTriangulated where

example [P.IsTriangulated] : P.rightOrthogonal.IsTriangulated := inferInstance

example [P.IsTriangulated] : P.leftOrthogonal.IsTriangulated := inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocal_trW` / 引理 `isLocal_trW`

English:
lemma isLocal_trW
  given: [P.IsTriangulated]
  proof: by
  ext Y
  refine ⟨fun hY X f hX => ?_, fun hY X₁ X₂ f ⟨X₃, g, h, hT, hX₃⟩ => ⟨?_, fun α => ?_⟩⟩
  · exact (hY _ (trW.mk P (contractible_distinguished₁ X) hX)).injective (by simp)
  · suffices forall (α : X₂ ⟶ Y), f ≫ α = 0 -> α = 0 from fun α₁ α₂ hα => by
      simpa [sub_eq_zero] using this (α₁ 

中文:
引理 isLocal_trW
  条件: [P.IsTriangulated]
  证明: by
  ext Y
  refine ⟨fun hY X f hX => ?_, fun hY X₁ X₂ f ⟨X₃, g, h, hT, hX₃⟩ => ⟨?_, fun α => ?_⟩⟩
  · exact (hY _ (trW.mk P (contractible_distinguished₁ X) hX)).injective (by simp)
  · suffices forall (α : X₂ ⟶ Y), f ≫ α = 0 -> α = 0 from fun α₁ α₂ hα => by
      simpa [sub_eq_zero] using this (α₁ 

Depends on / 依赖: P.le_shift, Triangle, Triangle.yoneda_exact, injective, inv_rot_of_distTriang, le_shift, sub_eq_zero, trW.mk
-/
lemma isLocal_trW [P.IsTriangulated] :
    P.trW.isLocal = P.rightOrthogonal := by
  ext Y
  refine ⟨fun hY X f hX => ?_, fun hY X₁ X₂ f ⟨X₃, g, h, hT, hX₃⟩ => ⟨?_, fun α => ?_⟩⟩
  · exact (hY _ (trW.mk P (contractible_distinguished₁ X) hX)).injective (by simp)
  · suffices forall (α : X₂ ⟶ Y), f ≫ α = 0 -> α = 0 from fun α₁ α₂ hα => by
      simpa [sub_eq_zero] using this (α₁ - α₂) (by simpa [sub_eq_zero] using hα)
    intro α hα
    obtain ⟨β, rfl⟩ := Triangle.yoneda_exact₂ _ hT α hα
    simp [hY β hX₃]
  · obtain ⟨β, rfl⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT)
      α (hY _ (P.le_shift _ _ hX₃))
    exact ⟨β, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isColocal_trW` / 引理 `isColocal_trW`

English:
lemma isColocal_trW
  given: [P.IsTriangulated]
  proof: by
  ext X
  refine ⟨fun hX Y f hY => ?_, fun hX Y₂ Y₃ h hh => ?_⟩
  · exact (hX _ (trW.mk P (contractible_distinguished₂ Y) (P.le_shift _ _ hY))).injective (by simp)
  · rw [trW_iff'] at hh
    obtain ⟨Y₁, f, g, hT, hY₁⟩ := hh
    refine ⟨?_, fun α => ?_⟩
    · suffices forall (α : X ⟶ Y₂), α ≫ h =

中文:
引理 isColocal_trW
  条件: [P.IsTriangulated]
  证明: by
  ext X
  refine ⟨fun hX Y f hY => ?_, fun hX Y₂ Y₃ h hh => ?_⟩
  · exact (hX _ (trW.mk P (contractible_distinguished₂ Y) (P.le_shift _ _ hY))).injective (by simp)
  · rw [trW_iff'] at hh
    obtain ⟨Y₁, f, g, hT, hY₁⟩ := hh
    refine ⟨?_, fun α => ?_⟩
    · suffices forall (α : X ⟶ Y₂), α ≫ h =

Depends on / 依赖: P.le_shift, Triangle, Triangle.coyoned, Triangle.coyoneda_exact, coyoned, injective, le_shift, sub_eq_zero, trW.mk, trW_iff
-/
lemma isColocal_trW [P.IsTriangulated] :
    P.trW.isColocal = P.leftOrthogonal := by
  ext X
  refine ⟨fun hX Y f hY => ?_, fun hX Y₂ Y₃ h hh => ?_⟩
  · exact (hX _ (trW.mk P (contractible_distinguished₂ Y) (P.le_shift _ _ hY))).injective (by simp)
  · rw [trW_iff'] at hh
    obtain ⟨Y₁, f, g, hT, hY₁⟩ := hh
    refine ⟨?_, fun α => ?_⟩
    · suffices forall (α : X ⟶ Y₂), α ≫ h = 0 -> α = 0 from fun α₁ α₂ hα => by
        simpa [sub_eq_zero] using this (α₁ - α₂) (by simpa [sub_eq_zero])
      intro α hα
      obtain ⟨β, rfl⟩ := Triangle.coyoneda_exact₂ _ hT α hα
      simp [hX β hY₁]
    · obtain ⟨β, rfl⟩ := Triangle.coyoneda_exact₂ _ (rot_of_distTriang _ hT)
        α (hX _ (P.le_shift _ _ hY₁))
      exact ⟨β, rfl⟩

variable {P} in
/--
lemma `rightOrthogonal.map_bijective_of_isTriangulated` / 引理 `rightOrthogonal.map_bijective_of_isTriangulated`

English:
lemma rightOrthogonal.map_bijective_of_isTriangulated
  proof: by
  rw [← isLocal_trW] at hY
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_precomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hY _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.trW g
    obtain ⟨α, hα⟩ := (hY _ φ.hs).2 φ.f
    r

中文:
引理 rightOrthogonal.map_bijective_of_isTriangulated
  证明: by
  rw [← isLocal_trW] at hY
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_precomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hY _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.trW g
    obtain ⟨α, hα⟩ := (hY _ φ.hs).2 φ.f
    r

Depends on / 依赖: Functor, Functor.map_comp, L.map, Localization, Localization.exists_rightFraction, MorphismProperty, MorphismProperty.RightFraction.map_s_comp_map, MorphismProperty.map_eq_iff_precomp, P.trW, RightFraction, cancel_epi, exists_rightFraction, isLocal_trW, map_comp, map_eq_iff_precomp, map_s_comp_map
-/
lemma rightOrthogonal.map_bijective_of_isTriangulated
    [P.IsTriangulated] [IsTriangulated C] {Y : C} (hY : P.rightOrthogonal Y)
    (L : C ⥤ D) [L.IsLocalization P.trW] (X : C) :
    Function.Bijective (L.map : (X ⟶ Y) -> _) := by
  rw [← isLocal_trW] at hY
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_precomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hY _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.trW g
    obtain ⟨α, hα⟩ := (hY _ φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ]; rw [← cancel_epi (L.map φ.s)]; rw [MorphismProperty.RightFraction.map_s_comp_map]; rw [← hα]; rw [Functor.map_comp]

variable {P} in
/--
lemma `leftOrthogonal.map_bijective_of_isTriangulated` / 引理 `leftOrthogonal.map_bijective_of_isTriangulated`

English:
lemma leftOrthogonal.map_bijective_of_isTriangulated
  proof: by
  rw [← isColocal_trW] at hX
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_postcomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hX _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.trW g
    obtain ⟨α, hα⟩ := (hX _ φ.hs).2 φ.f
   

中文:
引理 leftOrthogonal.map_bijective_of_isTriangulated
  证明: by
  rw [← isColocal_trW] at hX
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_postcomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hX _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.trW g
    obtain ⟨α, hα⟩ := (hX _ φ.hs).2 φ.f
   

Depends on / 依赖: Functor, Functor.map_comp, L.map, LeftFraction, Localization, Localization.exists_leftFraction, MorphismProperty, MorphismProperty.LeftFraction.map_comp_map_s, MorphismProperty.map_eq_iff_postcomp, P.trW, cancel_mono, exists_leftFraction, isColocal_trW, map_comp, map_comp_map_s, map_eq_iff_postcomp
-/
lemma leftOrthogonal.map_bijective_of_isTriangulated
    [P.IsTriangulated] [IsTriangulated C] {X : C} (hX : P.leftOrthogonal X)
    (L : C ⥤ D) [L.IsLocalization P.trW] (Y : C) :
    Function.Bijective (L.map : (X ⟶ Y) -> _) := by
  rw [← isColocal_trW] at hX
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ?_⟩
  · rw [MorphismProperty.map_eq_iff_postcomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hX _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.trW g
    obtain ⟨α, hα⟩ := (hX _ φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ]; rw [← cancel_mono (L.map φ.s)]; rw [MorphismProperty.LeftFraction.map_comp_map_s]; rw [← hα]; rw [Functor.map_comp]

end ObjectProperty

end CategoryTheory
