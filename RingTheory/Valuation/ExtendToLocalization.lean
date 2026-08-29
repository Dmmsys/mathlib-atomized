/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!

# Extending valuations to a localization

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.primeCompl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/

@[expose] public section


variable {A : Type*} [CommRing A] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation A Γ) {S : Submonoid A} (hS : S <= v.supp.primeCompl) (B : Type*) [CommRing B]
  [Algebra A B] [IsLocalization S B]

/--
Definition of `Valuation.extendToLocalization` / `Valuation.extendToLocalization` 的定义

English:
definition Valuation.extendToLocalization
  signature: : Valuation B Γ
  body: let f := IsLocalization.toLocalizationMap S B
  let h : forall s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert! f.lift_eq (P := Γ) _ 0 <;> simp [f]
    map_add_le_max' := fun x y => by
      obtain ⟨a, b, s, rfl, rfl⟩ : exists (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y := by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t
        constructor <;>
          · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]
            ring_nf
      convert_to! f.lift h (f.mk' (a + b) s) <= max (f.lift h _) (f.lift h _)
      · refine congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 ?_)
        rw [add_mul]; rw [map_add]
        rw [← IsLocalization.toLocalizationMap_apply S B]; rw [f.mk'_spec]; rw [f.mk'_spec]; rw [IsLocalization.toLocalizationMap_apply]; rw [IsLocalization.toLocalizationMap_apply]
      iterate 3 rw [f.lift_mk']
      dsimp
      grw [max_mul_mul_right, v.map_add a b] }

中文:
定义 赋值.extendToLocalization
  签名: : 赋值 B Γ
  定义体: let f := IsLocalization.toLocalizationMap S B
  let h : forall s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert! f.lift_eq (P := Γ) _ 0 <;> simp [f]
    map_add_le_max' := fun x y => by
      obtain ⟨a, b, s, rfl, rfl⟩ : exists (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y := by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t
        constructor <;>
          · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]
            ring_nf
      convert_to! f.lift h (f.mk' (a + b) s) <= max (f.lift h _) (f.lift h _)
      · refine congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 ?_)
        rw [add_mul]; rw [map_add]
        rw [← IsLocalization.toLocalizationMap_apply S B]; rw [f.mk'_spec]; rw [f.mk'_spec]; rw [IsLocalization.toLocalizationMap_apply]; rw [IsLocalization.toLocalizationMap_apply]
      iterate 3 rw [f.lift_mk']
      dsimp
      grw [max_mul_mul_right, v.map_add a b] }

Depends on / 依赖: IsLocalization, IsLocalization.toLocalizationMap, IsUnit, Submonoid, Submonoid.coe_mul, _eq_iff_eq, _surjective, coe_mul, convert, f.lift, f.lift_eq, f.mk, isUnit_iff_ne_zero, lift_eq, map_add_le_max, map_zero, toLocalizationMap, toMonoidHom
-/
noncomputable def Valuation.extendToLocalization : Valuation B Γ :=
  let f := IsLocalization.toLocalizationMap S B
  let h : forall s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert! f.lift_eq (P := Γ) _ 0 <;> simp [f]
    map_add_le_max' := fun x y => by
      obtain ⟨a, b, s, rfl, rfl⟩ : exists (a b : A) (s : S), f.mk' a s = x ∧ f.mk' b s = y := by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t
        constructor <;>
          · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]
            ring_nf
      convert_to! f.lift h (f.mk' (a + b) s) <= max (f.lift h _) (f.lift h _)
      · refine congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 ?_)
        rw [add_mul]; rw [map_add]
        rw [← IsLocalization.toLocalizationMap_apply S B]; rw [f.mk'_spec]; rw [f.mk'_spec]; rw [IsLocalization.toLocalizationMap_apply]; rw [IsLocalization.toLocalizationMap_apply]
      iterate 3 rw [f.lift_mk']
      dsimp
      grw [max_mul_mul_right, v.map_add a b] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Valuation.extendToLocalization_mk'` / 定理 `Valuation.extendToLocalization_mk'`

English:
theorem Valuation.extendToLocalization_mk'
  given: (x : A) (y : S)
  proof: (Submonoid.LocalizationMap.lift_mk' _ _ _ _).trans (by simp [IsUnit.coe_liftRight])

@[simp]

中文:
定理 赋值.extendToLocalization_mk'
  条件: (x : A) (y : S)
  证明: (Submonoid.LocalizationMap.lift_mk' _ _ _ _).trans (by simp [IsUnit.coe_liftRight])

@[simp]

Depends on / 依赖: IsUnit, IsUnit.coe_liftRight, LocalizationMap, Submonoid, Submonoid.LocalizationMap.lift_mk, coe_liftRight, lift_mk
-/
theorem Valuation.extendToLocalization_mk' (x : A) (y : S) :
    (v.extendToLocalization hS B) (IsLocalization.mk' _ x y) =
      v x * (v y)⁻¹ :=
  (Submonoid.LocalizationMap.lift_mk' _ _ _ _).trans (by simp [IsUnit.coe_liftRight])

@[simp]
/--
theorem `Valuation.extendToLocalization_apply_map_apply` / 定理 `Valuation.extendToLocalization_apply_map_apply`

English:
theorem Valuation.extendToLocalization_apply_map_apply
  given: (a : A)
  proof: Submonoid.LocalizationMap.lift_eq _ _ a

中文:
定理 赋值.extendToLocalization_apply_map_apply
  条件: (a : A)
  证明: Submonoid.LocalizationMap.lift_eq _ _ a

Depends on / 依赖: LocalizationMap, Submonoid, Submonoid.LocalizationMap.lift_eq, lift_eq
-/
theorem Valuation.extendToLocalization_apply_map_apply (a : A) :
    v.extendToLocalization hS B (algebraMap A B a) = v a :=
  Submonoid.LocalizationMap.lift_eq _ _ a
