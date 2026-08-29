/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Attila Gáspár
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Topology.Algebra.Group.Torsor

/-!
# Topological properties of affine spaces and maps

This file contains a few facts regarding the continuity of affine maps.
-/

public section


namespace AffineMap

variable
  {R V P W Q : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

section Ring

variable [Ring R] [Module R V] [Module R W]

/--
theorem `continuous_linear_iff` / 定理 `continuous_linear_iff`

English:
theorem continuous_linear_iff
  given: {f : P ->ᵃ[R] Q}
  statement: Continuous f.linear ↔ Continuous f
  proof: by
  inhabit P
  have :
    (f.linear : V -> W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

中文:
定理 continuous_linear_iff
  条件: {f : P ->ᵃ[R] Q}
  结论: Continuous f.linear ↔ Continuous f
  证明: by
  inhabit P
  have :
    (f.linear : V -> W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

Depends on / 依赖: Homeomorph, Homeomorph.comp_continuous_iff, Homeomorph.vaddConst, comp_continuous_iff, f.linear, inhabit, linear, vaddConst
-/
theorem continuous_linear_iff {f : P ->ᵃ[R] Q} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V -> W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

/--
theorem `isOpenMap_linear_iff` / 定理 `isOpenMap_linear_iff`

English:
theorem isOpenMap_linear_iff
  given: {f : P ->ᵃ[R] Q}
  statement: IsOpenMap f.linear ↔ IsOpenMap f
  proof: by
  inhabit P
  have :
    (f.linear : V -> W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

中文:
定理 isOpenMap_linear_iff
  条件: {f : P ->ᵃ[R] Q}
  结论: IsOpenMap f.linear ↔ IsOpenMap f
  证明: by
  inhabit P
  have :
    (f.linear : V -> W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

Depends on / 依赖: Homeomorph, Homeomorph.comp_isOpenMap_iff, Homeomorph.vaddConst, comp_isOpenMap_iff, f.linear, inhabit, linear, vaddConst
-/
theorem isOpenMap_linear_iff {f : P ->ᵃ[R] Q} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V -> W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

variable [TopologicalSpace R] [ContinuousSMul R V]

set_option backward.isDefEq.respectTransparency false in
/-- The line map is continuous in all arguments. -/
@[continuity, fun_prop]
/--
theorem `lineMap_continuous_uncurry` / 定理 `lineMap_continuous_uncurry`

English:
theorem lineMap_continuous_uncurry
  proof: by
  simp only [coe_lineMap]
  fun_prop

中文:
定理 lineMap_continuous_uncurry
  证明: by
  simp only [coe_lineMap]
  fun_prop

Depends on / 依赖: coe_lineMap, fun_prop
-/
theorem lineMap_continuous_uncurry :
    Continuous (fun pqt : P × P × R => lineMap pqt.1 pqt.2.1 pqt.2.2) := by
  simp only [coe_lineMap]
  fun_prop

/--
theorem `lineMap_continuous` / 定理 `lineMap_continuous`

English:
theorem lineMap_continuous
  given: {p q : P}
  proof: by
  fun_prop

中文:
定理 lineMap_continuous
  条件: {p q : P}
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem lineMap_continuous {p q : P} :
    Continuous (lineMap p q : R ->ᵃ[R] P) := by
  fun_prop

open Topology Filter

section Tendsto

variable {α : Type*} {l : Filter α}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.Filter.Tendsto.lineMap` / 定理 `_root_.Filter.Tendsto.lineMap`

English:
theorem _root_.Filter.Tendsto.lineMap
  statement: {f₁ f₂ : α -> P} {g : α -> R} {p₁ p₂ : P} {c : R}
  proof: (hg.smul (h₂.vsub h₁)).vadd h₁

中文:
定理 _root_.Filter.Tendsto.lineMap
  结论: {f₁ f₂ : α -> P} {g : α -> R} {p₁ p₂ : P} {c : R}
  证明: (hg.smul (h₂.vsub h₁)).vadd h₁

Depends on / 依赖: hg.smul
-/
theorem _root_.Filter.Tendsto.lineMap {f₁ f₂ : α -> P} {g : α -> R} {p₁ p₂ : P} {c : R}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝 <| AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁

/--
theorem `_root_.Filter.Tendsto.midpoint` / 定理 `_root_.Filter.Tendsto.midpoint`

English:
theorem _root_.Filter.Tendsto.midpoint
  statement: [Invertible (2 : R)] {f₁ f₂ : α -> P} {p₁ p₂ : P}
  proof: h₁.lineMap h₂ tendsto_const_nhds

中文:
定理 _root_.Filter.Tendsto.midpoint
  结论: [Invertible (2 : R)] {f₁ f₂ : α -> P} {p₁ p₂ : P}
  证明: h₁.lineMap h₂ tendsto_const_nhds

Depends on / 依赖: lineMap, tendsto_const_nhds
-/
theorem _root_.Filter.Tendsto.midpoint [Invertible (2 : R)] {f₁ f₂ : α -> P} {p₁ p₂ : P}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) :
    Tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝 <| midpoint R p₁ p₂) :=
  h₁.lineMap h₂ tendsto_const_nhds

end Tendsto

variable {X : Type*} [TopologicalSpace X] {f₁ f₂ : X -> P} {g : X -> R} {s : Set X} {x : X}

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/--
theorem `_root_.ContinuousWithinAt.lineMap` / 定理 `_root_.ContinuousWithinAt.lineMap`

English:
theorem _root_.ContinuousWithinAt.lineMap
  statement: (h₁ : ContinuousWithinAt f₁ s x)
  proof: Tendsto.lineMap h₁ h₂ hg

中文:
定理 _root_.ContinuousWithinAt.lineMap
  结论: (h₁ : ContinuousWithinAt f₁ s x)
  证明: Tendsto.lineMap h₁ h₂ hg

Depends on / 依赖: Tendsto, Tendsto.lineMap, lineMap
-/
theorem _root_.ContinuousWithinAt.lineMap (h₁ : ContinuousWithinAt f₁ s x)
    (h₂ : ContinuousWithinAt f₂ s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => lineMap (f₁ x) (f₂ x) (g x)) s x :=
  Tendsto.lineMap h₁ h₂ hg

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.ContinuousAt.lineMap` / 定理 `_root_.ContinuousAt.lineMap`

English:
theorem _root_.ContinuousAt.lineMap
  statement: (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x)
  proof: by
  fun_prop

中文:
定理 _root_.ContinuousAt.lineMap
  结论: (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem _root_.ContinuousAt.lineMap (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x => lineMap (f₁ x) (f₂ x) (g x)) x := by
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.ContinuousOn.lineMap` / 定理 `_root_.ContinuousOn.lineMap`

English:
theorem _root_.ContinuousOn.lineMap
  statement: (h₁ : ContinuousOn f₁ s) (h₂ : ContinuousOn f₂ s)
  proof: by
  fun_prop

中文:
定理 _root_.ContinuousOn.lineMap
  结论: (h₁ : ContinuousOn f₁ s) (h₂ : ContinuousOn f₂ s)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem _root_.ContinuousOn.lineMap (h₁ : ContinuousOn f₁ s) (h₂ : ContinuousOn f₂ s)
    (hg : ContinuousOn g s) :
    ContinuousOn (fun x => lineMap (f₁ x) (f₂ x) (g x)) s := by
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.Continuous.lineMap` / 定理 `_root_.Continuous.lineMap`

English:
theorem _root_.Continuous.lineMap
  statement: (h₁ : Continuous f₁) (h₂ : Continuous f₂)
  proof: by
  fun_prop

中文:
定理 _root_.Continuous.lineMap
  结论: (h₁ : Continuous f₁) (h₂ : Continuous f₂)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem _root_.Continuous.lineMap (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hg : Continuous g) :
    Continuous (fun x => lineMap (f₁ x) (f₂ x) (g x)) := by
  fun_prop

end Ring

section CommRing

variable [CommRing R] [Module R V] [ContinuousConstSMul R V]

@[continuity, fun_prop]
/--
theorem `homothety_continuous` / 定理 `homothety_continuous`

English:
theorem homothety_continuous
  given: (x : P) (t : R)
  statement: Continuous homothety x t
  proof: by
  rw [coe_homothety]
  fun_prop

中文:
定理 homothety_continuous
  条件: (x : P) (t : R)
  结论: Continuous homothety x t
  证明: by
  rw [coe_homothety]
  fun_prop

Depends on / 依赖: coe_homothety, fun_prop
-/
theorem homothety_continuous (x : P) (t : R) : Continuous homothety x t := by
  rw [coe_homothety]
  fun_prop

variable (R) [TopologicalSpace R] [Module R W] [ContinuousSMul R W] (x : Q) {s : Set Q}

open Topology

/--
theorem `_root_.eventually_homothety_mem_of_mem_interior` / 定理 `_root_.eventually_homothety_mem_of_mem_interior`

English:
theorem _root_.eventually_homothety_mem_of_mem_interior
  given: {y : Q} (hy : y in interior s)
  proof: by
  have cont : Continuous (fun δ : R => homothety x δ y) := lineMap_continuous
  filter_upwards [cont.tendsto' 1 y (by simp) |>.eventually (isOpen_interior.eventually_mem hy)]
    with _ h using interior_subset h

中文:
定理 _root_.eventually_homothety_mem_of_mem_interior
  条件: {y : Q} (hy : y in interior s)
  证明: by
  have cont : Continuous (fun δ : R => homothety x δ y) := lineMap_continuous
  filter_upwards [cont.tendsto' 1 y (by simp) |>.eventually (isOpen_interior.eventually_mem hy)]
    with _ h using interior_subset h

Depends on / 依赖: Continuous, cont.tendsto, eventually, eventually_mem, filter_upwards, homothety, interior_subset, isOpen_interior, isOpen_interior.eventually_mem, lineMap_continuous, tendsto
-/
theorem _root_.eventually_homothety_mem_of_mem_interior {y : Q} (hy : y in interior s) :
    forallᶠ δ in 𝓝 (1 : R), homothety x δ y in s := by
  have cont : Continuous (fun δ : R => homothety x δ y) := lineMap_continuous
  filter_upwards [cont.tendsto' 1 y (by simp) |>.eventually (isOpen_interior.eventually_mem hy)]
    with _ h using interior_subset h

/--
theorem `_root_.eventually_homothety_image_subset_of_finite_subset_interior` / 定理 `_root_.eventually_homothety_image_subset_of_finite_subset_interior`

English:
theorem _root_.eventually_homothety_image_subset_of_finite_subset_interior
  statement: {t : Set Q}
  proof: by
  suffices forall y in t, forallᶠ δ in 𝓝 (1 : R), homothety x δ y in s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior R x (h hy)

中文:
定理 _root_.eventually_homothety_image_subset_of_finite_subset_interior
  结论: {t : Set Q}
  证明: by
  suffices forall y in t, forallᶠ δ in 𝓝 (1 : R), homothety x δ y in s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior R x (h hy)

Depends on / 依赖: Filter, Filter.eventually_all_finite, Set.image_subset_iff, eventually_all_finite, eventually_homothety_mem_of_mem_interior, homothety, image_subset_iff, simp_rw
-/
theorem _root_.eventually_homothety_image_subset_of_finite_subset_interior {t : Set Q}
    (ht : t.Finite) (h : t subseteq interior s) : forallᶠ δ in 𝓝 (1 : R), homothety x δ '' t subseteq s := by
  suffices forall y in t, forallᶠ δ in 𝓝 (1 : R), homothety x δ y in s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior R x (h hy)

end CommRing

section Field

variable [Field R] [Module R V] [ContinuousConstSMul R V]

/--
theorem `homothety_isOpenMap` / 定理 `homothety_isOpenMap`

English:
theorem homothety_isOpenMap
  given: (x : P) (t : R) (ht : t != 0)
  statement: IsOpenMap homothety x t
  proof: by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

中文:
定理 homothety_isOpenMap
  条件: (x : P) (t : R) (ht : t != 0)
  结论: IsOpenMap homothety x t
  证明: by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

Depends on / 依赖: AffineMap, AffineMap.comp_apply, IsOpenMap, IsOpenMap.of_inverse, comp_apply, homothety_continuous, homothety_mul, of_inverse
-/
theorem homothety_isOpenMap (x : P) (t : R) (ht : t != 0) : IsOpenMap homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

end Field

end AffineMap
