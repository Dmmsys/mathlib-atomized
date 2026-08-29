/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Algebra.Homology.CommSq

/-!
# The exact sequence attached to a pushout square

Consider a pushout square in an abelian category:

```
    t
 X₁ ⟶ X₂
l| |r
 v v
 X₃ ⟶ X₄
    b
```

We study the associated exact sequence `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0`.
We also show that the induced morphism `kernel t ⟶ kernel b` is an epimorphism.

-/

public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Abelian

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange
  body: .mk' (fun _ _ _ _ _ _ (_ : Mono _) => inferInstanceAs (Mono _))

中文:
实例 :
  签名: (MorphismProperty.monomorphisms C).是StableUnderCobaseChange
  定义体: .mk' (fun _ _ _ _ _ _ (_ : Mono _) => inferInstanceAs (Mono _))
-/
instance : (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange :=
  .mk' (fun _ _ _ _ _ _ (_ : Mono _) => inferInstanceAs (Mono _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.epimorphisms C).IsStableUnderBaseChange
  body: .mk' (fun _ _ _ _ _ _ (_ : Epi _) => inferInstanceAs (Epi _))

中文:
实例 :
  签名: (MorphismProperty.epimorphisms C).是StableUnderBaseChange
  定义体: .mk' (fun _ _ _ _ _ _ (_ : Epi _) => inferInstanceAs (Epi _))
-/
instance : (MorphismProperty.epimorphisms C).IsStableUnderBaseChange :=
  .mk' (fun _ _ _ _ _ _ (_ : Epi _) => inferInstanceAs (Epi _))

end Abelian

variable {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

namespace IsPushout

/--
lemma `exact_shortComplex` / 引理 `exact_shortComplex`

English:
lemma exact_shortComplex
  given: (h : IsPushout t l r b)
  statement: h.shortComplex.Exact
  proof: h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCofork

中文:
引理 exact_shortComplex
  条件: (h : 是推出 t l r b)
  结论: h.shortComplex.正合
  证明: h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCofork

Depends on / 依赖: exact_of_g_is_cokernel, h.isColimitCokernelCofork, h.shortComplex.exact_of_g_is_cokernel, isColimitCokernelCofork, shortComplex
-/
lemma exact_shortComplex (h : IsPushout t l r b) : h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCofork

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `hom_eq_add_up_to_refinements` / 引理 `hom_eq_add_up_to_refinements`

English:
lemma hom_eq_add_up_to_refinements
  given: (h : IsPushout t l r b) {T : C} (x₄ : T ⟶ X₄)
  proof: by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, u, hu⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g x₄
  refine ⟨T', π, inferInstance, u ≫ biprod.fst, u ≫ biprod.snd, ?_⟩
  simp only [hu, assoc, ← Preadditive.comp_add]
  congr
  cat_disch

中文:
引理 hom_eq_add_up_to_refinements
  条件: (h : 是推出 t l r b) {T : C} (x₄ : T ⟶ X₄)
  证明: by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, u, hu⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g x₄
  refine ⟨T', π, inferInstance, u ≫ biprod.fst, u ≫ biprod.snd, ?_⟩
  simp only [hu, assoc, ← Preadditive.comp_add]
  congr
  cat_disch

Depends on / 依赖: Preadditive, Preadditive.comp_add, biprod, biprod.fst, biprod.snd, cat_disch, comp_add, epi_shortComplex_g, h.epi_shortComplex_g, h.shortComplex.g, shortComplex, surjective_up_to_refinements_of_epi
-/
lemma hom_eq_add_up_to_refinements (h : IsPushout t l r b) {T : C} (x₄ : T ⟶ X₄) :
    exists (T' : C) (π : T' ⟶ T) (_ : Epi π) (x₂ : T' ⟶ X₂) (x₃ : T' ⟶ X₃),
      π ≫ x₄ = x₂ ≫ r + x₃ ≫ b := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, u, hu⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g x₄
  refine ⟨T', π, inferInstance, u ≫ biprod.fst, u ≫ biprod.snd, ?_⟩
  simp only [hu, assoc, ← Preadditive.comp_add]
  congr
  cat_disch

/--
lemma `mono_of_isPullback_of_mono` / 引理 `mono_of_isPullback_of_mono`

English:
lemma mono_of_isPullback_of_mono
  proof: Preadditive.mono_of_cancel_zero _ (fun {T₀} x₄ hx₄ => by
    obtain ⟨T₁, π, _, x₂, x₃, eq⟩ := hom_eq_add_up_to_refinements h₁ x₄
    have fac₃ : (-x₂) ≫ r' = x₃ ≫ b' := by
      rw [Preadditive.neg_comp]; rw [neg_eq_iff_add_eq_zero]; rw [← fac₂]; rw [← fac₁]; rw [← assoc]; rw [← assoc]; rw [← Preadditive.add_comp]; rw [← eq]; rw [assoc]; rw [hx₄]; rw [comp_zero]
    obtain ⟨x₂', hx₂'⟩ : exists x₂', π ≫ x₄ = x₂' ≫ r := by
      refine ⟨x₂ + h₂.lift (-x₂) x₃ fac₃ ≫ t, ?_⟩
      rw [eq]; rw [Preadditive.add_comp]; rw [assoc]; rw [h₁.w]; rw [IsPullback.lift_snd_assoc]; rw [add_comm]
    rw [← cancel_epi π]; rw [comp_zero]; rw [reassoc_of% hx₂']; rw [fac₁] at hx₄
    obtain rfl := zero_of_comp_mono _ hx₄
    rw [zero_comp] at hx₂'
    rw [← cancel_epi π]; rw [hx₂']; rw [comp_zero])

中文:
引理 mono_of_isPullback_of_mono
  证明: Preadditive.mono_of_cancel_zero _ (fun {T₀} x₄ hx₄ => by
    obtain ⟨T₁, π, _, x₂, x₃, eq⟩ := hom_eq_add_up_to_refinements h₁ x₄
    have fac₃ : (-x₂) ≫ r' = x₃ ≫ b' := by
      rw [Preadditive.neg_comp]; rw [neg_eq_iff_add_eq_zero]; rw [← fac₂]; rw [← fac₁]; rw [← assoc]; rw [← assoc]; rw [← Preadditive.add_comp]; rw [← eq]; rw [assoc]; rw [hx₄]; rw [comp_zero]
    obtain ⟨x₂', hx₂'⟩ : exists x₂', π ≫ x₄ = x₂' ≫ r := by
      refine ⟨x₂ + h₂.lift (-x₂) x₃ fac₃ ≫ t, ?_⟩
      rw [eq]; rw [Preadditive.add_comp]; rw [assoc]; rw [h₁.w]; rw [IsPullback.lift_snd_assoc]; rw [add_comm]
    rw [← cancel_epi π]; rw [comp_zero]; rw [reassoc_of% hx₂']; rw [fac₁] at hx₄
    obtain rfl := zero_of_comp_mono _ hx₄
    rw [zero_comp] at hx₂'
    rw [← cancel_epi π]; rw [hx₂']; rw [comp_zero])

Depends on / 依赖: Preadditive, Preadditive.add_comp, Preadditive.mono_of_cancel_zero, Preadditive.neg_comp, add_comp, comp_zero, hom_eq_add_up_to_refinements, mono_of_cancel_zero, neg_comp, neg_eq_iff_add_eq_zero
-/
lemma mono_of_isPullback_of_mono
    (h₁ : IsPushout t l r b) {X₅ : C} {r' : X₂ ⟶ X₅} {b' : X₃ ⟶ X₅}
    (h₂ : IsPullback t l r' b') (k : X₄ ⟶ X₅)
    (fac₁ : r ≫ k = r') (fac₂ : b ≫ k = b') [Mono r'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} x₄ hx₄ => by
    obtain ⟨T₁, π, _, x₂, x₃, eq⟩ := hom_eq_add_up_to_refinements h₁ x₄
    have fac₃ : (-x₂) ≫ r' = x₃ ≫ b' := by
      rw [Preadditive.neg_comp]; rw [neg_eq_iff_add_eq_zero]; rw [← fac₂]; rw [← fac₁]; rw [← assoc]; rw [← assoc]; rw [← Preadditive.add_comp]; rw [← eq]; rw [assoc]; rw [hx₄]; rw [comp_zero]
    obtain ⟨x₂', hx₂'⟩ : exists x₂', π ≫ x₄ = x₂' ≫ r := by
      refine ⟨x₂ + h₂.lift (-x₂) x₃ fac₃ ≫ t, ?_⟩
      rw [eq]; rw [Preadditive.add_comp]; rw [assoc]; rw [h₁.w]; rw [IsPullback.lift_snd_assoc]; rw [add_comm]
    rw [← cancel_epi π]; rw [comp_zero]; rw [reassoc_of% hx₂']; rw [fac₁] at hx₄
    obtain rfl := zero_of_comp_mono _ hx₄
    rw [zero_comp] at hx₂'
    rw [← cancel_epi π]; rw [hx₂']; rw [comp_zero])

end IsPushout

namespace IsPullback

/--
lemma `exact_shortComplex'` / 引理 `exact_shortComplex'`

English:
lemma exact_shortComplex'
  given: (h : IsPullback t l r b)
  statement: h.shortComplex'.Exact
  proof: h.shortComplex'.exact_of_f_is_kernel
    h.isLimitKernelFork

中文:
引理 exact_shortComplex'
  条件: (h : 是拉回 t l r b)
  结论: h.shortComplex'.正合
  证明: h.shortComplex'.exact_of_f_is_kernel
    h.isLimitKernelFork

Depends on / 依赖: exact_of_f_is_kernel, h.isLimitKernelFork, h.shortComplex, isLimitKernelFork, shortComplex
-/
lemma exact_shortComplex' (h : IsPullback t l r b) : h.shortComplex'.Exact :=
  h.shortComplex'.exact_of_f_is_kernel
    h.isLimitKernelFork

/-!
Note: if `h : IsPullback t l r b`, then `X₁ ⟶ X₂ ⊞ X₃` is a monomorphism,
which can be translated in concrete terms thanks to the lemma `IsPullback.hom_ext`:
if a morphism `f : Z ⟶ X₁` becomes zero after composing with `X₁ ⟶ X₂` and
`X₁ ⟶ X₃`, then `f = 0`. This is the reason why we do not state the dual
statement to `IsPushout.hom_eq_add_up_to_refinements`.
-/

end IsPullback

namespace Abelian

variable {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/--
lemma `mono_cokernel_map_of_isPullback` / 引理 `mono_cokernel_map_of_isPullback`

English:
lemma mono_cokernel_map_of_isPullback
  given: (sq : IsPullback t l r b)
  proof: by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ z hz
  obtain ⟨A₁, π₁, _, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi (cokernel.π t) z
  have : (ShortComplex.mk _ _ (cokernel.condition b)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel b)
  obtain ⟨A₂, π₂, _, x₃, hx₃⟩ := this.exact_up_to_refinements (x₂ ≫ r) (by
    simpa [hz] using hx₂.symm =≫ cokernel.map _ _ _ _ sq.w)
  obtain ⟨x₁, hx₁, rfl⟩ := sq.exists_lift (π₂ ≫ x₂) x₃ (by simpa)
  simp [← cancel_epi π₁, ← cancel_epi π₂, hx₂, ← reassoc_of% hx₁]

中文:
引理 mono_cokernel_map_of_isPullback
  条件: (sq : 是拉回 t l r b)
  证明: by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ z hz
  obtain ⟨A₁, π₁, _, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi (cokernel.π t) z
  have : (ShortComplex.mk _ _ (cokernel.condition b)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel b)
  obtain ⟨A₂, π₂, _, x₃, hx₃⟩ := this.exact_up_to_refinements (x₂ ≫ r) (by
    simpa [hz] using hx₂.symm =≫ cokernel.map _ _ _ _ sq.w)
  obtain ⟨x₁, hx₁, rfl⟩ := sq.exists_lift (π₂ ≫ x₂) x₃ (by simpa)
  simp [← cancel_epi π₁, ← cancel_epi π₂, hx₂, ← reassoc_of% hx₁]

Depends on / 依赖: Preadditive, Preadditive.mono_iff_cancel_zero, ShortComplex, ShortComplex.exact_of_g_is_cokernel, ShortComplex.mk, cancel_epi, cokernel, cokernel.condition, cokernel.map, cokernelIsCokernel, condition, exact_of_g_is_cokernel, exact_up_to_refinements, exists_lift, mono_iff_cancel_zero, sq.exists_lift, sq.w, surjective_up_to_refinements_of_epi, this.exact_up_to_refinements
-/
lemma mono_cokernel_map_of_isPullback (sq : IsPullback t l r b) :
    Mono (cokernel.map _ _ _ _ sq.w) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ z hz
  obtain ⟨A₁, π₁, _, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi (cokernel.π t) z
  have : (ShortComplex.mk _ _ (cokernel.condition b)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel b)
  obtain ⟨A₂, π₂, _, x₃, hx₃⟩ := this.exact_up_to_refinements (x₂ ≫ r) (by
    simpa [hz] using hx₂.symm =≫ cokernel.map _ _ _ _ sq.w)
  obtain ⟨x₁, hx₁, rfl⟩ := sq.exists_lift (π₂ ≫ x₂) x₃ (by simpa)
  simp [← cancel_epi π₁, ← cancel_epi π₂, hx₂, ← reassoc_of% hx₁]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `epi_kernel_map_of_isPushout` / 引理 `epi_kernel_map_of_isPushout`

English:
lemma epi_kernel_map_of_isPushout
  given: (sq : IsPushout t l r b)
  proof: by
  rw [epi_iff_surjective_up_to_refinements]
  intro A₀ z
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := ((ShortComplex.mk _ _
    sq.cokernelCofork.condition).exact_of_g_is_cokernel
      sq.isColimitCokernelCofork).exact_up_to_refinements
        (z ≫ kernel.ι _ ≫ biprod.inr) (by simp)
  refine ⟨A₁, π₁, inferInstance, -kernel.lift _ x₁ ?_, ?_⟩
  · simpa using hx₁.symm =≫ biprod.fst
  · ext
    simpa using hx₁ =≫ biprod.snd

中文:
引理 epi_kernel_map_of_isPushout
  条件: (sq : 是推出 t l r b)
  证明: by
  rw [epi_iff_surjective_up_to_refinements]
  intro A₀ z
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := ((ShortComplex.mk _ _
    sq.cokernelCofork.condition).exact_of_g_is_cokernel
      sq.isColimitCokernelCofork).exact_up_to_refinements
        (z ≫ kernel.ι _ ≫ biprod.inr) (by simp)
  refine ⟨A₁, π₁, inferInstance, -kernel.lift _ x₁ ?_, ?_⟩
  · simpa using hx₁.symm =≫ biprod.fst
  · ext
    simpa using hx₁ =≫ biprod.snd

Depends on / 依赖: ShortComplex, ShortComplex.mk, biprod, biprod.fst, biprod.inr, biprod.snd, cokernelCofork, condition, epi_iff_surjective_up_to_refinements, exact_of_g_is_cokernel, exact_up_to_refinements, isColimitCokernelCofork, kernel, kernel.lift, sq.cokernelCofork.condition, sq.isColimitCokernelCofork
-/
lemma epi_kernel_map_of_isPushout (sq : IsPushout t l r b) :
    Epi (kernel.map _ _ _ _ sq.w) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A₀ z
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := ((ShortComplex.mk _ _
    sq.cokernelCofork.condition).exact_of_g_is_cokernel
      sq.isColimitCokernelCofork).exact_up_to_refinements
        (z ≫ kernel.ι _ ≫ biprod.inr) (by simp)
  refine ⟨A₁, π₁, inferInstance, -kernel.lift _ x₁ ?_, ?_⟩
  · simpa using hx₁.symm =≫ biprod.fst
  · ext
    simpa using hx₁ =≫ biprod.snd

end Abelian

end CategoryTheory
