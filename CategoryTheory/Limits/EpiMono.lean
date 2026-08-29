/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Relation between mono/epi and pullback/pushout squares

In this file, monomorphisms and epimorphisms are characterized in terms
of pullback and pushout squares. For example, we obtain `mono_iff_isPullback`
which asserts that a morphism `f : X ⟶ Y` is a monomorphism iff the obvious
square

```
X ⟶ X
| |
v v
X ⟶ Y
```

is a pullback square.


-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}

section Mono

variable {c : PullbackCone f f}

/--
lemma `mono_iff_fst_eq_snd` / 引理 `mono_iff_fst_eq_snd`

English:
lemma mono_iff_fst_eq_snd
  given: (hc : IsLimit c)
  statement: Mono f ↔ c.fst = c.snd
  proof: by
  constructor
  · intro hf
    simpa only [← cancel_mono f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc g g' h
    rw [hf]

中文:
引理 mono_iff_fst_eq_snd
  条件: (hc : IsLimit c)
  结论: Mono f ↔ c.fst = c.snd
  证明: by
  constructor
  · intro hf
    simpa only [← cancel_mono f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc g g' h
    rw [hf]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift, c.condition, cancel_mono, condition
-/
lemma mono_iff_fst_eq_snd (hc : IsLimit c) : Mono f ↔ c.fst = c.snd := by
  constructor
  · intro hf
    simpa only [← cancel_mono f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc g g' h
    rw [hf]

/--
lemma `mono_iff_isIso_fst` / 引理 `mono_iff_isIso_fst`

English:
lemma mono_iff_isIso_fst
  given: (hc : IsLimit c)
  statement: Mono f ↔ IsIso c.fst
  proof: by
  rw [mono_iff_fst_eq_snd hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine ⟨φ, PullbackCone.IsLimit.hom_ext hc ?_ ?_, hφ₁⟩
    · simp only [assoc, hφ₁, id_comp, comp_id]
    · simp only [assoc, hφ₂, id_comp, comp_id, h]
  · i

中文:
引理 mono_iff_isIso_fst
  条件: (hc : IsLimit c)
  结论: Mono f ↔ IsIso c.fst
  证明: by
  rw [mono_iff_fst_eq_snd hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine ⟨φ, PullbackCone.IsLimit.hom_ext hc ?_ ?_, hφ₁⟩
    · simp only [assoc, hφ₁, id_comp, comp_id]
    · simp only [assoc, hφ₂, id_comp, comp_id, h]
  · i

Depends on / 依赖: IsLimit, IsSplitEpi, IsSplitEpi.mk, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, SplitEpi, SplitEpi.mk, c.fst, cancel_mono, comp_id, hom_ext, id_comp, mono_iff_fst_eq_snd
-/
lemma mono_iff_isIso_fst (hc : IsLimit c) : Mono f ↔ IsIso c.fst := by
  rw [mono_iff_fst_eq_snd hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine ⟨φ, PullbackCone.IsLimit.hom_ext hc ?_ ?_, hφ₁⟩
    · simp only [assoc, hφ₁, id_comp, comp_id]
    · simp only [assoc, hφ₂, id_comp, comp_id, h]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    have : IsSplitEpi φ := IsSplitEpi.mk ⟨SplitEpi.mk c.fst (by
      rw [← cancel_mono c.fst]; rw [assoc]; rw [id_comp]; rw [hφ₁]; rw [comp_id])⟩
    rw [← cancel_epi φ]; rw [hφ₁]; rw [hφ₂]

/--
lemma `mono_iff_isIso_snd` / 引理 `mono_iff_isIso_snd`

English:
lemma mono_iff_isIso_snd
  given: (hc : IsLimit c)
  statement: Mono f ↔ IsIso c.snd
  proof: mono_iff_isIso_fst (PullbackCone.flipIsLimit hc)

中文:
引理 mono_iff_isIso_snd
  条件: (hc : IsLimit c)
  结论: Mono f ↔ IsIso c.snd
  证明: mono_iff_isIso_fst (PullbackCone.flipIsLimit hc)

Depends on / 依赖: PullbackCone, PullbackCone.flipIsLimit, flipIsLimit, mono_iff_isIso_fst
-/
lemma mono_iff_isIso_snd (hc : IsLimit c) : Mono f ↔ IsIso c.snd :=
  mono_iff_isIso_fst (PullbackCone.flipIsLimit hc)

variable (f)

/--
lemma `mono_iff_isPullback` / 引理 `mono_iff_isPullback`

English:
lemma mono_iff_isPullback
  statement: Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f
  proof: by
  constructor
  · intro
    exact IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)
  · intro hf
    exact (mono_iff_fst_eq_snd hf.isLimit).2 rfl

中文:
引理 mono_iff_isPullback
  结论: Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f
  证明: by
  constructor
  · intro
    exact IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)
  · intro hf
    exact (mono_iff_fst_eq_snd hf.isLimit).2 rfl

Depends on / 依赖: IsPullback, IsPullback.of_isLimit, PullbackCone, PullbackCone.isLimitMkIdId, hf.isLimit, isLimit, isLimitMkIdId, mono_iff_fst_eq_snd, of_isLimit
-/
lemma mono_iff_isPullback : Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f := by
  constructor
  · intro
    exact IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)
  · intro hf
    exact (mono_iff_fst_eq_snd hf.isLimit).2 rfl

end Mono

section Epi

variable {c : PushoutCocone f f}

/--
lemma `epi_iff_inl_eq_inr` / 引理 `epi_iff_inl_eq_inr`

English:
lemma epi_iff_inl_eq_inr
  given: (hc : IsColimit c)
  statement: Epi f ↔ c.inl = c.inr
  proof: by
  constructor
  · intro hf
    simpa only [← cancel_epi f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PushoutCocone.IsColimit.desc' hc g g' h
    rw [hf]

中文:
引理 epi_iff_inl_eq_inr
  条件: (hc : IsColimit c)
  结论: Epi f ↔ c.inl = c.inr
  证明: by
  constructor
  · intro hf
    simpa only [← cancel_epi f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PushoutCocone.IsColimit.desc' hc g g' h
    rw [hf]

Depends on / 依赖: IsColimit, PushoutCocone, PushoutCocone.IsColimit.desc, c.condition, cancel_epi, condition
-/
lemma epi_iff_inl_eq_inr (hc : IsColimit c) : Epi f ↔ c.inl = c.inr := by
  constructor
  · intro hf
    simpa only [← cancel_epi f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PushoutCocone.IsColimit.desc' hc g g' h
    rw [hf]

/--
lemma `epi_iff_isIso_inl` / 引理 `epi_iff_isIso_inl`

English:
lemma epi_iff_isIso_inl
  given: (hc : IsColimit c)
  statement: Epi f ↔ IsIso c.inl
  proof: by
  rw [epi_iff_inl_eq_inr hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc ?_ ?_⟩
    · simp only [comp_id, reassoc_of% hφ₁]
    · simp only [comp_id, h, reassoc_of% hφ₂]
  · intr

中文:
引理 epi_iff_isIso_inl
  条件: (hc : IsColimit c)
  结论: Epi f ↔ IsIso c.inl
  证明: by
  rw [epi_iff_inl_eq_inr hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc ?_ ?_⟩
    · simp only [comp_id, reassoc_of% hφ₁]
    · simp only [comp_id, h, reassoc_of% hφ₂]
  · intr

Depends on / 依赖: IsColimit, IsSplitMono, IsSplitMono.mk, PushoutCocone, PushoutCocone.IsColimit.desc, PushoutCocone.IsColimit.hom_ext, SplitMono, SplitMono.mk, c.inl, cancel_epi, cancel_mono, comp_id, epi_iff_inl_eq_inr, hom_ext, reassoc_of
-/
lemma epi_iff_isIso_inl (hc : IsColimit c) : Epi f ↔ IsIso c.inl := by
  rw [epi_iff_inl_eq_inr hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc ?_ ?_⟩
    · simp only [comp_id, reassoc_of% hφ₁]
    · simp only [comp_id, h, reassoc_of% hφ₂]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    have : IsSplitMono φ := IsSplitMono.mk ⟨SplitMono.mk c.inl (by
      rw [← cancel_epi c.inl]; rw [reassoc_of% hφ₁]; rw [comp_id])⟩
    rw [← cancel_mono φ]; rw [hφ₁]; rw [hφ₂]

/--
lemma `epi_iff_isIso_inr` / 引理 `epi_iff_isIso_inr`

English:
lemma epi_iff_isIso_inr
  given: (hc : IsColimit c)
  statement: Epi f ↔ IsIso c.inr
  proof: epi_iff_isIso_inl (PushoutCocone.flipIsColimit hc)

中文:
引理 epi_iff_isIso_inr
  条件: (hc : IsColimit c)
  结论: Epi f ↔ IsIso c.inr
  证明: epi_iff_isIso_inl (PushoutCocone.flipIsColimit hc)

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, epi_iff_isIso_inl, flipIsColimit
-/
lemma epi_iff_isIso_inr (hc : IsColimit c) : Epi f ↔ IsIso c.inr :=
  epi_iff_isIso_inl (PushoutCocone.flipIsColimit hc)

variable (f)

/--
lemma `epi_iff_isPushout` / 引理 `epi_iff_isPushout`

English:
lemma epi_iff_isPushout
  statement: Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y)
  proof: by
  constructor
  · intro
    exact IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  · intro hf
    exact (epi_iff_inl_eq_inr hf.isColimit).2 rfl

中文:
引理 epi_iff_isPushout
  结论: Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y)
  证明: by
  constructor
  · intro
    exact IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  · intro hf
    exact (epi_iff_inl_eq_inr hf.isColimit).2 rfl

Depends on / 依赖: IsPushout, IsPushout.of_isColimit, PushoutCocone, PushoutCocone.isColimitMkIdId, epi_iff_inl_eq_inr, hf.isColimit, isColimit, isColimitMkIdId, of_isColimit
-/
lemma epi_iff_isPushout : Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y) := by
  constructor
  · intro
    exact IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  · intro hf
    exact (epi_iff_inl_eq_inr hf.isColimit).2 rfl

end Epi

end CategoryTheory
