/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Differentials
public import Mathlib.CategoryTheory.ComposableArrows.Four

/-!
# Induced morphisms that are epi or mono

Given a spectral object in an abelian category, we show that certain
morphisms `E^n(f₁, f₂, f₃) ⟶ E^n(f₁', f₂', f₃')` are monomorphisms,
epimorphisms or isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

section

variable
  {i₀' i₀ i₁ i₂ i₃ i₃' : ι} (f₁ : i₀ ⟶ i₁)
  (f₁' : i₀' ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₃' : i₂ ⟶ i₃')
  (n₀ n₁ n₂ n₃ : Int)

/--
lemma `epi_map` / 引理 `epi_map`

English:
lemma epi_map
  statement: (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : Int)
  proof: have : Epi (X.cyclesMap f₁ f₂ f₁ f₂ (𝟙 (mk₂ f₁ f₂)) n₁) := by rw [X.cyclesMap_id]; infer_instance
  epi_of_epi_fac (X.πE_map _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂ (by cat_disch) _ _)

中文:
引理 epi_map
  结论: (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : 整数)
  证明: have : Epi (X.cyclesMap f₁ f₂ f₁ f₂ (𝟙 (mk₂ f₁ f₂)) n₁) := by rw [X.cyclesMap_id]; infer_instance
  epi_of_epi_fac (X.πE_map _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂ (by cat_disch) _ _)

Depends on / 依赖: X.cyclesMap, X.cyclesMap_id, X.map, cat_disch, cyclesMap, cyclesMap_id, epi_of_epi_fac, infer_instance
-/
lemma epi_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : Int)
    (hα₀ : α.app 0 = 𝟙 _ := by cat_disch) (hα₁ : α.app 1 = 𝟙 _ := by cat_disch)
    (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃' α n₀ n₁ n₂ hn₁ hn₂) :=
  have : Epi (X.cyclesMap f₁ f₂ f₁ f₂ (𝟙 (mk₂ f₁ f₂)) n₁) := by rw [X.cyclesMap_id]; infer_instance
  epi_of_epi_fac (X.πE_map _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂ (by cat_disch) _ _)

/--
lemma `mono_map` / 引理 `mono_map`

English:
lemma mono_map
  statement: (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : Int)
  proof: by
  have := X.map_ιE _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id]; rw [comp_id] at this
  exact mono_of_mono_fac this

中文:
引理 mono_map
  结论: (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : 整数)
  证明: by
  have := X.map_ιE _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id]; rw [comp_id] at this
  exact mono_of_mono_fac this

Depends on / 依赖: X.map, X.map_, cat_disch, comp_id, mono_of_mono_fac, opcyclesMap_id
-/
lemma mono_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : Int)
    (hα₁ : α.app 1 = 𝟙 _ := by cat_disch) (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hα₃ : α.app 3 = 𝟙 _ := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Mono (X.map f₁ f₂ f₃ f₁' f₂ f₃ α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.map_ιE _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id]; rw [comp_id] at this
  exact mono_of_mono_fac this

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : Int)

@[reassoc (attr := simp)]
/--
lemma `d_map_fourδ₄Toδ₃` / 引理 `d_map_fourδ₄Toδ₃`

English:
lemma d_map_fourδ₄Toδ₃
  statement: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂), ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃]

中文:
引理 d_map_fourδ₄Toδ₃
  结论: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂), ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃]

Depends on / 依赖: X.map, X.toCycles, X.toCycles_, cancel_epi, toCycles
-/
lemma d_map_fourδ₄Toδ₃ (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃ = 0 := by
  simp [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂), ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃]

instance (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.epi_map _ _ _ _ _ _ _ _ _ rfl rfl rfl hn₂ hn₃ rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_map_fourδ₄Toδ₃` / 引理 `isIso_map_fourδ₄Toδ₃`

English:
lemma isIso_map_fourδ₄Toδ₃
  statement: (h : (X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0 := by cat_disch)
  proof: by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ f₃ f₄ f₃₄ h₃₄ _).epi_f h
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch

中文:
引理 isIso_map_fourδ₄Toδ₃
  结论: (h : (X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0 := by cat_disch)
  证明: by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ f₃ f₄ f₃₄ h₃₄ _).epi_f h
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch

Depends on / 依赖: ShortComplex, ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono, X.exact, X.map, cat_disch, convert, epi_f, isIso_homologyMap_of_epi_of_isIso_of_mono
-/
lemma isIso_map_fourδ₄Toδ₃ (h : (X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0 := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ f₃ f₄ f₃₄ h₃₄ _).epi_f h
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch

/--
lemma `isIso_map_fourδ₄Toδ₃_of_isZero` / 引理 `isIso_map_fourδ₄Toδ₃_of_isZero`

English:
lemma isIso_map_fourδ₄Toδ₃_of_isZero
  statement: (h : IsZero ((X.H n₁).obj (mk₁ f₄)) := by cat_disch)
  proof: X.isIso_map_fourδ₄Toδ₃ _ _ _ _ _ _ _ _ _ (h.eq_of_tgt _ _)

@[reassoc (attr := simp)]

中文:
引理 isIso_map_fourδ₄Toδ₃_of_isZero
  结论: (h : 是零 ((X.H n₁).obj (mk₁ f₄)) := by cat_disch)
  证明: X.isIso_map_fourδ₄Toδ₃ _ _ _ _ _ _ _ _ _ (h.eq_of_tgt _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: X.isIso_map_four, X.map, cat_disch, eq_of_tgt, h.eq_of_tgt
-/
lemma isIso_map_fourδ₄Toδ₃_of_isZero (h : IsZero ((X.H n₁).obj (mk₁ f₄)) := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.isIso_map_fourδ₄Toδ₃ _ _ _ _ _ _ _ _ _ (h.eq_of_tgt _ _)

@[reassoc (attr := simp)]
/--
lemma `map_fourδ₁Toδ₀_d` / 引理 `map_fourδ₁Toδ₀_d`

English:
lemma map_fourδ₁Toδ₀_d
  statement: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  simp [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂),
    X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃, X.map_ιE_assoc
    f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by cat_disch) hn₁

中文:
引理 map_fourδ₁Toδ₀_d
  结论: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  simp [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂),
    X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃, X.map_ιE_assoc
    f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by cat_disch) hn₁

Depends on / 依赖: X.d_, X.fromOpcycles, X.map, X.map_, cancel_mono, cat_disch, fromOpcycles
-/
lemma map_fourδ₁Toδ₀_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ = 0 := by
  simp [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂),
    X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃, X.map_ιE_assoc
    f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by cat_disch) hn₁ hn₂]

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.mono_map _ _ _ _ _ _ _ _ _ rfl rfl rfl _ _ rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_map_fourδ₁Toδ₀` / 引理 `isIso_map_fourδ₁Toδ₀`

English:
lemma isIso_map_fourδ₁Toδ₀
  statement: (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
  proof: by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert! (inferInstance : Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h

中文:
引理 isIso_map_fourδ₁Toδ₀
  结论: (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
  证明: by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert! (inferInstance : Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h

Depends on / 依赖: ShortComplex, ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono, X.exact, X.map, cat_disch, convert, isIso_homologyMap_of_epi_of_isIso_of_mono, mono_g
-/
lemma isIso_map_fourδ₁Toδ₀ (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert! (inferInstance : Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h

/--
lemma `isIso_map_fourδ₁Toδ₀_of_isZero` / 引理 `isIso_map_fourδ₁Toδ₀_of_isZero`

English:
lemma isIso_map_fourδ₁Toδ₀_of_isZero
  statement: (h : IsZero ((X.H n₂).obj (mk₁ f₂)))
  proof: X.isIso_map_fourδ₁Toδ₀ _ _ _ _ _ _ _ _ _ (h.eq_of_src _ _)

中文:
引理 isIso_map_fourδ₁Toδ₀_of_isZero
  结论: (h : 是零 ((X.H n₂).obj (mk₁ f₂)))
  证明: X.isIso_map_fourδ₁Toδ₀ _ _ _ _ _ _ _ _ _ (h.eq_of_src _ _)

Depends on / 依赖: X.isIso_map_four, X.map, eq_of_src, h.eq_of_src
-/
lemma isIso_map_fourδ₁Toδ₀_of_isZero (h : IsZero ((X.H n₂).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.isIso_map_fourδ₁Toδ₀ _ _ _ _ _ _ _ _ _ (h.eq_of_src _ _)

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ <= i₁)
  (hi₁₂ : i₁ <= i₂) (hi₂₃ : i₂ <= i₃) (hi₃₄ : i₃ <= i₄) (hi₄₅ : i₄ <= i₅)

/--
Definition of `mapFourδ₁Toδ₀'` / `mapFourδ₁Toδ₀'` 的定义

English:
abbreviation mapFourδ₁Toδ₀'
  signature: (n₀ n₁ n₂ : Int)
  body: X'.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

中文:
缩写 mapFourδ₁Toδ₀'
  签名: (n₀ n₁ n₂ : 整数)
  定义体: X'.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂
-/
noncomputable abbrev mapFourδ₁Toδ₀' (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/--
Definition of `mapFourδ₄Toδ₃'` / `mapFourδ₄Toδ₃'` 的定义

English:
abbreviation mapFourδ₄Toδ₃'
  signature: (n₀ n₁ n₂ : Int)
  body: X'.map _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

@[reassoc]

中文:
缩写 mapFourδ₄Toδ₃'
  签名: (n₀ n₁ n₂ : 整数)
  定义体: X'.map _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

@[reassoc]
-/
noncomputable abbrev mapFourδ₄Toδ₃' (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

@[reassoc]
/--
lemma `mapFourδ₁Toδ₀'_comp` / 引理 `mapFourδ₁Toδ₀'_comp`

English:
lemma mapFourδ₁Toδ₀'_comp
  statement: (n₀ n₁ n₂ : Int)
  proof: (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]

中文:
引理 mapFourδ₁Toδ₀'_comp
  结论: (n₀ n₁ n₂ : 整数)
  证明: (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]
-/
lemma mapFourδ₁Toδ₀'_comp (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₃ i₄ i₅ hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₁Toδ₀' i₀ i₂ i₃ i₄ i₅ (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]
/--
lemma `mapFourδ₄Toδ₃'_comp` / 引理 `mapFourδ₄Toδ₃'_comp`

English:
lemma mapFourδ₄Toδ₃'_comp
  statement: (n₀ n₁ n₂ : Int)
  proof: (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]

中文:
引理 mapFourδ₄Toδ₃'_comp
  结论: (n₀ n₁ n₂ : 整数)
  证明: (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]
-/
lemma mapFourδ₄Toδ₃'_comp (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₄ i₅ hi₀₁ hi₁₂ (hi₂₃.trans hi₃₄) hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₅ hi₀₁ hi₁₂ hi₂₃ (hi₃₄.trans hi₄₅) n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

@[reassoc]
/--
lemma `mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'` / 引理 `mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'`

English:
lemma mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
  statement: (n₀ n₁ n₂ : Int)
  proof: by
  rw [← map_comp ..]; rw [← map_comp ..]
  rfl

中文:
引理 mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
  结论: (n₀ n₁ n₂ : 整数)
  证明: by
  rw [← map_comp ..]; rw [← map_comp ..]
  rfl
-/
lemma mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₄Toδ₃' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₄Toδ₃' i₀ i₂ i₃ i₄ i₅ _ _ _ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₅ hi₀₁ _ _ _ n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← map_comp ..]; rw [← map_comp ..]
  rfl

section

variable (n₀ n₁ n₂ : Int) (h : IsZero ((X'.H n₂).obj (mk₁ (homOfLE hi₀₁))))

include h in
/--
lemma `isIso_mapFourδ₁Toδ₀'` / 引理 `isIso_mapFourδ₁Toδ₀'`

English:
lemma isIso_mapFourδ₁Toδ₀'
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: X'.isIso_map_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h

中文:
引理 isIso_mapFourδ₁Toδ₀'
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: X'.isIso_map_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h
-/
lemma isIso_mapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h

/-- For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ≅ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`
when `H^{n₁ + 1}(i₀ ≤ i₁)` is a zero object. -/
@[simps! hom]
/--
Definition of `isoMapFourδ₁Toδ₀'` / `isoMapFourδ₁Toδ₀'` 的定义

English:
definition isoMapFourδ₁Toδ₀'
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: have := X'.isIso_mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]

中文:
定义 isoMapFourδ₁Toδ₀'
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: have := X'.isIso_mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]

Depends on / 依赖: homOfLE
-/
noncomputable def isoMapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]
/--
lemma `isoMapFourδ₁Toδ₀'_hom_inv_id` / 引理 `isoMapFourδ₁Toδ₀'_hom_inv_id`

English:
lemma isoMapFourδ₁Toδ₀'_hom_inv_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoMapFourδ₁Toδ₀'_hom_inv_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
-/
lemma isoMapFourδ₁Toδ₀'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoMapFourδ₁Toδ₀'_inv_hom_id` / 引理 `isoMapFourδ₁Toδ₀'_inv_hom_id`

English:
lemma isoMapFourδ₁Toδ₀'_inv_hom_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

中文:
引理 isoMapFourδ₁Toδ₀'_inv_hom_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id
-/
lemma isoMapFourδ₁Toδ₀'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (n₀ n₁ n₂ : Int) (h : IsZero ((X'.H n₀).obj (mk₁ (homOfLE hi₃₄))))

include h in
/--
lemma `isIso_mapFourδ₄Toδ₃'` / 引理 `isIso_mapFourδ₄Toδ₃'`

English:
lemma isIso_mapFourδ₄Toδ₃'
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: X'.isIso_map_fourδ₄Toδ₃_of_isZero (h := h) ..

中文:
引理 isIso_mapFourδ₄Toδ₃'
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: X'.isIso_map_fourδ₄Toδ₃_of_isZero (h := h) ..
-/
lemma isIso_mapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₄Toδ₃_of_isZero (h := h) ..

/-- For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ≅ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`
when `H^{n₁-1}(i₃ ≤ i₄)` is a zero object. -/
@[simps! hom]
/--
Definition of `isoMapFourδ₄Toδ₃'` / `isoMapFourδ₄Toδ₃'` 的定义

English:
definition isoMapFourδ₄Toδ₃'
  signature: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  body: have := X'.isIso_mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]

中文:
定义 isoMapFourδ₄Toδ₃'
  签名: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  定义体: have := X'.isIso_mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]

Depends on / 依赖: homOfLE
-/
noncomputable def isoMapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]
/--
lemma `isoMapFourδ₄Toδ₄'_hom_inv_id` / 引理 `isoMapFourδ₄Toδ₄'_hom_inv_id`

English:
lemma isoMapFourδ₄Toδ₄'_hom_inv_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoMapFourδ₄Toδ₄'_hom_inv_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id
-/
lemma isoMapFourδ₄Toδ₄'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoMapFourδ₄Toδ₄'_inv_hom_id` / 引理 `isoMapFourδ₄Toδ₄'_inv_hom_id`

English:
lemma isoMapFourδ₄Toδ₄'_inv_hom_id
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

中文:
引理 isoMapFourδ₄Toδ₄'_inv_hom_id
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id
-/
lemma isoMapFourδ₄Toδ₄'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ <= i₁)
  (hi₁₂ : i₁ <= i₂) (hi₂₃ : i₂ <= i₃) (hi₃₄ : i₃ <= i₄) (hi₄₅ : i₄ <= i₅)

/--
Definition of `mapFourδ₂Toδ₁'` / `mapFourδ₂Toδ₁'` 的定义

English:
abbreviation mapFourδ₂Toδ₁'
  signature: (n₀ n₁ n₂ : Int)
  body: X'.map _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

中文:
缩写 mapFourδ₂Toδ₁'
  签名: (n₀ n₁ n₂ : 整数)
  定义体: X'.map _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂
-/
noncomputable abbrev mapFourδ₂Toδ₁' (n₀ n₁ n₂ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/--
lemma `isIso_mapFourδ₂Toδ₁'` / 引理 `isIso_mapFourδ₂Toδ₁'`

English:
lemma isIso_mapFourδ₂Toδ₁'
  statement: (n₀ n₁ n₂ : Int)
  proof: X'.isIso_map _ _ _ _ _ _ _ _ _ _
    (by exact (inferInstanceAs (IsIso ((X'.H n₀).map (𝟙 _))))) h₁ h₂

中文:
引理 isIso_mapFourδ₂Toδ₁'
  结论: (n₀ n₁ n₂ : 整数)
  证明: X'.isIso_map _ _ _ _ _ _ _ _ _ _
    (by exact (inferInstanceAs (IsIso ((X'.H n₀).map (𝟙 _))))) h₁ h₂

Depends on / 依赖: isIso_map
-/
lemma isIso_mapFourδ₂Toδ₁' (n₀ n₁ n₂ : Int)
    (h₁ : IsIso ((X'.H n₁).map (twoδ₁Toδ₀' i₁ i₂ i₃ hi₁₂ hi₂₃)))
    (h₂ : IsIso ((X'.H n₂).map (twoδ₂Toδ₁' i₀ i₁ i₂ hi₀₁ hi₁₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map _ _ _ _ _ _ _ _ _ _
    (by exact (inferInstanceAs (IsIso ((X'.H n₀).map (𝟙 _))))) h₁ h₂

end

end

end SpectralObject

end Abelian

end CategoryTheory
