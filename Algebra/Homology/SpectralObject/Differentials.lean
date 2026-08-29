/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Page

/-!
# Differentials of a spectral object

Let `X` be a spectral object in an abelian category `C` indexed by a category `ι`.
In this file, we construct the differentials `d : E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)`
that are attached to families of five composable morphisms `f₁`, `f₂`, `f₃`, `f₄`, `f₅`
in `ι`. We show that `d ≫ d = 0`. The homology of these differentials is computed in the
file `Mathlib/Algebra/Homology/SpectralObject/Homology.lean`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

open Category ComposableArrows Limits Preadditive

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅)
  (n₀ n₁ n₂ n₃ : Int)

/--
Definition of `d` / `d` 的定义

English:
definition d
  body: X.descE f₃ f₄ f₅ _ rfl n₀ n₁ n₂ (X.δ (f₁ ≫ f₂) (f₃ ≫ f₄) n₁ n₂ hn₂ ≫
    X.toCycles f₁ f₂ _ rfl n₂ ≫ X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃) (by
      rw [X.δ_naturality_assoc (f₁ ≫ f₂) f₃ (f₁ ≫ f₂) (f₃ ≫ f₄)
        (𝟙 _) (twoδ₂Toδ₁ f₃ f₄ _ rfl) n₁ n₂ rfl hn₂]; rw [Functor.map_id]; rw [id_comp]; rw [δ_toCycles_assoc ..]; rw [δToCycles_πE ..]) hn₁
          (by rw [δ_δ_assoc .., zero_comp])

@[reassoc]

中文:
定义 d
  定义体: X.descE f₃ f₄ f₅ _ rfl n₀ n₁ n₂ (X.δ (f₁ ≫ f₂) (f₃ ≫ f₄) n₁ n₂ hn₂ ≫
    X.toCycles f₁ f₂ _ rfl n₂ ≫ X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃) (by
      rw [X.δ_naturality_assoc (f₁ ≫ f₂) f₃ (f₁ ≫ f₂) (f₃ ≫ f₄)
        (𝟙 _) (twoδ₂Toδ₁ f₃ f₄ _ rfl) n₁ n₂ rfl hn₂]; rw [Functor.map_id]; rw [id_comp]; rw [δ_toCycles_assoc ..]; rw [δToCycles_πE ..]) hn₁
          (by rw [δ_δ_assoc .., zero_comp])

@[reassoc]

Depends on / 依赖: Functor, Functor.map_id, X.descE, X.toCycles, id_comp, map_id, toCycles, zero_comp
-/
noncomputable def d
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.E f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.E f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ :=
  X.descE f₃ f₄ f₅ _ rfl n₀ n₁ n₂ (X.δ (f₁ ≫ f₂) (f₃ ≫ f₄) n₁ n₂ hn₂ ≫
    X.toCycles f₁ f₂ _ rfl n₂ ≫ X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃) (by
      rw [X.δ_naturality_assoc (f₁ ≫ f₂) f₃ (f₁ ≫ f₂) (f₃ ≫ f₄)
        (𝟙 _) (twoδ₂Toδ₁ f₃ f₄ _ rfl) n₁ n₂ rfl hn₂]; rw [Functor.map_id]; rw [id_comp]; rw [δ_toCycles_assoc ..]; rw [δToCycles_πE ..]) hn₁
          (by rw [δ_δ_assoc .., zero_comp])

@[reassoc]
/--
lemma `toCycles_πE_d` / 引理 `toCycles_πE_d`

English:
lemma toCycles_πE_d
  proof: by
  subst h₁₂ h₃₄
  simp only [d, δ_toCycles_assoc, toCycles_πE_descE]

中文:
引理 toCycles_πE_d
  证明: by
  subst h₁₂ h₃₄
  simp only [d, δ_toCycles_assoc, toCycles_πE_descE]

Depends on / 依赖: X.toCycles, toCycles
-/
lemma toCycles_πE_d
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.toCycles f₃ f₄ f₃₄ h₃₄ n₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
        X.δ f₁₂ f₃₄ n₁ n₂ hn₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₂ ≫
          X.πE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  subst h₁₂ h₃₄
  simp only [d, δ_toCycles_assoc, toCycles_πE_descE]

set_option backward.defeqAttrib.useBackward true in
include h₃₄ in
@[reassoc]
/--
lemma `d_ιE_fromOpcycles` / 引理 `d_ιE_fromOpcycles`

English:
lemma d_ιE_fromOpcycles
  proof: by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁)]; rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_ιE_assoc ..]; rw [p_fromOpcycles]; rw [toCycles_i_assoc]; rw [fromOpcyles_δ ..]; rw [πE_ιE_assoc ..]; rw [pOpcycles_δFromOpcycles]; rw [toCycles_i_assoc]; rw [← Functor.map_comp]; rw [Eq.comm]
  apply δ_naturality
  simp

中文:
引理 d_ιE_fromOpcycles
  证明: by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁)]; rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_ιE_assoc ..]; rw [p_fromOpcycles]; rw [toCycles_i_assoc]; rw [fromOpcyles_δ ..]; rw [πE_ιE_assoc ..]; rw [pOpcycles_δFromOpcycles]; rw [toCycles_i_assoc]; rw [← Functor.map_comp]; rw [Eq.comm]
  apply δ_naturality
  simp

Depends on / 依赖: X.fromOpcycles, X.toCycles, X.toCycles_, cancel_epi, fromOpcycles, p_fromOpcycles, toCycles
-/
lemma d_ιE_fromOpcycles
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫ X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂ =
      X.ιE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₄ f₅ f₄₅ h₄₅ n₁ ≫
        X.δ f₂₃ f₄₅ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁)]; rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_ιE_assoc ..]; rw [p_fromOpcycles]; rw [toCycles_i_assoc]; rw [fromOpcyles_δ ..]; rw [πE_ιE_assoc ..]; rw [pOpcycles_δFromOpcycles]; rw [toCycles_i_assoc]; rw [← Functor.map_comp]; rw [Eq.comm]
  apply δ_naturality
  simp

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (n₀ n₁ n₂ n₃ n₄ : Int)

@[reassoc (attr := simp)]
/--
lemma `d_d` / 引理 `d_d`

English:
lemma d_d
  statement: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  rw [← cancel_epi (X.πE f₅ f₆ f₇ n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles f₅ f₆ _ rfl n₁)]; rw [comp_zero]; rw [comp_zero]; rw [X.toCycles_πE_d_assoc f₃ f₄ f₅ f₆ f₇ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [X.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄]; rw [δ_δ_assoc ..]; rw [zero_comp]

中文:
引理 d_d
  结论: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  rw [← cancel_epi (X.πE f₅ f₆ f₇ n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles f₅ f₆ _ rfl n₁)]; rw [comp_zero]; rw [comp_zero]; rw [X.toCycles_πE_d_assoc f₃ f₄ f₅ f₆ f₇ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [X.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄]; rw [δ_δ_assoc ..]; rw [zero_comp]

Depends on / 依赖: X.toCycles, X.toCycles_, cancel_epi, comp_zero, toCycles
-/
lemma d_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    X.d f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ = 0 := by
  rw [← cancel_epi (X.πE f₅ f₆ f₇ n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles f₅ f₆ _ rfl n₁)]; rw [comp_zero]; rw [comp_zero]; rw [X.toCycles_πE_d_assoc f₃ f₄ f₅ f₆ f₇ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [X.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄]; rw [δ_δ_assoc ..]; rw [zero_comp]

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : Int)

/--
Definition of `Ψ` / `Ψ` 的定义

English:
definition Ψ
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: X.descCycles f₂ f₃ _ rfl
    (X.δ f₁ (f₂ ≫ f₃) n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁) (by
      rw [X.δ_naturality_assoc f₁ f₂ f₁ (f₂ ≫ f₃) (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ _ rfl) _ _ rfl]; rw [Functor.map_id]; rw [id_comp]; rw [δ_pOpcycles ..])

@[reassoc (attr := simp)]

中文:
定义 Ψ
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: X.descCycles f₂ f₃ _ rfl
    (X.δ f₁ (f₂ ≫ f₃) n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁) (by
      rw [X.δ_naturality_assoc f₁ f₂ f₁ (f₂ ≫ f₃) (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ _ rfl) _ _ rfl]; rw [Functor.map_id]; rw [id_comp]; rw [δ_pOpcycles ..])

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_id, X.cycles, X.descCycles, X.opcycles, X.pOpcycles, cycles, descCycles, id_comp, map_id, opcycles, pOpcycles
-/
noncomputable def Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cycles f₂ f₃ n₀ ⟶ X.opcycles f₁ f₂ n₁ :=
  X.descCycles f₂ f₃ _ rfl
    (X.δ f₁ (f₂ ≫ f₃) n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁) (by
      rw [X.δ_naturality_assoc f₁ f₂ f₁ (f₂ ≫ f₃) (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ _ rfl) _ _ rfl]; rw [Functor.map_id]; rw [id_comp]; rw [δ_pOpcycles ..])

@[reassoc (attr := simp)]
/--
lemma `toCycles_Ψ` / 引理 `toCycles_Ψ`

English:
lemma toCycles_Ψ
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  subst h₂₃
  simp only [Ψ, toCycles_descCycles]

@[reassoc (attr := simp)]

中文:
引理 toCycles_Ψ
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  subst h₂₃
  simp only [Ψ, toCycles_descCycles]

@[reassoc (attr := simp)]

Depends on / 依赖: X.pOpcycles, X.toCycles, pOpcycles, toCycles, toCycles_descCycles
-/
lemma toCycles_Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂₃ n₀ n₁ hn₁ ≫ X.pOpcycles f₁ f₂ n₁ := by
  subst h₂₃
  simp only [Ψ, toCycles_descCycles]

@[reassoc (attr := simp)]
/--
lemma `Ψ_fromOpcycles` / 引理 `Ψ_fromOpcycles`

English:
lemma Ψ_fromOpcycles
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_epi (X.toCycles f₂ f₃ _ rfl n₀)]; rw [toCycles_Ψ_assoc ..]; rw [p_fromOpcycles]; rw [toCycles_i_assoc]
  exact (X.δ_naturality _ _ _ _ _ _ _ _ rfl).symm

include h₂₃ in
@[reassoc (attr := simp)]

中文:
引理 Ψ_fromOpcycles
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_epi (X.toCycles f₂ f₃ _ rfl n₀)]; rw [toCycles_Ψ_assoc ..]; rw [p_fromOpcycles]; rw [toCycles_i_assoc]
  exact (X.δ_naturality _ _ _ _ _ _ _ _ rfl).symm

include h₂₃ in
@[reassoc (attr := simp)]

Depends on / 依赖: X.fromOpcycles, X.iCycles, X.toCycles, cancel_epi, fromOpcycles, iCycles, p_fromOpcycles, toCycles, toCycles_i_assoc
-/
lemma Ψ_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.iCycles f₂ f₃ n₀ ≫ X.δ f₁₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_epi (X.toCycles f₂ f₃ _ rfl n₀)]; rw [toCycles_Ψ_assoc ..]; rw [p_fromOpcycles]; rw [toCycles_i_assoc]
  exact (X.δ_naturality _ _ _ _ _ _ _ _ rfl).symm

include h₂₃ in
@[reassoc (attr := simp)]
/--
lemma `cyclesMap_Ψ` / 引理 `cyclesMap_Ψ`

English:
lemma cyclesMap_Ψ
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_epi (X.toCycles f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) n₀), comp_zero,
    X.toCycles_cyclesMap_assoc f₁₂ f₃ f₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) f₂₃ h₂₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂)
    (twoδ₁Toδ₀ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])) n₀ rfl rfl,
    toCycles_Ψ .., zero₃_assoc .., zero_comp]

include h₁₂ in

中文:
引理 cyclesMap_Ψ
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_epi (X.toCycles f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) n₀), comp_zero,
    X.toCycles_cyclesMap_assoc f₁₂ f₃ f₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) f₂₃ h₂₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂)
    (twoδ₁Toδ₀ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])) n₀ rfl rfl,
    toCycles_Ψ .., zero₃_assoc .., zero_comp]

include h₁₂ in

Depends on / 依赖: X.cyclesMap, X.toCycles, X.toCycles_cyclesMap_assoc, cancel_epi, comp_zero, cyclesMap, reassoc_of, toCycles, toCycles_cyclesMap_assoc, zero_comp
-/
lemma cyclesMap_Ψ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀ ≫
      X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ = 0 := by
  rw [← cancel_epi (X.toCycles f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) n₀), comp_zero,
    X.toCycles_cyclesMap_assoc f₁₂ f₃ f₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) f₂₃ h₂₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂)
    (twoδ₁Toδ₀ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])) n₀ rfl rfl,
    toCycles_Ψ .., zero₃_assoc .., zero_comp]

include h₁₂ in
/--
lemma `Ψ_opcyclesMap` / 引理 `Ψ_opcyclesMap`

English:
lemma Ψ_opcyclesMap
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) n₁),
    zero_comp, assoc, X.opcyclesMap_fromOpcycles f₁ f₂ f₁ f₂₃ f₁₂ h₁₂
    (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃)
    (twoδ₂Toδ₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃) (by rw [reassoc_of% h₁₂])) n₁ rfl rfl,
    Ψ_fromOpcycles_assoc .., zero₁ .., comp_zero]

中文:
引理 Ψ_opcyclesMap
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) n₁),
    zero_comp, assoc, X.opcyclesMap_fromOpcycles f₁ f₂ f₁ f₂₃ f₁₂ h₁₂
    (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃)
    (twoδ₂Toδ₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃) (by rw [reassoc_of% h₁₂])) n₁ rfl rfl,
    Ψ_fromOpcycles_assoc .., zero₁ .., comp_zero]

Depends on / 依赖: X.fromOpcycles, X.opcyclesMap, X.opcyclesMap_fromOpcycles, cancel_mono, comp_zero, fromOpcycles, opcyclesMap, opcyclesMap_fromOpcycles, reassoc_of, zero_comp
-/
lemma Ψ_opcyclesMap (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫
      X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ = 0 := by
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) n₁),
    zero_comp, assoc, X.opcyclesMap_fromOpcycles f₁ f₂ f₁ f₂₃ f₁₂ h₁₂
    (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃)
    (twoδ₂Toδ₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃) (by rw [reassoc_of% h₁₂])) n₁ rfl rfl,
    Ψ_fromOpcycles_assoc .., zero₁ .., comp_zero]

/--
Definition of `sequenceΨ` / `sequenceΨ` 的定义

English:
definition sequenceΨ
  signature: (hn₁ : n₀ + 1 = n₁ := by lia)
  body: mk₃ (X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀)
    (X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁)
    (X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁)

中文:
定义 sequenceΨ
  签名: (hn₁ : n₀ + 1 = n₁ := by lia)
  定义体: mk₃ (X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀)
    (X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁)
    (X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁)

Depends on / 依赖: ComposableArrows, X.cyclesMap, X.opcyclesMap, cyclesMap, opcyclesMap
-/
noncomputable def sequenceΨ (hn₁ : n₀ + 1 = n₁ := by lia) :
    ComposableArrows C 3 :=
  mk₃ (X.cyclesMap _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₀)
    (X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁)
    (X.opcyclesMap _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁)

/--
lemma `cyclesMap_Ψ_exact` / 引理 `cyclesMap_Ψ_exact`

English:
lemma cyclesMap_Ψ_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles f₁₂ f₃ n₀ n₁ hn₁ (z ≫ X.iCycles f₂ f₃ n₀) ?_, ?_⟩ <;> dsimp
  · rw [assoc, ← X.Ψ_fromOpcycles f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ hn₁, reassoc_of% hz, zero_comp]
  · rw [← cancel_mono (X.iCycles f₂ f₃ n₀), id_comp, assoc,
      X.cyclesMap_i _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) n₀ (by cat_disch),
      Functor.map_id, comp_id, liftCycles_i]

中文:
引理 cyclesMap_Ψ_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles f₁₂ f₃ n₀ n₁ hn₁ (z ≫ X.iCycles f₂ f₃ n₀) ?_, ?_⟩ <;> dsimp
  · rw [assoc, ← X.Ψ_fromOpcycles f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ hn₁, reassoc_of% hz, zero_comp]
  · rw [← cancel_mono (X.iCycles f₂ f₃ n₀), id_comp, assoc,
      X.cyclesMap_i _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) n₀ (by cat_disch),
      Functor.map_id, comp_id, liftCycles_i]

Depends on / 依赖: Functor, Functor.map_i, ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, ShortComplex.mk, X.cyclesMap_, X.cyclesMap_i, X.iCycles, X.liftCycles, cancel_mono, cat_disch, cyclesMap_i, exact_iff_exact_up_to_refinements, iCycles, id_comp, liftCycles, map_i, reassoc_of, zero_comp
-/
lemma cyclesMap_Ψ_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (X.cyclesMap_Ψ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles f₁₂ f₃ n₀ n₁ hn₁ (z ≫ X.iCycles f₂ f₃ n₀) ?_, ?_⟩ <;> dsimp
  · rw [assoc, ← X.Ψ_fromOpcycles f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ hn₁, reassoc_of% hz, zero_comp]
  · rw [← cancel_mono (X.iCycles f₂ f₃ n₀), id_comp, assoc,
      X.cyclesMap_i _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) n₀ (by cat_disch),
      Functor.map_id, comp_id, liftCycles_i]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Ψ_opcyclesMap_exact` / 引理 `Ψ_opcyclesMap_exact`

English:
lemma Ψ_opcyclesMap_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro _ z₀ hz₀
  obtain ⟨A₁, π₁, _, z₁, hz₁⟩ := surjective_up_to_refinements_of_epi (X.pOpcycles f₁ f₂ n₁) z₀
  obtain ⟨A₂, π₂, _, z₂, hz₂⟩ :=
      (X.cokernelSequenceOpcycles_exact f₁ f₂₃ n₀ n₁ hn₁).exact_up_to_refinements z₁ (by
    dsimp
    have H := X.p_opcyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) n₁ (by cat_disch)
    rw [Functor.map_id]; rw [id_comp] at H
    rw [← H]; rw [← reassoc_of% hz₁]; rw [hz₀]; rw [comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z₂ ≫ X.toCycles f₂ f₃ f₂₃ h₂₃ n₀, ?_⟩
  rw [← cancel_mono (X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [toCycles_Ψ_assoc ..]; rw [p_fromOpcycles]; rw [← reassoc_of% dsimp% hz₂]; rw [reassoc_of% hz₁]; rw [p_fromOpcycles]

中文:
引理 Ψ_opcyclesMap_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro _ z₀ hz₀
  obtain ⟨A₁, π₁, _, z₁, hz₁⟩ := surjective_up_to_refinements_of_epi (X.pOpcycles f₁ f₂ n₁) z₀
  obtain ⟨A₂, π₂, _, z₂, hz₂⟩ :=
      (X.cokernelSequenceOpcycles_exact f₁ f₂₃ n₀ n₁ hn₁).exact_up_to_refinements z₁ (by
    dsimp
    have H := X.p_opcyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) n₁ (by cat_disch)
    rw [Functor.map_id]; rw [id_comp] at H
    rw [← H]; rw [← reassoc_of% hz₁]; rw [hz₀]; rw [comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z₂ ≫ X.toCycles f₂ f₃ f₂₃ h₂₃ n₀, ?_⟩
  rw [← cancel_mono (X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [toCycles_Ψ_assoc ..]; rw [p_fromOpcycles]; rw [← reassoc_of% dsimp% hz₂]; rw [reassoc_of% hz₁]; rw [p_fromOpcycles]

Depends on / 依赖: Functor, Functor.map_id, ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, ShortComplex.mk, X.cokernelSequenceOpcycles_exact, X.pOpcycles, X.p_opcyclesMap, cat_disch, cokernelSequenceOpcycles_exact, exact_iff_exact_up_to_refinements, exact_up_to_refinements, id_c, map_id, pOpcycles, p_opcyclesMap, surjective_up_to_refinements_of_epi
-/
lemma Ψ_opcyclesMap_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (X.Ψ_opcyclesMap f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro _ z₀ hz₀
  obtain ⟨A₁, π₁, _, z₁, hz₁⟩ := surjective_up_to_refinements_of_epi (X.pOpcycles f₁ f₂ n₁) z₀
  obtain ⟨A₂, π₂, _, z₂, hz₂⟩ :=
      (X.cokernelSequenceOpcycles_exact f₁ f₂₃ n₀ n₁ hn₁).exact_up_to_refinements z₁ (by
    dsimp
    have H := X.p_opcyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) n₁ (by cat_disch)
    rw [Functor.map_id]; rw [id_comp] at H
    rw [← H]; rw [← reassoc_of% hz₁]; rw [hz₀]; rw [comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z₂ ≫ X.toCycles f₂ f₃ f₂₃ h₂₃ n₀, ?_⟩
  rw [← cancel_mono (X.fromOpcycles f₁ f₂ f₁₂ h₁₂ n₁)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [toCycles_Ψ_assoc ..]; rw [p_fromOpcycles]; rw [← reassoc_of% dsimp% hz₂]; rw [reassoc_of% hz₁]; rw [p_fromOpcycles]

/--
lemma `sequenceΨ_exact` / 引理 `sequenceΨ_exact`

English:
lemma sequenceΨ_exact
  given: (hn₁ : n₀ + 1 = n₁ := by lia)
  proof: exact_of_δ₀ (X.cyclesMap_Ψ_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows
    (X.Ψ_opcyclesMap_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows

中文:
引理 sequenceΨ_exact
  条件: (hn₁ : n₀ + 1 = n₁ := by lia)
  证明: exact_of_δ₀ (X.cyclesMap_Ψ_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows
    (X.Ψ_opcyclesMap_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows

Depends on / 依赖: X.cyclesMap_, X.sequence, exact_toComposableArrows
-/
lemma sequenceΨ_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sequenceΨ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).Exact :=
  exact_of_δ₀ (X.cyclesMap_Ψ_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows
    (X.Ψ_opcyclesMap_exact f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ n₀ n₁ hn₁).exact_toComposableArrows

end

@[reassoc (attr := simp)]
/--
lemma `πE_d_ιE` / 引理 `πE_d_ιE`

English:
lemma πE_d_ιE
  proof: by
  rw [← cancel_epi (X.toCycles f₃ f₄ _ rfl n₁)]; rw [toCycles_Ψ ..]; rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_ιE ..]; rw [toCycles_i_assoc]; rw [← X.δ_naturality_assoc (f₁ ≫ f₂) (f₃ ≫ f₄) f₂ (f₃ ≫ f₄)
      (twoδ₁Toδ₀ f₁ f₂ _ rfl) (𝟙 _) n₁ n₂ rfl hn₂]; rw [Functor.map_id]; rw [id_comp]

中文:
引理 πE_d_ιE
  证明: by
  rw [← cancel_epi (X.toCycles f₃ f₄ _ rfl n₁)]; rw [toCycles_Ψ ..]; rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_ιE ..]; rw [toCycles_i_assoc]; rw [← X.δ_naturality_assoc (f₁ ≫ f₂) (f₃ ≫ f₄) f₂ (f₃ ≫ f₄)
      (twoδ₁Toδ₀ f₁ f₂ _ rfl) (𝟙 _) n₁ n₂ rfl hn₂]; rw [Functor.map_id]; rw [id_comp]

Depends on / 依赖: X.toCycles, X.toCycles_, cancel_epi, isNoetherian_submodule, toCycles, toCycles_i_assoc
-/
lemma πE_d_ιE
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (n₀ n₁ n₂ n₃ : Int)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ = X.Ψ f₂ f₃ f₄ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.toCycles f₃ f₄ _ rfl n₁)]; rw [toCycles_Ψ ..]; rw [X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_ιE ..]; rw [toCycles_i_assoc]; rw [← X.δ_naturality_assoc (f₁ ≫ f₂) (f₃ ≫ f₄) f₂ (f₃ ≫ f₄)
      (twoδ₁Toδ₀ f₁ f₂ _ rfl) (𝟙 _) n₁ n₂ rfl hn₂]; rw [Functor.map_id]; rw [id_comp]

section

variable {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
  (n₀ n₁ n₂ n₃ : Int)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `πE_EIsoH_hom` / 引理 `πE_EIsoH_hom`

English:
lemma πE_EIsoH_hom
  given: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [πE, cyclesIsoH, EIsoH]

@[reassoc]

中文:
引理 πE_EIsoH_hom
  条件: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [πE, cyclesIsoH, EIsoH]

@[reassoc]

Depends on / 依赖: X.EIsoH, X.cyclesIsoH, cyclesIsoH, isArtinian_submodule
-/
lemma πE_EIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE (𝟙 i₀) f₁ (𝟙 i₁) n₀ n₁ n₂ hn₁ hn₂ ≫ (X.EIsoH f₁ n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.cyclesIsoH f₁ n₁ n₂ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [πE, cyclesIsoH, EIsoH]

@[reassoc]
/--
lemma `d_EIsoH_hom` / 引理 `d_EIsoH_hom`

English:
lemma d_EIsoH_hom
  statement: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  proof: by
  rw [← cancel_epi (X.πE (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles (𝟙 i₁) f₂ f₂ (by simp) n₁)]; rw [X.toCycles_πE_d_assoc (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) f₁ (by simp) _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_EIsoH_hom ..]; rw [πE_EIsoH_hom_assoc ..]; rw [cyclesIsoH_inv_hom_id ..]; rw [comp_id]; rw [cyclesIsoH_inv_hom_id_assoc ..]

中文:
引理 d_EIsoH_hom
  结论: (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
  证明: by
  rw [← cancel_epi (X.πE (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles (𝟙 i₁) f₂ f₂ (by simp) n₁)]; rw [X.toCycles_πE_d_assoc (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) f₁ (by simp) _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_EIsoH_hom ..]; rw [πE_EIsoH_hom_assoc ..]; rw [cyclesIsoH_inv_hom_id ..]; rw [comp_id]; rw [cyclesIsoH_inv_hom_id_assoc ..]

Depends on / 依赖: X.EIsoH, X.toCycles, X.toCycles_, cancel_epi, cyclesI, toCycles
-/
lemma d_EIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      (X.EIsoH f₁ n₁ n₂ n₃ hn₂ hn₃).hom =
    (X.EIsoH f₂ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.δ f₁ f₂ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.πE (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ hn₁ hn₂)]; rw [← cancel_epi (X.toCycles (𝟙 i₁) f₂ f₂ (by simp) n₁)]; rw [X.toCycles_πE_d_assoc (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) f₁ (by simp) _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]; rw [πE_EIsoH_hom ..]; rw [πE_EIsoH_hom_assoc ..]; rw [cyclesIsoH_inv_hom_id ..]; rw [comp_id]; rw [cyclesIsoH_inv_hom_id_assoc ..]

end

end SpectralObject

end Abelian

end CategoryTheory
