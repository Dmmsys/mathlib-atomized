/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism

/-!
# Simplicial homotopies

In this file, we define the notion of homotopy (`SSet.Homotopy`) between
morphisms `f : X ⟶ Y` and `g : X ⟶ Y` of simplicial sets: it involves
a morphism `X ⊗ Δ[1] ⟶ Y` inducing both `f` and `g`. (This definition is
a particular case of `SSet.RelativeMorphism.Homotopy` that is defined in
the file `Mathlib/AlgebraicTopology/SimplicialSet/RelativeMorphism.lean`).
We show that from `H : SSet.Homotopy f g`, we can obtain a combinatorial
homotopy `SimplicialObject.Homotopy f g` (where the data involve
a family of maps `X _⦋n⦌ → Y _⦋n + 1⦌` for all `n : ℕ` and `i : Fin (n + 1)`.)

-/

@[expose] public section

open CategoryTheory SimplicialObject MonoidalCategory Simplicial Opposite

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- Morphisms relatively to the `⊥` subcomplexes of `X` and `Y`
identify to morphisms `X ⟶ Y`. -/
@[simps]
/--
Definition of `RelativeMorphism.botEquiv` / `RelativeMorphism.botEquiv` 的定义

English:
definition RelativeMorphism.botEquiv
  signature: :
  body: f.map
  invFun f := { map := f }

中文:
定义 Relative态射.botEquiv
  签名: :
  定义体: f.map
  invFun f := { map := f }

Depends on / 依赖: f.map
-/
def RelativeMorphism.botEquiv :
    RelativeMorphism (⊥ : X.Subcomplex) (⊥ : Y.Subcomplex)
      (Subcomplex.isInitialBot.to _) ≃ (X ⟶ Y) where
  toFun f := f.map
  invFun f := { map := f }

/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
definition Homotopy
  signature: (f g : X ⟶ Y)
  body: (RelativeMorphism.botEquiv.symm f).Homotopy (RelativeMorphism.botEquiv.symm g)

中文:
定义 同伦
  签名: (f g : X ⟶ Y)
  定义体: (RelativeMorphism.botEquiv.symm f).Homotopy (RelativeMorphism.botEquiv.symm g)

Depends on / 依赖: Homotopy, RelativeMorphism, RelativeMorphism.botEquiv.symm, botEquiv
-/
def Homotopy (f g : X ⟶ Y) : Type u :=
  (RelativeMorphism.botEquiv.symm f).Homotopy (RelativeMorphism.botEquiv.symm g)

namespace Homotopy

variable {f g : X ⟶ Y}

@[reassoc (attr := simp high)]
/--
lemma `h₀` / 引理 `h₀`

English:
lemma h₀
  given: (H : Homotopy f g)
  statement: ι₀ ≫ H.h = f
  proof: RelativeMorphism.Homotopy.h₀ H

@[reassoc (attr := simp high)]

中文:
引理 h₀
  条件: (H : 同伦 f g)
  结论: ι₀ ≫ H.h = f
  证明: RelativeMorphism.Homotopy.h₀ H

@[reassoc (attr := simp high)]

Depends on / 依赖: Homotopy, RelativeMorphism, RelativeMorphism.Homotopy.h
-/
lemma h₀ (H : Homotopy f g) : ι₀ ≫ H.h = f :=
  RelativeMorphism.Homotopy.h₀ H

@[reassoc (attr := simp high)]
/--
lemma `h₁` / 引理 `h₁`

English:
lemma h₁
  given: (H : Homotopy f g)
  statement: ι₁ ≫ H.h = g
  proof: RelativeMorphism.Homotopy.h₁ H

中文:
引理 h₁
  条件: (H : 同伦 f g)
  结论: ι₁ ≫ H.h = g
  证明: RelativeMorphism.Homotopy.h₁ H

Depends on / 依赖: Homotopy, RelativeMorphism, RelativeMorphism.Homotopy.h
-/
lemma h₁ (H : Homotopy f g) : ι₁ ≫ H.h = g :=
  RelativeMorphism.Homotopy.h₁ H

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toSimplicialObjectHomotopy` / `toSimplicialObjectHomotopy` 的定义

English:
definition toSimplicialObjectHomotopy
  signature: (H : Homotopy f g)
  body: ↾fun x =>
    (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1
  h_zero_comp_δ_zero n := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply, ← H.h₁]
    dsimp
    apply congr_ar

中文:
定义 toSimplicialObjectHomotopy
  签名: (H : 同伦 f g)
  定义体: ↾fun x =>
    (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1
  h_zero_comp_δ_zero n := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply, ← H.h₁]
    dsimp
    apply congr_ar
-/
noncomputable def toSimplicialObjectHomotopy (H : Homotopy f g) :
    SimplicialObject.Homotopy f g where
  h i := ↾fun x =>
    (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app _ (prodStdSimplex.nonDegenerateEquiv₁ i).1
  h_zero_comp_δ_zero n := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply, ← H.h₁]
    dsimp
    apply congr_arg
    ext k : 2
    · simp [dsimp% SimplexCategory.δ_comp_σ_self (i := (0 : Fin (n + 1)))]
    · rw [stdSimplex.δ_objMk₁_of_lt _ _ (by tauto)]
      rfl
  h_last_comp_δ_last n := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply, ← H.h₀]
    dsimp
    apply congr_arg
    ext k
    · simp [dsimp% SimplexCategory.δ_comp_σ_succ (i := Fin.last n)]
    · simp [stdSimplex.δ_objMk₁_of_le, stdSimplex.objMk₁_apply_eq_zero_iff, ← Fin.castSucc_succ]
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · simpa [stdSimplex.δ_objEquiv_symm_apply,
        SSet.yonedaEquiv_symm_app_objEquiv_symm.{u}] using!
          ConcreteCategory.congr_hom (X.δ_comp_σ_of_le hij) x
    · rw [stdSimplex.δ_objMk₁_of_lt, Fin.pred_succ]
      rw [Fin.castSucc_lt_succ_iff]; rw [← Fin.castSucc_succ]
      simp only [Fin.castSucc_le_castSucc_iff]
      exact hij.trans (j.castSucc_le_succ)
  h_succ_comp_δ_castSucc_succ {n} i := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · rw [stdSimplex.δ_objEquiv_symm_apply, stdSimplex.δ_objEquiv_symm_apply,
        SimplexCategory.δ_comp_σ_succ, ← Fin.castSucc_succ, SimplexCategory.δ_comp_σ_self]
    · rw [stdSimplex.δ_objMk₁_of_lt _ _ (by simp), stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
      rfl
  h_castSucc_comp_δ_succ_of_lt {n} i j hij := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.δ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · simp [SimplexCategory.δ_comp_σ_of_gt hij, SSet.yonedaEquiv_symm_app_objEquiv_symm.{u}]
      rfl
    · rw [stdSimplex.δ_objMk₁_of_le _ _ (by simpa using! Fin.le_of_lt hij)]
      rfl
  h_comp_σ_castSucc_of_le {n} i j hij := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.σ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · simp [SimplexCategory.σ_comp_σ hij, SSet.yonedaEquiv_symm_app_objEquiv_symm.{u}]
      rfl
    · rw [stdSimplex.σ_objMk₁_of_lt _ _ (by simpa)]
  h_comp_σ_succ_of_lt {n} i j hij := by
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      ← SSet.σ_naturality_apply]
    dsimp
    apply congr_arg
    ext k : 2
    · simp [← SimplexCategory.σ_comp_σ hij, SSet.yonedaEquiv_symm_app_objEquiv_symm.{u}]
      rfl
    · rw [stdSimplex.σ_objMk₁_of_le _ _ (by simpa)]
      rfl

end Homotopy

end SSet
