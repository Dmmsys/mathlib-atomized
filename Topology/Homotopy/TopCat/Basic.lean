/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies between morphisms in `TopCat`

In this file, we define the type `TopCat.Homotopy` of homotopies
between two morphisms in the category `TopCat`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

variable {X Y Z : TopCat.{u}}

/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
abbreviation Homotopy
  signature: (f g : X ⟶ Y)
  body: ContinuousMap.Homotopy f.hom g.hom

中文:
缩写 Homotopy
  签名: (f g : X ⟶ Y)
  定义体: ContinuousMap.Homotopy f.hom g.hom

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy, Homotopy, f.hom, g.hom
-/
abbrev Homotopy (f g : X ⟶ Y) := ContinuousMap.Homotopy f.hom g.hom

namespace Homotopy

variable {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)

/--
Definition of `h` / `h` 的定义

English:
definition h
  signature: (H : Homotopy f₀ f₁)
  body: (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))

中文:
定义 h
  签名: (H : Homotopy f₀ f₁)
  定义体: (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))

Depends on / 依赖: ContinuousMap, ContinuousMap.prodMap, H.toContinuousMap.comp, I.homeomorph, homeomorph, prodMap, toContinuousMap
-/
def h (H : Homotopy f₀ f₁) : X otimes I ⟶ Y :=
  (β_ _ _).hom ≫ ofHom (H.toContinuousMap.comp (ContinuousMap.prodMap I.homeomorph (.id _)))

-- simps generates the wrong apply lemma
@[simp]
/--
theorem `h_hom_apply` / 定理 `h_hom_apply`

English:
theorem h_hom_apply
  given: (p : ↑(X otimes I))
  statement: F.h p = F (I.homeomorph p.2, p.1)
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 h_hom_apply
  条件: (p : ↑(X otimes I))
  结论: F.h p = F (I.homeomorph p.2, p.1)
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem h_hom_apply (p : ↑(X otimes I)) : F.h p = F (I.homeomorph p.2, p.1) := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₀_h` / 引理 `ι₀_h`

English:
lemma ι₀_h
  statement: ι₀ ≫ F.h = f₀
  proof: by
  ext x
  exact F.map_zero_left x

@[reassoc (attr := simp)]

中文:
引理 ι₀_h
  结论: ι₀ ≫ F.h = f₀
  证明: by
  ext x
  exact F.map_zero_left x

@[reassoc (attr := simp)]

Depends on / 依赖: F.map_zero_left, map_zero_left
-/
lemma ι₀_h : ι₀ ≫ F.h = f₀ := by
  ext x
  exact F.map_zero_left x

@[reassoc (attr := simp)]
/--
lemma `ι₁_h` / 引理 `ι₁_h`

English:
lemma ι₁_h
  statement: ι₁ ≫ F.h = f₁
  proof: by
  ext x
  exact F.map_one_left x

中文:
引理 ι₁_h
  结论: ι₁ ≫ F.h = f₁
  证明: by
  ext x
  exact F.map_one_left x

Depends on / 依赖: F.map_one_left, map_one_left
-/
lemma ι₁_h : ι₁ ≫ F.h = f₁ := by
  ext x
  exact F.map_one_left x

/--
Definition of `refl` / `refl` 的定义

English:
abbreviation refl
  signature: (f : X ⟶ Y)
  body: ContinuousMap.Homotopy.refl f.hom

@[simp]

中文:
缩写 refl
  签名: (f : X ⟶ Y)
  定义体: ContinuousMap.Homotopy.refl f.hom

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy.refl, Homotopy, f.hom
-/
abbrev refl (f : X ⟶ Y) := ContinuousMap.Homotopy.refl f.hom

@[simp]
/--
lemma `h_refl` / 引理 `h_refl`

English:
lemma h_refl
  statement: h (refl f₀) = fst _ _ ≫ f₀
  proof: rfl

中文:
引理 h_refl
  结论: h (refl f₀) = fst _ _ ≫ f₀
  证明: rfl
-/
lemma h_refl : h (refl f₀) = fst _ _ ≫ f₀ := rfl

/--
Definition of `symm` / `symm` 的定义

English:
abbreviation symm
  body: ContinuousMap.Homotopy.symm F

@[simp]

中文:
缩写 symm
  定义体: ContinuousMap.Homotopy.symm F

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy.symm, Homotopy
-/
abbrev symm := ContinuousMap.Homotopy.symm F

@[simp]
/--
lemma `h_symm` / 引理 `h_symm`

English:
lemma h_symm
  statement: h F.symm = (X ◁ I.symm) ≫ F.h
  proof: rfl

中文:
引理 h_symm
  结论: h F.symm = (X ◁ I.symm) ≫ F.h
  证明: rfl
-/
lemma h_symm : h F.symm = (X ◁ I.symm) ≫ F.h := rfl

/--
Definition of `trans` / `trans` 的定义

English:
abbreviation trans
  body: ContinuousMap.Homotopy.trans F G

中文:
缩写 trans
  定义体: ContinuousMap.Homotopy.trans F G

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy.trans, Homotopy
-/
noncomputable abbrev trans := ContinuousMap.Homotopy.trans F G

/-- The homotopy between compositions of morphisms in `TopCat`. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
abbreviation comp
  signature: {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁)
  body: ContinuousMap.Homotopy.comp G F

中文:
缩写 comp
  签名: {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁)
  定义体: ContinuousMap.Homotopy.comp G F

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy.comp, Homotopy
-/
abbrev comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) := ContinuousMap.Homotopy.comp G F

attribute [nolint simpNF] comp_apply

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `h_comp` / 引理 `h_comp`

English:
lemma h_comp
  given: {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁)
  proof: by
  ext
  simp

中文:
引理 h_comp
  条件: {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁)
  证明: by
  ext
  simp
-/
lemma h_comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    (G.comp F).h = X ◁ lift (𝟙 I) (𝟙 I) ≫ (α_ _ _ _).inv ≫ F.h ▷ _ ≫ G.h := by
  ext
  simp

end Homotopy

end TopCat
