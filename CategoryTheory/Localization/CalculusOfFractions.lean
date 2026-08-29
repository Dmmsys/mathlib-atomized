/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Calculus of fractions

Following the definitions by [Gabriel and Zisman][gabriel-zisman-1967],
given a morphism property `W : MorphismProperty C` on a category `C`,
we introduce the class `W.HasLeftCalculusOfFractions`. The main
result `Localization.exists_leftFraction` is that if `L : C ⥤ D`
is a localization functor for `W`, then for any morphism `L.obj X ⟶ L.obj Y` in `D`,
there exists an auxiliary object `Y' : C` and morphisms `g : X ⟶ Y'` and `s : Y ⟶ Y'`,
with `W s`, such that the given morphism is a sort of fraction `g / s`,
or more precisely of the form `L.map g ≫ (Localization.isoOfHom L W s hs).inv`.
We also show that the functor `L.mapArrow : Arrow C ⥤ Arrow D` is essentially surjective.

Similar results are obtained when `W` has a right calculus of fractions.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

open Category

namespace MorphismProperty

/--
Definition of `LeftFraction` / `LeftFraction` 的定义

English:
structure LeftFraction
  parameters: (W : MorphismProperty C) (X Y : C)
  axioms and operations (4):
    - {Y' : C}
    - f : X ⟶ Y'
    - s : Y ⟶ Y'
    - hs : W s

中文:
结构 LeftFraction
  参数: (W : Morphism命题erty C) (X Y : C)
  公理与运算 (4 个):
    - {Y' : C}
    - f : X ⟶ Y'
    - s : Y ⟶ Y'
    - hs : W s
-/
structure LeftFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a left fraction -/
  {Y' : C}
  /-- the numerator of a left fraction -/
  f : X ⟶ Y'
  /-- the denominator of a left fraction -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

namespace LeftFraction

variable (W : MorphismProperty C) {X Y : C}

/-- The left fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: (f : X ⟶ Y) [W.ContainsIdentities]
  body: mk f (𝟙 Y) (W.id_mem Y)

中文:
定义 ofHom
  签名: (f : X ⟶ Y) [W.ContainsIdentities]
  定义体: mk f (𝟙 Y) (W.id_mem Y)

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, CategoryTheory, CategoryTheory.isCardinalPresentable_iff, Fact.out, IsCardinalLocallyPresentable, IsCardinalLocallyPresentable.iff_exists_isStrongGenerator, IsRegular, ObjectProperty, ObjectProperty.singleton_le_iff, W.id_mem, aleph0_le, hasCardinalLT_of_finite, id_mem, iff_exists_isStrongGenerator, isCardinalPresentable_iff, isStrongGenerator_punit, singleton, singleton_le_iff
-/
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    W.LeftFraction X Y := mk f (𝟙 Y) (W.id_mem Y)

variable {W}

/-- The left fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
/--
Definition of `ofInv` / `ofInv` 的定义

English:
definition ofInv
  signature: (s : Y ⟶ X) (hs : W s)
  body: mk (𝟙 X) s hs

中文:
定义 ofInv
  签名: (s : Y ⟶ X) (hs : W s)
  定义体: mk (𝟙 X) s hs
-/
def ofInv (s : Y ⟶ X) (hs : W s) :
    W.LeftFraction X Y := mk (𝟙 X) s hs

instance {L : C ⥤ D} [L.IsLocalization W] (z : W.LeftFraction X Y) :
    IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  body: have := hL _ φ.hs
  L.map φ.f ≫ inv (L.map φ.s)

@[reassoc (attr := simp)]

中文:
定义 map
  签名: (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  定义体: have := hL _ φ.hs
  L.map φ.f ≫ inv (L.map φ.s)

@[reassoc (attr := simp)]

Depends on / 依赖: L.map
-/
noncomputable def map (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  L.map φ.f ≫ inv (L.map φ.s)

@[reassoc (attr := simp)]
/--
lemma `map_comp_map_s` / 引理 `map_comp_map_s`

English:
lemma map_comp_map_s
  given: (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  proof: by
  let := hL _ φ.hs
  simp [map]

中文:
引理 map_comp_map_s
  条件: (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  证明: by
  let := hL _ φ.hs
  simp [map]
-/
lemma map_comp_map_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    φ.map L hL ≫ L.map φ.s = L.map φ.f := by
  let := hL _ φ.hs
  simp [map]

variable (W)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_ofHom` / 引理 `map_ofHom`

English:
lemma map_ofHom
  given: (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities]
  proof: by
  simp [map]

中文:
引理 map_ofHom
  条件: (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities]
  证明: by
  simp [map]
-/
lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `map_ofInv_hom_id` / 引理 `map_ofInv_hom_id`

English:
lemma map_ofInv_hom_id
  given: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  proof: by
  let := hL _ hs
  simp [map]

中文:
引理 map_ofInv_hom_id
  条件: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  证明: by
  let := hL _ hs
  simp [map]
-/
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  let := hL _ hs
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `map_hom_ofInv_id` / 引理 `map_hom_ofInv_id`

English:
lemma map_hom_ofInv_id
  given: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  proof: by
  let := hL _ hs
  simp [map]

中文:
引理 map_hom_ofInv_id
  条件: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  证明: by
  let := hL _ hs
  simp [map]
-/
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  let := hL _ hs
  simp [map]

variable {W}

/--
lemma `cases` / 引理 `cases`

English:
lemma cases
  given: (α : W.LeftFraction X Y)
  proof: ⟨_, _, _, _, rfl⟩

中文:
引理 cases
  条件: (α : W.LeftFraction X Y)
  证明: ⟨_, _, _, _, rfl⟩
-/
lemma cases (α : W.LeftFraction X Y) :
    exists (Y' : C) (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s), α = LeftFraction.mk f s hs :=
  ⟨_, _, _, _, rfl⟩

end LeftFraction

/--
Definition of `RightFraction` / `RightFraction` 的定义

English:
structure RightFraction
  parameters: (W : MorphismProperty C) (X Y : C)
  axioms and operations (4):
    - {X' : C}
    - s : X' ⟶ X
    - hs : W s
    - f : X' ⟶ Y

中文:
结构 RightFraction
  参数: (W : Morphism命题erty C) (X Y : C)
  公理与运算 (4 个):
    - {X' : C}
    - s : X' ⟶ X
    - hs : W s
    - f : X' ⟶ Y
-/
structure RightFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a right fraction -/
  {X' : C}
  /-- the denominator of a right fraction -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of a right fraction -/
  f : X' ⟶ Y

namespace RightFraction

variable (W : MorphismProperty C)
variable {X Y : C}

/-- The right fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: (f : X ⟶ Y) [W.ContainsIdentities]
  body: mk (𝟙 X) (W.id_mem X) f

中文:
定义 ofHom
  签名: (f : X ⟶ Y) [W.ContainsIdentities]
  定义体: mk (𝟙 X) (W.id_mem X) f

Depends on / 依赖: W.id_mem, id_mem
-/
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    W.RightFraction X Y := mk (𝟙 X) (W.id_mem X) f

variable {W}

/-- The right fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
/--
Definition of `ofInv` / `ofInv` 的定义

English:
definition ofInv
  signature: (s : Y ⟶ X) (hs : W s)
  body: mk s hs (𝟙 Y)

中文:
定义 ofInv
  签名: (s : Y ⟶ X) (hs : W s)
  定义体: mk s hs (𝟙 Y)
-/
def ofInv (s : Y ⟶ X) (hs : W s) :
    W.RightFraction X Y := mk s hs (𝟙 Y)

instance {L : C ⥤ D} [L.IsLocalization W] (z : W.RightFraction X Y) :
    IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  body: have := hL _ φ.hs
  inv (L.map φ.s) ≫ L.map φ.f

@[reassoc (attr := simp)]

中文:
定义 map
  签名: (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  定义体: have := hL _ φ.hs
  inv (L.map φ.s) ≫ L.map φ.f

@[reassoc (attr := simp)]

Depends on / 依赖: L.map
-/
noncomputable def map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  inv (L.map φ.s) ≫ L.map φ.f

@[reassoc (attr := simp)]
/--
lemma `map_s_comp_map` / 引理 `map_s_comp_map`

English:
lemma map_s_comp_map
  given: (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  proof: by
  let := hL _ φ.hs
  simp [map]

中文:
引理 map_s_comp_map
  条件: (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  证明: by
  let := hL _ φ.hs
  simp [map]
-/
lemma map_s_comp_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map φ.s ≫ φ.map L hL = L.map φ.f := by
  let := hL _ φ.hs
  simp [map]

variable (W)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `map_ofHom` / 引理 `map_ofHom`

English:
lemma map_ofHom
  given: (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities]
  proof: by
  simp [map]

中文:
引理 map_ofHom
  条件: (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities]
  证明: by
  simp [map]
-/
lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `map_ofInv_hom_id` / 引理 `map_ofInv_hom_id`

English:
lemma map_ofInv_hom_id
  given: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  proof: by
  let := hL _ hs
  simp [map]

中文:
引理 map_ofInv_hom_id
  条件: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  证明: by
  let := hL _ hs
  simp [map]
-/
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  let := hL _ hs
  simp [map]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `map_hom_ofInv_id` / 引理 `map_hom_ofInv_id`

English:
lemma map_hom_ofInv_id
  given: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  proof: by
  let := hL _ hs
  simp [map]

中文:
引理 map_hom_ofInv_id
  条件: (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L)
  证明: by
  let := hL _ hs
  simp [map]
-/
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  let := hL _ hs
  simp [map]

variable {W}

/--
lemma `cases` / 引理 `cases`

English:
lemma cases
  given: (α : W.RightFraction X Y)
  proof: ⟨_, _, _, _, rfl⟩

中文:
引理 cases
  条件: (α : W.RightFraction X Y)
  证明: ⟨_, _, _, _, rfl⟩
-/
lemma cases (α : W.RightFraction X Y) :
    exists (X' : C) (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y), α = RightFraction.mk s hs f :=
  ⟨_, _, _, _, rfl⟩

end RightFraction

variable (W : MorphismProperty C)

/--
Definition of `HasLeftCalculusOfFractions` / `HasLeftCalculusOfFractions` 的定义

English:
class HasLeftCalculusOfFractions
  parameters: : Prop extends W.IsMultiplicative where
  extends: W.IsMultiplicative
  axioms and operations (2):
    - exists_leftFraction(⦃X Y) : C⦄ (φ : W.RightFraction X Y) : exists (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f
    - ext : forall ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s) (_ : s ≫ f₁ = s ≫ f₂), exists (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

中文:
类 HasLeftCalculusOfFractions
  参数: : 命题 extends W.IsMultiplicative where
  继承: W.IsMultiplicative
  公理与运算 (2 个):
    - exists_leftFraction(⦃X Y) : C⦄ (φ : W.RightFraction X Y) : 存在 (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f
    - ext : 对任意 ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s) (_ : s ≫ f₁ = s ≫ f₂), 存在 (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t
-/
class HasLeftCalculusOfFractions : Prop extends W.IsMultiplicative where
  exists_leftFraction ⦃X Y : C⦄ (φ : W.RightFraction X Y) :
    exists (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f
  ext : forall ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s)
    (_ : s ≫ f₁ = s ≫ f₂), exists (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

/--
Definition of `HasRightCalculusOfFractions` / `HasRightCalculusOfFractions` 的定义

English:
class HasRightCalculusOfFractions
  parameters: : Prop extends W.IsMultiplicative where
  extends: W.IsMultiplicative
  axioms and operations (2):
    - exists_rightFraction(⦃X Y) : C⦄ (φ : W.LeftFraction X Y) : exists (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s
    - ext : forall ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s) (_ : f₁ ≫ s = f₂ ≫ s), exists (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

中文:
类 HasRightCalculusOfFractions
  参数: : 命题 extends W.IsMultiplicative where
  继承: W.IsMultiplicative
  公理与运算 (2 个):
    - exists_rightFraction(⦃X Y) : C⦄ (φ : W.LeftFraction X Y) : 存在 (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s
    - ext : 对任意 ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s) (_ : f₁ ≫ s = f₂ ≫ s), 存在 (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂
-/
class HasRightCalculusOfFractions : Prop extends W.IsMultiplicative where
  exists_rightFraction ⦃X Y : C⦄ (φ : W.LeftFraction X Y) :
    exists (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s
  ext : forall ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s)
    (_ : f₁ ≫ s = f₂ ≫ s), exists (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

variable {W}

/--
lemma `RightFraction.exists_leftFraction` / 引理 `RightFraction.exists_leftFraction`

English:
lemma RightFraction.exists_leftFraction
  statement: [W.HasLeftCalculusOfFractions] {X Y : C}
  proof: HasLeftCalculusOfFractions.exists_leftFraction φ

中文:
引理 RightFraction.exists_leftFraction
  结论: [W.HasLeftCalculusOfFractions] {X Y : C}
  证明: HasLeftCalculusOfFractions.exists_leftFraction φ

Depends on / 依赖: HasLeftCalculusOfFractions, HasLeftCalculusOfFractions.exists_leftFraction, exists_leftFraction
-/
lemma RightFraction.exists_leftFraction [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : exists (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f :=
  HasLeftCalculusOfFractions.exists_leftFraction φ

/--
Definition of `RightFraction.leftFraction` / `RightFraction.leftFraction` 的定义

English:
definition RightFraction.leftFraction
  signature: [W.HasLeftCalculusOfFractions] {X Y : C}
  body: φ.exists_leftFraction.choose

@[reassoc]

中文:
定义 RightFraction.leftFraction
  签名: [W.HasLeftCalculusOfFractions] {X Y : C}
  定义体: φ.exists_leftFraction.choose

@[reassoc]

Depends on / 依赖: exists_leftFraction, exists_leftFraction.choose
-/
noncomputable def RightFraction.leftFraction [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : W.LeftFraction X Y :=
  φ.exists_leftFraction.choose

@[reassoc]
/--
lemma `RightFraction.leftFraction_fac` / 引理 `RightFraction.leftFraction_fac`

English:
lemma RightFraction.leftFraction_fac
  statement: [W.HasLeftCalculusOfFractions] {X Y : C}
  proof: φ.exists_leftFraction.choose_spec

中文:
引理 RightFraction.leftFraction_fac
  结论: [W.HasLeftCalculusOfFractions] {X Y : C}
  证明: φ.exists_leftFraction.choose_spec

Depends on / 依赖: choose_spec, exists_leftFraction, exists_leftFraction.choose_spec
-/
lemma RightFraction.leftFraction_fac [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : φ.f ≫ φ.leftFraction.s = φ.s ≫ φ.leftFraction.f :=
  φ.exists_leftFraction.choose_spec

/--
lemma `LeftFraction.exists_rightFraction` / 引理 `LeftFraction.exists_rightFraction`

English:
lemma LeftFraction.exists_rightFraction
  statement: [W.HasRightCalculusOfFractions] {X Y : C}
  proof: HasRightCalculusOfFractions.exists_rightFraction φ

中文:
引理 LeftFraction.exists_rightFraction
  结论: [W.HasRightCalculusOfFractions] {X Y : C}
  证明: HasRightCalculusOfFractions.exists_rightFraction φ

Depends on / 依赖: HasRightCalculusOfFractions, HasRightCalculusOfFractions.exists_rightFraction, exists_rightFraction
-/
lemma LeftFraction.exists_rightFraction [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : exists (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s :=
  HasRightCalculusOfFractions.exists_rightFraction φ

/--
Definition of `LeftFraction.rightFraction` / `LeftFraction.rightFraction` 的定义

English:
definition LeftFraction.rightFraction
  signature: [W.HasRightCalculusOfFractions] {X Y : C}
  body: φ.exists_rightFraction.choose

@[reassoc]

中文:
定义 LeftFraction.rightFraction
  签名: [W.HasRightCalculusOfFractions] {X Y : C}
  定义体: φ.exists_rightFraction.choose

@[reassoc]

Depends on / 依赖: exists_rightFraction, exists_rightFraction.choose
-/
noncomputable def LeftFraction.rightFraction [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : W.RightFraction X Y :=
  φ.exists_rightFraction.choose

@[reassoc]
/--
lemma `LeftFraction.rightFraction_fac` / 引理 `LeftFraction.rightFraction_fac`

English:
lemma LeftFraction.rightFraction_fac
  statement: [W.HasRightCalculusOfFractions] {X Y : C}
  proof: φ.exists_rightFraction.choose_spec

中文:
引理 LeftFraction.rightFraction_fac
  结论: [W.HasRightCalculusOfFractions] {X Y : C}
  证明: φ.exists_rightFraction.choose_spec

Depends on / 依赖: choose_spec, exists_rightFraction, exists_rightFraction.choose_spec
-/
lemma LeftFraction.rightFraction_fac [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : φ.rightFraction.s ≫ φ.f = φ.rightFraction.f ≫ φ.s :=
  φ.exists_rightFraction.choose_spec

/--
Definition of `LeftFractionRel` / `LeftFractionRel` 的定义

English:
definition LeftFractionRel
  signature: {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
  body: exists (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)

中文:
定义 LeftFractionRel
  签名: {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
  定义体: exists (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)
-/
def LeftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) : Prop :=
  exists (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)

namespace LeftFractionRel

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: {X Y : C} (z : W.LeftFraction X Y)
  statement: LeftFractionRel z z
  proof: ⟨z.Y', 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [Category.comp_id] using z.hs⟩

中文:
引理 refl
  条件: {X Y : C} (z : W.LeftFraction X Y)
  结论: LeftFractionRel z z
  证明: ⟨z.Y', 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [Category.comp_id] using z.hs⟩

Depends on / 依赖: Category, Category.comp_id, comp_id, z.hs
-/
lemma refl {X Y : C} (z : W.LeftFraction X Y) : LeftFractionRel z z :=
  ⟨z.Y', 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [Category.comp_id] using z.hs⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂)
  proof: by
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
  exact ⟨Z, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩

中文:
引理 symm
  条件: {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂)
  证明: by
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
  exact ⟨Z, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩

Depends on / 依赖: hft.symm, hst.symm
-/
lemma symm {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) :
    LeftFractionRel z₂ z₁ := by
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
  exact ⟨Z, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y}
  proof: by
  obtain ⟨Z₄, t₁, t₂, hst, hft, ht⟩ := h₁₂
  obtain ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩ := h₂₃
  obtain ⟨⟨v₄, v₅, hv₅⟩, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
    (RightFraction.mk (z₁.s ≫ t₁) ht (z₃.s ≫ u₃))
  simp only [Category.assoc] at fac
  have eq : z₂.s ≫ u₂ ≫ v₅ = z₂.s ≫ t₂ ≫ v₄ :

中文:
引理 trans
  结论: {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y}
  证明: by
  obtain ⟨Z₄, t₁, t₂, hst, hft, ht⟩ := h₁₂
  obtain ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩ := h₂₃
  obtain ⟨⟨v₄, v₅, hv₅⟩, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
    (RightFraction.mk (z₁.s ≫ t₁) ht (z₃.s ≫ u₃))
  simp only [Category.assoc] at fac
  have eq : z₂.s ≫ u₂ ≫ v₅ = z₂.s ≫ t₂ ≫ v₄ :

Depends on / 依赖: Category, Category.assoc, HasLeftCalculusOfFractions, HasLeftCalculusOfFractions.exists_leftFraction, HasLeftCalculusOfFractions.ext, RightFraction, RightFraction.mk, exists_leftFraction, reassoc_of
-/
lemma trans {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y}
    [HasLeftCalculusOfFractions W]
    (h₁₂ : LeftFractionRel z₁ z₂) (h₂₃ : LeftFractionRel z₂ z₃) :
    LeftFractionRel z₁ z₃ := by
  obtain ⟨Z₄, t₁, t₂, hst, hft, ht⟩ := h₁₂
  obtain ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩ := h₂₃
  obtain ⟨⟨v₄, v₅, hv₅⟩, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
    (RightFraction.mk (z₁.s ≫ t₁) ht (z₃.s ≫ u₃))
  simp only [Category.assoc] at fac
  have eq : z₂.s ≫ u₂ ≫ v₅ = z₂.s ≫ t₂ ≫ v₄ := by
    simpa only [← reassoc_of% hsu, reassoc_of% hst] using fac
  obtain ⟨Z₇, w, hw, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₂.hs eq
  simp only [Category.assoc] at fac'
  refine ⟨Z₇, t₁ ≫ v₄ ≫ w, u₃ ≫ v₅ ≫ w, ?_, ?_, ?_⟩
  · rw [reassoc_of% fac]
  · rw [reassoc_of% hft, ← fac', reassoc_of% hfu]
  · rw [← reassoc_of% fac, ← reassoc_of% hsu, ← Category.assoc]
    exact W.comp_mem _ _ hu (W.comp_mem _ _ hv₅ hw)

end LeftFractionRel

section

variable (W)

/--
lemma `equivalenceLeftFractionRel` / 引理 `equivalenceLeftFractionRel`

English:
lemma equivalenceLeftFractionRel
  given: [W.HasLeftCalculusOfFractions] (X Y : C)
  proof: LeftFractionRel.refl
  symm := LeftFractionRel.symm
  trans := LeftFractionRel.trans

中文:
引理 equivalenceLeftFractionRel
  条件: [W.HasLeftCalculusOfFractions] (X Y : C)
  证明: LeftFractionRel.refl
  symm := LeftFractionRel.symm
  trans := LeftFractionRel.trans

Depends on / 依赖: LeftFractionRel, LeftFractionRel.refl
-/
lemma equivalenceLeftFractionRel [W.HasLeftCalculusOfFractions] (X Y : C) :
    @_root_.Equivalence (W.LeftFraction X Y) LeftFractionRel where
  refl := LeftFractionRel.refl
  symm := LeftFractionRel.symm
  trans := LeftFractionRel.trans

variable {W}

namespace LeftFraction

open HasLeftCalculusOfFractions

/-- Auxiliary definition for the composition of left fractions. -/
@[simp]
/--
Definition of `comp₀` / `comp₀` 的定义

English:
definition comp₀
  signature: [W.HasLeftCalculusOfFractions] {X Y Z : C}
  body: mk (z₁.f ≫ z₃.f) (z₂.s ≫ z₃.s) (W.comp_mem _ _ z₂.hs z₃.hs)

中文:
定义 comp₀
  签名: [W.HasLeftCalculusOfFractions] {X Y Z : C}
  定义体: mk (z₁.f ≫ z₃.f) (z₂.s ≫ z₃.s) (W.comp_mem _ _ z₂.hs z₃.hs)

Depends on / 依赖: W.comp_mem, comp_mem
-/
def comp₀ [W.HasLeftCalculusOfFractions] {X Y Z : C}
    (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) (z₃ : W.LeftFraction z₁.Y' z₂.Y') :
    W.LeftFraction X Z :=
  mk (z₁.f ≫ z₃.f) (z₂.s ≫ z₃.s) (W.comp_mem _ _ z₂.hs z₃.hs)

/--
lemma `comp₀_rel` / 引理 `comp₀_rel`

English:
lemma comp₀_rel
  statement: [W.HasLeftCalculusOfFractions]
  proof: by
  obtain ⟨z₄, fac⟩ := exists_leftFraction (RightFraction.mk z₃.s z₃.hs z₃'.s)
  dsimp at fac
  have eq : z₁.s ≫ z₃.f ≫ z₄.f = z₁.s ≫ z₃'.f ≫ z₄.s := by
    rw [← reassoc_of% h₃]; rw [← reassoc_of% h₃']; rw [fac]
  obtain ⟨Y, t, ht, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₁.hs eq
  simp onl

中文:
引理 comp₀_rel
  结论: [W.HasLeftCalculusOfFractions]
  证明: by
  obtain ⟨z₄, fac⟩ := exists_leftFraction (RightFraction.mk z₃.s z₃.hs z₃'.s)
  dsimp at fac
  have eq : z₁.s ≫ z₃.f ≫ z₄.f = z₁.s ≫ z₃'.f ≫ z₄.s := by
    rw [← reassoc_of% h₃]; rw [← reassoc_of% h₃']; rw [fac]
  obtain ⟨Y, t, ht, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₁.hs eq
  simp onl

Depends on / 依赖: HasLeftCalculusOfFractions, HasLeftCalculusOfFractions.ext, RightFraction, RightFraction.mk, W.comp_mem, comp_mem, exists_leftFraction, reassoc_of
-/
lemma comp₀_rel [W.HasLeftCalculusOfFractions]
    {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ z₃' : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f)
    (h₃' : z₂.f ≫ z₃'.s = z₁.s ≫ z₃'.f) :
    LeftFractionRel (z₁.comp₀ z₂ z₃) (z₁.comp₀ z₂ z₃') := by
  obtain ⟨z₄, fac⟩ := exists_leftFraction (RightFraction.mk z₃.s z₃.hs z₃'.s)
  dsimp at fac
  have eq : z₁.s ≫ z₃.f ≫ z₄.f = z₁.s ≫ z₃'.f ≫ z₄.s := by
    rw [← reassoc_of% h₃]; rw [← reassoc_of% h₃']; rw [fac]
  obtain ⟨Y, t, ht, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₁.hs eq
  simp only [assoc] at fac'
  refine ⟨Y, z₄.f ≫ t, z₄.s ≫ t, ?_, ?_, ?_⟩
  · simp only [comp₀, assoc, reassoc_of% fac]
  · simp only [comp₀, assoc, fac']
  · simp only [comp₀, assoc, ← reassoc_of% fac]
    exact W.comp_mem _ _ z₂.hs (W.comp_mem _ _ z₃'.hs (W.comp_mem _ _ z₄.hs ht))

variable (W) in
/--
Definition of `Localization.Hom` / `Localization.Hom` 的定义

English:
definition Localization.Hom
  signature: (X Y : C)
  body: Quot (LeftFractionRel : W.LeftFraction X Y -> W.LeftFraction X Y -> Prop)

中文:
定义 Localization.Hom
  签名: (X Y : C)
  定义体: Quot (LeftFractionRel : W.LeftFraction X Y -> W.LeftFraction X Y -> Prop)

Depends on / 依赖: LeftFraction, LeftFractionRel, W.LeftFraction
-/
def Localization.Hom (X Y : C) :=
  Quot (LeftFractionRel : W.LeftFraction X Y -> W.LeftFraction X Y -> Prop)

/--
Definition of `Localization.Hom.mk` / `Localization.Hom.mk` 的定义

English:
definition Localization.Hom.mk
  signature: {X Y : C} (z : W.LeftFraction X Y)
  body: Quot.mk _ z

中文:
定义 Localization.Hom.mk
  签名: {X Y : C} (z : W.LeftFraction X Y)
  定义体: Quot.mk _ z

Depends on / 依赖: Quot.mk
-/
def Localization.Hom.mk {X Y : C} (z : W.LeftFraction X Y) : Localization.Hom W X Y :=
  Quot.mk _ z

/--
lemma `Localization.Hom.mk_surjective` / 引理 `Localization.Hom.mk_surjective`

English:
lemma Localization.Hom.mk_surjective
  given: {X Y : C} (f : Localization.Hom W X Y)
  proof: by
  obtain ⟨z⟩ := f
  exact ⟨z, rfl⟩

中文:
引理 Localization.Hom.mk_surjective
  条件: {X Y : C} (f : Localization.Hom W X Y)
  证明: by
  obtain ⟨z⟩ := f
  exact ⟨z, rfl⟩
-/
lemma Localization.Hom.mk_surjective {X Y : C} (f : Localization.Hom W X Y) :
    exists (z : W.LeftFraction X Y), f = mk z := by
  obtain ⟨z⟩ := f
  exact ⟨z, rfl⟩

variable [W.HasLeftCalculusOfFractions]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  body: Localization.Hom.mk (z₁.comp₀ z₂ (RightFraction.mk z₁.s z₁.hs z₂.f).leftFraction)

中文:
定义 comp
  定义体: Localization.Hom.mk (z₁.comp₀ z₂ (RightFraction.mk z₁.s z₁.hs z₂.f).leftFraction)

Depends on / 依赖: Localization, Localization.Hom.mk, RightFraction, RightFraction.mk, leftFraction
-/
noncomputable def comp
    {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) :
    Localization.Hom W X Z :=
  Localization.Hom.mk (z₁.comp₀ z₂ (RightFraction.mk z₁.s z₁.hs z₂.f).leftFraction)

/--
lemma `comp_eq` / 引理 `comp_eq`

English:
lemma comp_eq
  statement: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  proof: Quot.sound (LeftFraction.comp₀_rel _ _ _ _
    (RightFraction.leftFraction_fac (RightFraction.mk z₁.s z₁.hs z₂.f)) h₃)

中文:
引理 comp_eq
  结论: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  证明: Quot.sound (LeftFraction.comp₀_rel _ _ _ _
    (RightFraction.leftFraction_fac (RightFraction.mk z₁.s z₁.hs z₂.f)) h₃)

Depends on / 依赖: LeftFraction, LeftFraction.comp, Quot.sound, RightFraction, RightFraction.leftFraction_fac, RightFraction.mk, leftFraction_fac
-/
lemma comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) :
    z₁.comp z₂ = Localization.Hom.mk (z₁.comp₀ z₂ z₃) :=
  Quot.sound (LeftFraction.comp₀_rel _ _ _ _
    (RightFraction.leftFraction_fac (RightFraction.mk z₁.s z₁.hs z₂.f)) h₃)

namespace Localization

/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: {X Y Z : C} (z₁ : Hom W X Y) (z₂ : Hom W Y Z)
  body: by
  refine Quot.lift₂ (fun a b => a.comp b) ?_ ?_ z₁ z₂
  · rintro a b₁ b₂ ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₁.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₂.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFract

中文:
定义 Hom.comp
  签名: {X Y Z : C} (z₁ : Hom W X Y) (z₂ : Hom W Y Z)
  定义体: by
  refine Quot.lift₂ (fun a b => a.comp b) ?_ ?_ z₁ z₂
  · rintro a b₁ b₂ ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₁.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₂.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFract
-/
noncomputable def Hom.comp {X Y Z : C} (z₁ : Hom W X Y) (z₂ : Hom W Y Z) : Hom W X Z := by
  refine Quot.lift₂ (fun a b => a.comp b) ?_ ?_ z₁ z₂
  · rintro a b₁ b₂ ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₁.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₂.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFraction (RightFraction.mk z₁.s z₁.hs t₁)
    obtain ⟨w₂, fac₂'⟩ := exists_leftFraction (RightFraction.mk z₂.s z₂.hs t₂)
    obtain ⟨u, fac₃⟩ := exists_leftFraction (RightFraction.mk w₁.s w₁.hs w₂.s)
    dsimp at fac₁ fac₂ fac₁' fac₂' fac₃ ⊢
    have eq : a.s ≫ z₁.f ≫ w₁.f ≫ u.f = a.s ≫ z₂.f ≫ w₂.f ≫ u.s := by
      rw [← reassoc_of% fac₁]; rw [← reassoc_of% fac₂]; rw [← reassoc_of% fac₁']; rw [← reassoc_of% fac₂']; rw [reassoc_of% hft]; rw [fac₃]
    obtain ⟨Z, p, hp, fac₄⟩ := HasLeftCalculusOfFractions.ext _ _ _ a.hs eq
    simp only [assoc] at fac₄
    rw [comp_eq _ _ z₁ fac₁]; rw [comp_eq _ _ z₂ fac₂]
    apply Quot.sound
    refine ⟨Z, w₁.f ≫ u.f ≫ p, w₂.f ≫ u.s ≫ p, ?_, ?_, ?_⟩
    · dsimp
      simp only [assoc, ← reassoc_of% fac₁', ← reassoc_of% fac₂',
        reassoc_of% hst, reassoc_of% fac₃]
    · dsimp
      simp only [assoc, fac₄]
    · dsimp
      simp only [assoc]
      rw [← reassoc_of% fac₁']; rw [← reassoc_of% fac₃]; rw [← assoc]
      exact W.comp_mem _ _ ht (W.comp_mem _ _ w₂.hs (W.comp_mem _ _ u.hs hp))
  · rintro a₁ a₂ b ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a₁.s a₁.hs b.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a₂.s a₂.hs b.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFraction (RightFraction.mk (a₁.s ≫ t₁) ht (b.f ≫ z₁.s))
    obtain ⟨w₂, fac₂'⟩ := exists_leftFraction (RightFraction.mk (a₂.s ≫ t₂)
      (show W _ by rw [← hst]; exact ht) (b.f ≫ z₂.s))
    let p₁ : W.LeftFraction X Z := LeftFraction.mk (a₁.f ≫ t₁ ≫ w₁.f) (b.s ≫ z₁.s ≫ w₁.s)
      (W.comp_mem _ _ b.hs (W.comp_mem _ _ z₁.hs w₁.hs))
    let p₂ : W.LeftFraction X Z := LeftFraction.mk (a₂.f ≫ t₂ ≫ w₂.f) (b.s ≫ z₂.s ≫ w₂.s)
      (W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs w₂.hs))
    dsimp at fac₁ fac₂ fac₁' fac₂' ⊢
    simp only [assoc] at fac₁' fac₂'
    rw [comp_eq _ _ z₁ fac₁]; rw [comp_eq _ _ z₂ fac₂]
    apply Quot.sound
    refine LeftFractionRel.trans ?_ ((?_ : LeftFractionRel p₁ p₂).trans ?_)
    · have eq : a₁.s ≫ z₁.f ≫ w₁.s = a₁.s ≫ t₁ ≫ w₁.f := by rw [← fac₁', reassoc_of% fac₁]
      obtain ⟨Z, u, hu, fac₃⟩ := HasLeftCalculusOfFractions.ext _ _ _ a₁.hs eq
      simp only [assoc] at fac₃
      refine ⟨Z, w₁.s ≫ u, u, ?_, ?_, ?_⟩
      · dsimp [p₁]
        simp only [assoc]
      · dsimp [p₁]
        simp only [assoc, fac₃]
      · dsimp
        simp only [assoc]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₁.hs (W.comp_mem _ _ w₁.hs hu))
    · obtain ⟨q, fac₃⟩ := exists_leftFraction (RightFraction.mk (z₁.s ≫ w₁.s)
        (W.comp_mem _ _ z₁.hs w₁.hs) (z₂.s ≫ w₂.s))
      dsimp at fac₃
      simp only [assoc] at fac₃
      have eq : a₁.s ≫ t₁ ≫ w₁.f ≫ q.f = a₁.s ≫ t₁ ≫ w₂.f ≫ q.s := by
        rw [← reassoc_of% fac₁']; rw [← fac₃]; rw [reassoc_of% hst]; rw [reassoc_of% fac₂']
      obtain ⟨Z, u, hu, fac₄⟩ := HasLeftCalculusOfFractions.ext _ _ _ a₁.hs eq
      simp only [assoc] at fac₄
      refine ⟨Z, q.f ≫ u, q.s ≫ u, ?_, ?_, ?_⟩
      · simp only [p₁, p₂, assoc, reassoc_of% fac₃]
      · rw [assoc, assoc, assoc, assoc, fac₄, reassoc_of% hft]
      · simp only [p₁, assoc, ← reassoc_of% fac₃]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs
          (W.comp_mem _ _ w₂.hs (W.comp_mem _ _ q.hs hu)))
    · have eq : a₂.s ≫ z₂.f ≫ w₂.s = a₂.s ≫ t₂ ≫ w₂.f := by
        rw [← fac₂']; rw [reassoc_of% fac₂]
      obtain ⟨Z, u, hu, fac₄⟩ := HasLeftCalculusOfFractions.ext _ _ _ a₂.hs eq
      simp only [assoc] at fac₄
      refine ⟨Z, u, w₂.s ≫ u, ?_, ?_, ?_⟩
      · dsimp [p₁, p₂]
        simp only [assoc]
      · dsimp [p₁, p₂]
        simp only [assoc, fac₄]
      · dsimp [p₁, p₂]
        simp only [assoc]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs (W.comp_mem _ _ w₂.hs hu))

/--
lemma `Hom.comp_eq` / 引理 `Hom.comp_eq`

English:
lemma Hom.comp_eq
  given: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  proof: rfl

中文:
引理 Hom.comp_eq
  条件: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  证明: rfl
-/
lemma Hom.comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) :
    Hom.comp (mk z₁) (mk z₂) = z₁.comp z₂ := rfl

end Localization

/-- The constructed localized category for a morphism property
that has left calculus of fractions. -/
@[nolint unusedArguments]
/--
Definition of `Localization` / `Localization` 的定义

English:
definition Localization
  signature: (_ : MorphismProperty C)
  body: C

中文:
定义 Localization
  签名: (_ : Morphism命题erty C)
  定义体: C
-/
def Localization (_ : MorphismProperty C) := C

namespace Localization

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Localization W)
  body: Localization.Hom W X Y
  id _ := Localization.Hom.mk (ofHom W (𝟙 _))
  comp f g := f.comp g
  comp_id := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    rw [Hom.comp_eq]; rw [comp_eq z (ofHom W (𝟙 Y)) (ofInv z.s z.hs) (by simp)]
    dsimp [comp₀]
    simp only [comp_id, id_c

中文:
实例 :
  签名: Category (Localization W)
  定义体: Localization.Hom W X Y
  id _ := Localization.Hom.mk (ofHom W (𝟙 _))
  comp f g := f.comp g
  comp_id := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    rw [Hom.comp_eq]; rw [comp_eq z (ofHom W (𝟙 Y)) (ofInv z.s z.hs) (by simp)]
    dsimp [comp₀]
    simp only [comp_id, id_c

Depends on / 依赖: Localization, Localization.Hom
-/
noncomputable instance : Category (Localization W) where
  Hom X Y := Localization.Hom W X Y
  id _ := Localization.Hom.mk (ofHom W (𝟙 _))
  comp f g := f.comp g
  comp_id := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    rw [Hom.comp_eq]; rw [comp_eq z (ofHom W (𝟙 Y)) (ofInv z.s z.hs) (by simp)]
    dsimp [comp₀]
    simp only [comp_id, id_comp]
  id_comp := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    rw [Hom.comp_eq]; rw [comp_eq (ofHom W (𝟙 X)) z (ofHom W z.f) (by simp)]
    dsimp
    simp only [id_comp, comp_id]
  assoc := by
    rintro (X₁ X₂ X₃ X₄ : C) f₁ f₂ f₃
    obtain ⟨z₁, rfl⟩ := Hom.mk_surjective f₁
    obtain ⟨z₂, rfl⟩ := Hom.mk_surjective f₂
    obtain ⟨z₃, rfl⟩ := Hom.mk_surjective f₃
    rw [Hom.comp_eq z₁ z₂]; rw [Hom.comp_eq z₂ z₃]
    obtain ⟨z₁₂, fac₁₂⟩ := exists_leftFraction (RightFraction.mk z₁.s z₁.hs z₂.f)
    obtain ⟨z₂₃, fac₂₃⟩ := exists_leftFraction (RightFraction.mk z₂.s z₂.hs z₃.f)
    obtain ⟨z', fac⟩ := exists_leftFraction (RightFraction.mk z₁₂.s z₁₂.hs z₂₃.f)
    dsimp at fac₁₂ fac₂₃ fac
    rw [comp_eq z₁ z₂ z₁₂ fac₁₂]; rw [comp_eq z₂ z₃ z₂₃ fac₂₃]; rw [comp₀]; rw [comp₀]; rw [Hom.comp_eq]; rw [Hom.comp_eq]; rw [comp_eq _ z₃ (mk z'.f (z₂₃.s ≫ z'.s) (W.comp_mem _ _ z₂₃.hs z'.hs))
        (by dsimp; rw [assoc]; rw [reassoc_of% fac₂₃]; rw [fac]),
      comp_eq z₁ _ (mk (z₁₂.f ≫ z'.f) z'.s z'.hs)
        (by dsimp; rw [assoc, ← reassoc_of% fac₁₂, fac])]
    simp

set_option backward.defeqAttrib.useBackward true in
variable (W) in
/-- The localization functor to the constructed localized category for a morphism property
that has left calculus of fractions. -/
@[simps obj]
/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  signature: : C ⥤ Localization W where
  body: X
  map f := Hom.mk (ofHom W f)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change _ = Hom.comp _ _
    rw [Hom.comp_eq]; rw [comp_eq (ofHom W f) (ofHom W g) (ofHom W g) (by simp)]
    simp only [ofHom, comp₀, comp_id]

中文:
定义 Q
  签名: : C ⥤ Localization W where
  定义体: X
  map f := Hom.mk (ofHom W f)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change _ = Hom.comp _ _
    rw [Hom.comp_eq]; rw [comp_eq (ofHom W f) (ofHom W g) (ofHom W g) (by simp)]
    simp only [ofHom, comp₀, comp_id]
-/
noncomputable def Q : C ⥤ Localization W where
  obj X := X
  map f := Hom.mk (ofHom W f)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change _ = Hom.comp _ _
    rw [Hom.comp_eq]; rw [comp_eq (ofHom W f) (ofHom W g) (ofHom W g) (by simp)]
    simp only [ofHom, comp₀, comp_id]

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {X Y : C} (f : W.LeftFraction X Y)
  body: Hom.mk f

中文:
缩写 homMk
  签名: {X Y : C} (f : W.LeftFraction X Y)
  定义体: Hom.mk f

Depends on / 依赖: Hom.mk
-/
noncomputable abbrev homMk {X Y : C} (f : W.LeftFraction X Y) : (Q W).obj X ⟶ (Q W).obj Y :=
  Hom.mk f

/--
lemma `homMk_eq_hom_mk` / 引理 `homMk_eq_hom_mk`

English:
lemma homMk_eq_hom_mk
  given: {X Y : C} (f : W.LeftFraction X Y)
  statement: homMk f = Hom.mk f
  proof: rfl

中文:
引理 homMk_eq_hom_mk
  条件: {X Y : C} (f : W.LeftFraction X Y)
  结论: homMk f = Hom.mk f
  证明: rfl
-/
lemma homMk_eq_hom_mk {X Y : C} (f : W.LeftFraction X Y) : homMk f = Hom.mk f := rfl

variable (W)

/--
lemma `Q_map` / 引理 `Q_map`

English:
lemma Q_map
  given: {X Y : C} (f : X ⟶ Y)
  statement: (Q W).map f = homMk (ofHom W f)
  proof: rfl

中文:
引理 Q_map
  条件: {X Y : C} (f : X ⟶ Y)
  结论: (Q W).map f = homMk (ofHom W f)
  证明: rfl
-/
lemma Q_map {X Y : C} (f : X ⟶ Y) : (Q W).map f = homMk (ofHom W f) := rfl

variable {W}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `homMk_comp_homMk` / 引理 `homMk_comp_homMk`

English:
lemma homMk_comp_homMk
  statement: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  proof: by
  change Hom.comp _ _ = _
  rw [Hom.comp_eq]; rw [comp_eq z₁ z₂ z₃ h₃]

中文:
引理 homMk_comp_homMk
  结论: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  证明: by
  change Hom.comp _ _ = _
  rw [Hom.comp_eq]; rw [comp_eq z₁ z₂ z₃ h₃]

Depends on / 依赖: Hom.comp, Hom.comp_eq, comp_eq
-/
lemma homMk_comp_homMk {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) :
    homMk z₁ ≫ homMk z₂ = homMk (z₁.comp₀ z₂ z₃) := by
  change Hom.comp _ _ = _
  rw [Hom.comp_eq]; rw [comp_eq z₁ z₂ z₃ h₃]

/--
lemma `homMk_eq_of_leftFractionRel` / 引理 `homMk_eq_of_leftFractionRel`

English:
lemma homMk_eq_of_leftFractionRel
  statement: {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
  proof: Quot.sound h

中文:
引理 homMk_eq_of_leftFractionRel
  结论: {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
  证明: Quot.sound h

Depends on / 依赖: Quot.sound
-/
lemma homMk_eq_of_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
    (h : LeftFractionRel z₁ z₂) :
    homMk z₁ = homMk z₂ :=
  Quot.sound h

/--
lemma `homMk_eq_iff_leftFractionRel` / 引理 `homMk_eq_iff_leftFractionRel`

English:
lemma homMk_eq_iff_leftFractionRel
  given: {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
  proof: @Equivalence.quot_mk_eq_iff _ _ (equivalenceLeftFractionRel W X Y) _ _

中文:
引理 homMk_eq_iff_leftFractionRel
  条件: {X Y : C} (z₁ z₂ : W.LeftFraction X Y)
  证明: @Equivalence.quot_mk_eq_iff _ _ (equivalenceLeftFractionRel W X Y) _ _

Depends on / 依赖: Equivalence, Equivalence.quot_mk_eq_iff, Iso.refl, NatIso, NatIso.ofComponents, equivalenceLeftFractionRel, ofComponents, quot_mk_eq_iff
-/
lemma homMk_eq_iff_leftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) :
    homMk z₁ = homMk z₂ ↔ LeftFractionRel z₁ z₂ :=
  @Equivalence.quot_mk_eq_iff _ _ (equivalenceLeftFractionRel W X Y) _ _

/--
Definition of `Qinv` / `Qinv` 的定义

English:
definition Qinv
  signature: {X Y : C} (s : X ⟶ Y) (hs : W s)
  body: homMk (ofInv s hs)

中文:
定义 Qinv
  签名: {X Y : C} (s : X ⟶ Y) (hs : W s)
  定义体: homMk (ofInv s hs)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def Qinv {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj Y ⟶ (Q W).obj X :=
  homMk (ofInv s hs)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `Q_map_comp_Qinv` / 引理 `Q_map_comp_Qinv`

English:
lemma Q_map_comp_Qinv
  given: {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s)
  proof: by
  dsimp only [Q_map, Qinv]
  rw [homMk_comp_homMk (ofHom W f) (ofInv s hs) (ofHom W (𝟙 _)) (by simp)]
  simp

中文:
引理 Q_map_comp_Qinv
  条件: {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s)
  证明: by
  dsimp only [Q_map, Qinv]
  rw [homMk_comp_homMk (ofHom W f) (ofInv s hs) (ofHom W (𝟙 _)) (by simp)]
  simp

Depends on / 依赖: Q_map, homMk_comp_homMk
-/
lemma Q_map_comp_Qinv {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (Q W).map f ≫ Qinv s hs = homMk (mk f s hs) := by
  dsimp only [Q_map, Qinv]
  rw [homMk_comp_homMk (ofHom W f) (ofInv s hs) (ofHom W (𝟙 _)) (by simp)]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism in `Localization W` that is induced by a morphism in `W`. -/
@[simps]
/--
Definition of `Qiso` / `Qiso` 的定义

English:
definition Qiso
  signature: {X Y : C} (s : X ⟶ Y) (hs : W s)
  body: (Q W).map s
  inv := Qinv s hs
  hom_inv_id := by
    rw [Q_map_comp_Qinv]
    apply homMk_eq_of_leftFractionRel
    exact ⟨_, 𝟙 Y, s, by simp, by simp, by simpa using hs⟩
  inv_hom_id := by
    dsimp only [Qinv, Q_map]
    rw [homMk_comp_homMk (ofInv s hs) (ofHom W s) (ofHom W (𝟙 Y)) (by simp)]
   

中文:
定义 Qiso
  签名: {X Y : C} (s : X ⟶ Y) (hs : W s)
  定义体: (Q W).map s
  inv := Qinv s hs
  hom_inv_id := by
    rw [Q_map_comp_Qinv]
    apply homMk_eq_of_leftFractionRel
    exact ⟨_, 𝟙 Y, s, by simp, by simp, by simpa using hs⟩
  inv_hom_id := by
    dsimp only [Qinv, Q_map]
    rw [homMk_comp_homMk (ofInv s hs) (ofHom W s) (ofHom W (𝟙 Y)) (by simp)]
   
-/
noncomputable def Qiso {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj X ≅ (Q W).obj Y where
  hom := (Q W).map s
  inv := Qinv s hs
  hom_inv_id := by
    rw [Q_map_comp_Qinv]
    apply homMk_eq_of_leftFractionRel
    exact ⟨_, 𝟙 Y, s, by simp, by simp, by simpa using hs⟩
  inv_hom_id := by
    dsimp only [Qinv, Q_map]
    rw [homMk_comp_homMk (ofInv s hs) (ofHom W s) (ofHom W (𝟙 Y)) (by simp)]
    apply homMk_eq_of_leftFractionRel
    exact ⟨_, 𝟙 Y, 𝟙 Y, by simp, by simp, by simpa using W.id_mem Y⟩

@[reassoc (attr := simp)]
/--
lemma `Qiso_hom_inv_id` / 引理 `Qiso_hom_inv_id`

English:
lemma Qiso_hom_inv_id
  given: {X Y : C} (s : X ⟶ Y) (hs : W s)
  proof: (Qiso s hs).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 Qiso_hom_inv_id
  条件: {X Y : C} (s : X ⟶ Y) (hs : W s)
  证明: (Qiso s hs).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id
-/
lemma Qiso_hom_inv_id {X Y : C} (s : X ⟶ Y) (hs : W s) :
    (Q W).map s ≫ Qinv s hs = 𝟙 _ := (Qiso s hs).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `Qiso_inv_hom_id` / 引理 `Qiso_inv_hom_id`

English:
lemma Qiso_inv_hom_id
  given: {X Y : C} (s : X ⟶ Y) (hs : W s)
  proof: (Qiso s hs).inv_hom_id

中文:
引理 Qiso_inv_hom_id
  条件: {X Y : C} (s : X ⟶ Y) (hs : W s)
  证明: (Qiso s hs).inv_hom_id

Depends on / 依赖: inv_hom_id
-/
lemma Qiso_inv_hom_id {X Y : C} (s : X ⟶ Y) (hs : W s) :
    Qinv s hs ≫ (Q W).map s = 𝟙 _ := (Qiso s hs).inv_hom_id

instance {X Y : C} (s : X ⟶ Y) (hs : W s) : IsIso (Qinv s hs) :=
inferInstanceAs IsIso (Qiso s hs).inv

section

variable {E : Type*} [Category* E]

/--
Definition of `Hom.map` / `Hom.map` 的定义

English:
definition Hom.map
  signature: {X Y : C} (f : Hom W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F)
  body: Quot.lift (fun f => f.map F hF) (by
    intro a₁ a₂ ⟨Z, t₁, t₂, hst, hft, h⟩
    have := hF _ h
    rw [← cancel_mono (F.map (a₁.s ≫ t₁))]; rw [F.map_comp]; rw [map_comp_map_s_assoc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [hst]; rw [hft]; rw [F.map_comp]; rw [F.map_comp]; rw [map_comp_map_s_assoc

中文:
定义 Hom.map
  签名: {X Y : C} (f : Hom W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F)
  定义体: Quot.lift (fun f => f.map F hF) (by
    intro a₁ a₂ ⟨Z, t₁, t₂, hst, hft, h⟩
    have := hF _ h
    rw [← cancel_mono (F.map (a₁.s ≫ t₁))]; rw [F.map_comp]; rw [map_comp_map_s_assoc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [hst]; rw [hft]; rw [F.map_comp]; rw [F.map_comp]; rw [map_comp_map_s_assoc

Depends on / 依赖: F.map, F.map_comp, Quot.lift, cancel_mono, f.map, map_comp, map_comp_map_s_assoc
-/
noncomputable def Hom.map {X Y : C} (f : Hom W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    F.obj X ⟶ F.obj Y :=
  Quot.lift (fun f => f.map F hF) (by
    intro a₁ a₂ ⟨Z, t₁, t₂, hst, hft, h⟩
    have := hF _ h
    rw [← cancel_mono (F.map (a₁.s ≫ t₁))]; rw [F.map_comp]; rw [map_comp_map_s_assoc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [hst]; rw [hft]; rw [F.map_comp]; rw [F.map_comp]; rw [map_comp_map_s_assoc]) f

@[simp]
/--
lemma `Hom.map_mk` / 引理 `Hom.map_mk`

English:
lemma Hom.map_mk
  given: {W} {X Y : C} (f : LeftFraction W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F)
  proof: rfl

中文:
引理 Hom.map_mk
  条件: {W} {X Y : C} (f : LeftFraction W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F)
  证明: rfl
-/
lemma Hom.map_mk {W} {X Y : C} (f : LeftFraction W X Y) (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    Hom.map (Hom.mk f) F hF = f.map F hF := rfl

namespace StrictUniversalPropertyFixedTarget

variable (W)

/--
lemma `inverts` / 引理 `inverts`

English:
lemma inverts
  statement: W.IsInvertedBy (Q W)
  proof: fun _ _ s hs =>
inferInstanceAs IsIso (Qiso s hs).hom

中文:
引理 inverts
  结论: W.IsInvertedBy (Q W)
  证明: fun _ _ s hs =>
inferInstanceAs IsIso (Qiso s hs).hom
-/
lemma inverts : W.IsInvertedBy (Q W) := fun _ _ s hs =>
inferInstanceAs IsIso (Qiso s hs).hom

variable {W}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (F : C ⥤ E) (hF : W.IsInvertedBy F)
  body: F.obj X
  map {_ _ : C} f := f.map F hF
  map_id := by
    intro (X : C)
    change (Hom.mk (ofHom W (𝟙 X))).map F hF = _
    rw [Hom.map_mk]; rw [map_ofHom]; rw [F.map_id]
  map_comp := by
    rintro (X Y Z : C) f g
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    obtain ⟨g, rfl⟩ := Hom.mk_surjective

中文:
定义 lift
  签名: (F : C ⥤ E) (hF : W.IsInvertedBy F)
  定义体: F.obj X
  map {_ _ : C} f := f.map F hF
  map_id := by
    intro (X : C)
    change (Hom.mk (ofHom W (𝟙 X))).map F hF = _
    rw [Hom.map_mk]; rw [map_ofHom]; rw [F.map_id]
  map_comp := by
    rintro (X Y Z : C) f g
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    obtain ⟨g, rfl⟩ := Hom.mk_surjective

Depends on / 依赖: F.obj
-/
noncomputable def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) :
    Localization W ⥤ E where
  obj X := F.obj X
  map {_ _ : C} f := f.map F hF
  map_id := by
    intro (X : C)
    change (Hom.mk (ofHom W (𝟙 X))).map F hF = _
    rw [Hom.map_mk]; rw [map_ofHom]; rw [F.map_id]
  map_comp := by
    rintro (X Y Z : C) f g
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    obtain ⟨g, rfl⟩ := Hom.mk_surjective g
    dsimp
    obtain ⟨z, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
      (RightFraction.mk f.s f.hs g.f)
    rw [homMk_comp_homMk f g z fac]; rw [Hom.map_mk]
    dsimp at fac ⊢
    have := hF _ g.hs
    have := hF _ z.hs
    rw [← cancel_mono (F.map g.s)]; rw [assoc]; rw [map_comp_map_s]; rw [← cancel_mono (F.map z.s)]; rw [assoc]; rw [assoc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [map_comp_map_s]; rw [fac]
    dsimp
    rw [F.map_comp]; rw [F.map_comp]; rw [map_comp_map_s_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  given: (F : C ⥤ E) (hF : W.IsInvertedBy F)
  statement: Q W ⋙ lift F hF = F
  proof: Functor.ext (fun _ => rfl) (fun X Y f => by
    dsimp [lift]
    rw [Q_map]; rw [Hom.map_mk]; rw [id_comp]; rw [comp_id]; rw [map_ofHom])

中文:
引理 fac
  条件: (F : C ⥤ E) (hF : W.IsInvertedBy F)
  结论: Q W ⋙ lift F hF = F
  证明: Functor.ext (fun _ => rfl) (fun X Y f => by
    dsimp [lift]
    rw [Q_map]; rw [Hom.map_mk]; rw [id_comp]; rw [comp_id]; rw [map_ofHom])

Depends on / 依赖: Functor, Functor.ext, Hom.map_mk, Q_map, comp_id, id_comp, map_mk, map_ofHom
-/
lemma fac (F : C ⥤ E) (hF : W.IsInvertedBy F) : Q W ⋙ lift F hF = F :=
  Functor.ext (fun _ => rfl) (fun X Y f => by
    dsimp [lift]
    rw [Q_map]; rw [Hom.map_mk]; rw [id_comp]; rw [comp_id]; rw [map_ofHom])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `uniq` / 引理 `uniq`

English:
lemma uniq
  given: (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W ⋙ F₂)
  statement: F₁ = F₂
  proof: Functor.ext (fun X => Functor.congr_obj h X) (by
    rintro (X Y : C) f
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    rw [show Hom.mk f = homMk (mk f.f f.s f.hs) by rfl]; rw [← Q_map_comp_Qinv f.f f.s f.hs]; rw [F₁.map_comp]; rw [F₂.map_comp]; rw [assoc]
    erw [Functor.congr_hom h f.f]
    rw [as

中文:
引理 uniq
  条件: (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W ⋙ F₂)
  结论: F₁ = F₂
  证明: Functor.ext (fun X => Functor.congr_obj h X) (by
    rintro (X Y : C) f
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    rw [show Hom.mk f = homMk (mk f.f f.s f.hs) by rfl]; rw [← Q_map_comp_Qinv f.f f.s f.hs]; rw [F₁.map_comp]; rw [F₂.map_comp]; rw [assoc]
    erw [Functor.congr_hom h f.f]
    rw [as

Depends on / 依赖: Functor, Functor.congr_hom, Functor.congr_obj, Functor.ext, Functor.map_id, Hom.mk, Hom.mk_surjective, Q_map_comp_Qinv, Qiso_hom_inv_id, cancel_epi, congr_hom, congr_obj, f.hs, h.symm, id_comp, inverts, map_comp, map_comp_assoc, map_id, mk_surjective
-/
lemma uniq (F₁ F₂ : Localization W ⥤ E) (h : Q W ⋙ F₁ = Q W ⋙ F₂) : F₁ = F₂ :=
  Functor.ext (fun X => Functor.congr_obj h X) (by
    rintro (X Y : C) f
    obtain ⟨f, rfl⟩ := Hom.mk_surjective f
    rw [show Hom.mk f = homMk (mk f.f f.s f.hs) by rfl]; rw [← Q_map_comp_Qinv f.f f.s f.hs]; rw [F₁.map_comp]; rw [F₂.map_comp]; rw [assoc]
    erw [Functor.congr_hom h f.f]
    rw [assoc]; rw [assoc]
    congr 2
    have := inverts W _ f.hs
    rw [← cancel_epi (F₂.map ((Q W).map f.s))]; rw [← F₂.map_comp_assoc]; rw [Qiso_hom_inv_id]; rw [Functor.map_id]; rw [id_comp]
    erw [Functor.congr_hom h.symm f.s]
    dsimp
    rw [assoc]; rw [assoc]; rw [eqToHom_trans_assoc]; rw [eqToHom_refl]; rw [id_comp]; rw [← F₁.map_comp]; rw [Qiso_hom_inv_id]
    dsimp
    rw [F₁.map_id]; rw [comp_id])

end StrictUniversalPropertyFixedTarget

variable (W)

open StrictUniversalPropertyFixedTarget in
/--
Definition of `strictUniversalPropertyFixedTarget` / `strictUniversalPropertyFixedTarget` 的定义

English:
definition strictUniversalPropertyFixedTarget
  signature: (E : Type*) [Category* E]
  body: inverts W
  lift := lift
  fac := fac
  uniq := uniq

中文:
定义 strictUniversalPropertyFixedTarget
  签名: (E : 类型) [Category* E]
  定义体: inverts W
  lift := lift
  fac := fac
  uniq := uniq

Depends on / 依赖: inverts
-/
noncomputable def strictUniversalPropertyFixedTarget (E : Type*) [Category* E] :
    Localization.StrictUniversalPropertyFixedTarget (Q W) W E where
  inverts := inverts W
  lift := lift
  fac := fac
  uniq := uniq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Q W).IsLocalization W
  body: Functor.IsLocalization.mk' _ _
    (strictUniversalPropertyFixedTarget W _)
    (strictUniversalPropertyFixedTarget W _)

中文:
实例 :
  签名: (Q W).IsLocalization W
  定义体: Functor.IsLocalization.mk' _ _
    (strictUniversalPropertyFixedTarget W _)
    (strictUniversalPropertyFixedTarget W _)

Depends on / 依赖: Functor, Functor.IsLocalization.mk, IsLocalization, strictUniversalPropertyFixedTarget
-/
instance : (Q W).IsLocalization W :=
  Functor.IsLocalization.mk' _ _
    (strictUniversalPropertyFixedTarget W _)
    (strictUniversalPropertyFixedTarget W _)

end

/--
lemma `homMk_eq` / 引理 `homMk_eq`

English:
lemma homMk_eq
  given: {X Y : C} (f : LeftFraction W X Y)
  proof: by
  rw [← Q_map_comp_Qinv f.f f.s f.hs]; rw [← cancel_mono ((Q W).map f.s)]; rw [assoc]; rw [Qiso_inv_hom_id]; rw [comp_id]; rw [map_comp_map_s]

中文:
引理 homMk_eq
  条件: {X Y : C} (f : LeftFraction W X Y)
  证明: by
  rw [← Q_map_comp_Qinv f.f f.s f.hs]; rw [← cancel_mono ((Q W).map f.s)]; rw [assoc]; rw [Qiso_inv_hom_id]; rw [comp_id]; rw [map_comp_map_s]

Depends on / 依赖: Q_map_comp_Qinv, Qiso_inv_hom_id, cancel_mono, comp_id, f.hs, map_comp_map_s
-/
lemma homMk_eq {X Y : C} (f : LeftFraction W X Y) :
    homMk f = f.map (Q W) (Localization.inverts _ W) := by
  rw [← Q_map_comp_Qinv f.f f.s f.hs]; rw [← cancel_mono ((Q W).map f.s)]; rw [assoc]; rw [Qiso_inv_hom_id]; rw [comp_id]; rw [map_comp_map_s]

/--
lemma `map_eq_iff` / 引理 `map_eq_iff`

English:
lemma map_eq_iff
  given: {X Y : C} (f g : LeftFraction W X Y)
  proof: by
  simp only [← Hom.map_mk _ (Q W)]
  constructor
  · intro h
    rw [← homMk_eq_iff_leftFractionRel]; rw [homMk_eq]; rw [homMk_eq]
    exact h
  · intro h
    congr 1
    exact Quot.sound h

中文:
引理 map_eq_iff
  条件: {X Y : C} (f g : LeftFraction W X Y)
  证明: by
  simp only [← Hom.map_mk _ (Q W)]
  constructor
  · intro h
    rw [← homMk_eq_iff_leftFractionRel]; rw [homMk_eq]; rw [homMk_eq]
    exact h
  · intro h
    congr 1
    exact Quot.sound h

Depends on / 依赖: Hom.map_mk, Quot.sound, homMk_eq, homMk_eq_iff_leftFractionRel, map_mk
-/
lemma map_eq_iff {X Y : C} (f g : LeftFraction W X Y) :
    f.map (LeftFraction.Localization.Q W) (Localization.inverts _ _) =
        g.map (LeftFraction.Localization.Q W) (Localization.inverts _ _) ↔
      LeftFractionRel f g := by
  simp only [← Hom.map_mk _ (Q W)]
  constructor
  · intro h
    rw [← homMk_eq_iff_leftFractionRel]; rw [homMk_eq]; rw [homMk_eq]
    exact h
  · intro h
    congr 1
    exact Quot.sound h

end Localization

section

/--
lemma `map_eq` / 引理 `map_eq`

English:
lemma map_eq
  given: {W} {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) [L.IsLocalization W]
  proof: rfl

中文:
引理 map_eq
  条件: {W} {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) [L.IsLocalization W]
  证明: rfl
-/
lemma map_eq {W} {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) [L.IsLocalization W] :
    φ.map L (Localization.inverts L W) =
      L.map φ.f ≫ (Localization.isoOfHom L W φ.s φ.hs).inv := rfl

/--
lemma `map_compatibility` / 引理 `map_compatibility`

English:
lemma map_compatibility
  statement: {W} {X Y : C}
  proof: by
  let e := Localization.compUniqFunctor L₁ L₂ W
  rw [← cancel_mono (e.hom.app Y)]; rw [assoc]; rw [assoc]; rw [e.inv_hom_id_app]; rw [comp_id]; rw [← cancel_mono (L₂.map φ.s)]; rw [assoc]; rw [assoc]; rw [map_comp_map_s]; rw [← e.hom.naturality]
  simpa [← Functor.map_comp_assoc, map_comp_map_s]

中文:
引理 map_compatibility
  结论: {W} {X Y : C}
  证明: by
  let e := Localization.compUniqFunctor L₁ L₂ W
  rw [← cancel_mono (e.hom.app Y)]; rw [assoc]; rw [assoc]; rw [e.inv_hom_id_app]; rw [comp_id]; rw [← cancel_mono (L₂.map φ.s)]; rw [assoc]; rw [assoc]; rw [map_comp_map_s]; rw [← e.hom.naturality]
  simpa [← Functor.map_comp_assoc, map_comp_map_s]

Depends on / 依赖: Functor, Functor.map_comp_assoc, Localization, Localization.compUniqFunctor, cancel_mono, compUniqFunctor, comp_id, e.hom.app, e.hom.naturality, e.inv_hom_id_app, inv_hom_id_app, map_comp_assoc, map_comp_map_s, naturality
-/
lemma map_compatibility {W} {X Y : C}
    (φ : W.LeftFraction X Y) {E : Type*} [Category* E]
    (L₁ : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLocalization W] :
    (Localization.uniq L₁ L₂ W).functor.map (φ.map L₁ (Localization.inverts L₁ W)) =
      (Localization.compUniqFunctor L₁ L₂ W).hom.app X ≫
        φ.map L₂ (Localization.inverts L₂ W) ≫
        (Localization.compUniqFunctor L₁ L₂ W).inv.app Y := by
  let e := Localization.compUniqFunctor L₁ L₂ W
  rw [← cancel_mono (e.hom.app Y)]; rw [assoc]; rw [assoc]; rw [e.inv_hom_id_app]; rw [comp_id]; rw [← cancel_mono (L₂.map φ.s)]; rw [assoc]; rw [assoc]; rw [map_comp_map_s]; rw [← e.hom.naturality]
  simpa [← Functor.map_comp_assoc, map_comp_map_s] using e.hom.naturality φ.f

/--
lemma `map_eq_of_map_eq` / 引理 `map_eq_of_map_eq`

English:
lemma map_eq_of_map_eq
  statement: {W} {X Y : C}
  proof: by
  apply (Localization.uniq L₂ L₁ W).functor.map_injective
  rw [map_compatibility φ₁ L₂ L₁]; rw [map_compatibility φ₂ L₂ L₁]; rw [h]

中文:
引理 map_eq_of_map_eq
  结论: {W} {X Y : C}
  证明: by
  apply (Localization.uniq L₂ L₁ W).functor.map_injective
  rw [map_compatibility φ₁ L₂ L₁]; rw [map_compatibility φ₂ L₂ L₁]; rw [h]

Depends on / 依赖: Localization, Localization.uniq, functor, functor.map_injective, map_compatibility, map_injective
-/
lemma map_eq_of_map_eq {W} {X Y : C}
    (φ₁ φ₂ : W.LeftFraction X Y) {E : Type*} [Category* E]
    (L₁ : C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLocalization W]
    (h : φ₁.map L₁ (Localization.inverts L₁ W) = φ₂.map L₁ (Localization.inverts L₁ W)) :
    φ₁.map L₂ (Localization.inverts L₂ W) = φ₂.map L₂ (Localization.inverts L₂ W) := by
  apply (Localization.uniq L₂ L₁ W).functor.map_injective
  rw [map_compatibility φ₁ L₂ L₁]; rw [map_compatibility φ₂ L₂ L₁]; rw [h]

/--
lemma `map_comp_map_eq_map` / 引理 `map_comp_map_eq_map`

English:
lemma map_comp_map_eq_map
  statement: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  proof: by
  have : IsIso (L.map (z₂.s ≫ z₃.s)) := by
    rw [L.map_comp]
    infer_instance
  dsimp [LeftFraction.comp₀]
  rw [← cancel_mono (L.map (z₂.s ≫ z₃.s))]; rw [map_comp_map_s]; rw [L.map_comp]; rw [assoc]; rw [map_comp_map_s_assoc]; rw [← L.map_comp]; rw [h₃]; rw [L.map_comp]; rw [map_comp_map_s_a

中文:
引理 map_comp_map_eq_map
  结论: {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
  证明: by
  have : IsIso (L.map (z₂.s ≫ z₃.s)) := by
    rw [L.map_comp]
    infer_instance
  dsimp [LeftFraction.comp₀]
  rw [← cancel_mono (L.map (z₂.s ≫ z₃.s))]; rw [map_comp_map_s]; rw [L.map_comp]; rw [assoc]; rw [map_comp_map_s_assoc]; rw [← L.map_comp]; rw [h₃]; rw [L.map_comp]; rw [map_comp_map_s_a

Depends on / 依赖: L.map, L.map_comp, LeftFraction, LeftFraction.comp, cancel_mono, infer_instance, map_comp, map_comp_map_s, map_comp_map_s_assoc
-/
lemma map_comp_map_eq_map {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f)
    (L : C ⥤ D) [L.IsLocalization W] :
    z₁.map L (Localization.inverts L W) ≫ z₂.map L (Localization.inverts L W) =
      (z₁.comp₀ z₂ z₃).map L (Localization.inverts L W) := by
  have : IsIso (L.map (z₂.s ≫ z₃.s)) := by
    rw [L.map_comp]
    infer_instance
  dsimp [LeftFraction.comp₀]
  rw [← cancel_mono (L.map (z₂.s ≫ z₃.s))]; rw [map_comp_map_s]; rw [L.map_comp]; rw [assoc]; rw [map_comp_map_s_assoc]; rw [← L.map_comp]; rw [h₃]; rw [L.map_comp]; rw [map_comp_map_s_assoc]; rw [L.map_comp]

end

end LeftFraction

end

end MorphismProperty

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

section

variable [W.HasLeftCalculusOfFractions]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Localization.exists_leftFraction` / 引理 `Localization.exists_leftFraction`

English:
lemma Localization.exists_leftFraction
  given: {X Y : C} (f : L.obj X ⟶ L.obj Y)
  proof: by
  let E := Localization.uniq (MorphismProperty.LeftFraction.Localization.Q W) L W
  let e : _ ⋙ E.functor ≅ L := Localization.compUniqFunctor _ _ _
  obtain ⟨f', rfl⟩ : exists (f' : E.functor.obj X ⟶ E.functor.obj Y),
      f = e.inv.app _ ≫ f' ≫ e.hom.app _ := ⟨e.hom.app _ ≫ f ≫ e.inv.app _, by 

中文:
引理 Localization.exists_leftFraction
  条件: {X Y : C} (f : L.obj X ⟶ L.obj Y)
  证明: by
  let E := Localization.uniq (MorphismProperty.LeftFraction.Localization.Q W) L W
  let e : _ ⋙ E.functor ≅ L := Localization.compUniqFunctor _ _ _
  obtain ⟨f', rfl⟩ : exists (f' : E.functor.obj X ⟶ E.functor.obj Y),
      f = e.inv.app _ ≫ f' ≫ e.hom.app _ := ⟨e.hom.app _ ≫ f ≫ e.inv.app _, by 

Depends on / 依赖: E.functor, E.functor.map_surjective, E.functor.obj, LeftFraction, Localization, Localization.compUniqFunctor, Localization.uniq, MorphismProperty, MorphismProperty.LeftFraction.Localization.Hom.mk_surjective, MorphismProperty.LeftFraction.Localization.Q, MorphismProperty.LeftFraction.Localization.homMk_eq_hom_, compUniqFunctor, e.hom.app, e.inv.app, functor, homMk_eq_hom_, map_surjective, mk_surjective
-/
lemma Localization.exists_leftFraction {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    exists (φ : W.LeftFraction X Y), f = φ.map L (Localization.inverts L W) := by
  let E := Localization.uniq (MorphismProperty.LeftFraction.Localization.Q W) L W
  let e : _ ⋙ E.functor ≅ L := Localization.compUniqFunctor _ _ _
  obtain ⟨f', rfl⟩ : exists (f' : E.functor.obj X ⟶ E.functor.obj Y),
      f = e.inv.app _ ≫ f' ≫ e.hom.app _ := ⟨e.hom.app _ ≫ f ≫ e.inv.app _, by simp⟩
  obtain ⟨g, rfl⟩ := E.functor.map_surjective f'
  obtain ⟨g, rfl⟩ := MorphismProperty.LeftFraction.Localization.Hom.mk_surjective g
  refine ⟨g, ?_⟩
  rw [← MorphismProperty.LeftFraction.Localization.homMk_eq_hom_mk]; rw [MorphismProperty.LeftFraction.Localization.homMk_eq g]; rw [g.map_compatibility (MorphismProperty.LeftFraction.Localization.Q W) L]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app]; rw [comp_id]; rw [Iso.inv_hom_id_app_assoc]

/--
lemma `MorphismProperty.LeftFraction.map_eq_iff` / 引理 `MorphismProperty.LeftFraction.map_eq_iff`

English:
lemma MorphismProperty.LeftFraction.map_eq_iff
  proof: by
  constructor
  · intro h
    rw [← MorphismProperty.LeftFraction.Localization.map_eq_iff]
    apply map_eq_of_map_eq _ _ _ _ h
  · intro h
    simp only [← Localization.Hom.map_mk _ L (Localization.inverts _ _)]
    congr 1
    exact Quot.sound h

中文:
引理 MorphismProperty.LeftFraction.map_eq_iff
  证明: by
  constructor
  · intro h
    rw [← MorphismProperty.LeftFraction.Localization.map_eq_iff]
    apply map_eq_of_map_eq _ _ _ _ h
  · intro h
    simp only [← Localization.Hom.map_mk _ L (Localization.inverts _ _)]
    congr 1
    exact Quot.sound h

Depends on / 依赖: LeftFraction, Localization, Localization.Hom.map_mk, Localization.inverts, MorphismProperty, MorphismProperty.LeftFraction.Localization.map_eq_iff, Quot.sound, inverts, map_eq_iff, map_eq_of_map_eq, map_mk
-/
lemma MorphismProperty.LeftFraction.map_eq_iff
    {X Y : C} (φ ψ : W.LeftFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      LeftFractionRel φ ψ := by
  constructor
  · intro h
    rw [← MorphismProperty.LeftFraction.Localization.map_eq_iff]
    apply map_eq_of_map_eq _ _ _ _ h
  · intro h
    simp only [← Localization.Hom.map_mk _ L (Localization.inverts _ _)]
    congr 1
    exact Quot.sound h

set_option backward.defeqAttrib.useBackward true in
/--
lemma `MorphismProperty.map_eq_iff_postcomp` / 引理 `MorphismProperty.map_eq_iff_postcomp`

English:
lemma MorphismProperty.map_eq_iff_postcomp
  given: {X Y : C} (f₁ f₂ : X ⟶ Y)
  proof: by
  constructor
  · intro h
    rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [LeftFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs, f

中文:
引理 MorphismProperty.map_eq_iff_postcomp
  条件: {X Y : C} (f₁ f₂ : X ⟶ Y)
  证明: by
  constructor
  · intro h
    rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [LeftFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs, f

Depends on / 依赖: L.map_comp, LeftFraction, LeftFraction.map_eq_iff, LeftFraction.map_ofHom, Localization, Localization.inverts, Localization.isoOfHom, Localization.isoOfHom_hom, cancel_mono, inverts, isoOfHom, isoOfHom_hom, map_comp, map_eq_iff, map_ofHom
-/
lemma MorphismProperty.map_eq_iff_postcomp {X Y : C} (f₁ f₂ : X ⟶ Y) :
    L.map f₁ = L.map f₂ ↔ exists (Z : C) (s : Y ⟶ Z) (_ : W s), f₁ ≫ s = f₂ ≫ s := by
  constructor
  · intro h
    rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [← LeftFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [LeftFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs, fac⟩
    simp only [← cancel_mono (Localization.isoOfHom L W s hs).hom,
      Localization.isoOfHom_hom, ← L.map_comp, fac]

set_option backward.defeqAttrib.useBackward true in
include W in
/--
lemma `Localization.essSurj_mapArrow` / 引理 `Localization.essSurj_mapArrow`

English:
lemma Localization.essSurj_mapArrow
  proof: by
    have := Localization.essSurj L W
    obtain ⟨X, ⟨eX⟩⟩ : exists (X : C), Nonempty (L.obj X ≅ f.left) :=
      ⟨_, ⟨L.objObjPreimageIso f.left⟩⟩
    obtain ⟨Y, ⟨eY⟩⟩ : exists (Y : C), Nonempty (L.obj Y ≅ f.right) :=
      ⟨_, ⟨L.objObjPreimageIso f.right⟩⟩
    obtain ⟨φ, hφ⟩ := Localization.exi

中文:
引理 Localization.essSurj_mapArrow
  证明: by
    have := Localization.essSurj L W
    obtain ⟨X, ⟨eX⟩⟩ : exists (X : C), Nonempty (L.obj X ≅ f.left) :=
      ⟨_, ⟨L.objObjPreimageIso f.left⟩⟩
    obtain ⟨Y, ⟨eY⟩⟩ : exists (Y : C), Nonempty (L.obj Y ≅ f.right) :=
      ⟨_, ⟨L.objObjPreimageIso f.right⟩⟩
    obtain ⟨φ, hφ⟩ := Localization.exi

Depends on / 依赖: Arrow.isoMk, Arrow.mk, Iso.hom_inv_id_assoc, Iso.symm, L.obj, L.objObjPreimageIso, Localization, Localization.essSurj, Localization.exists_leftFraction, Localization.isoOfHom, Nonempty, cancel_epi, eX.hom, eX.symm, eY.inv, eY.symm, essSurj, exists_leftFraction, f.hom, f.left
-/
lemma Localization.essSurj_mapArrow :
    L.mapArrow.EssSurj where
  mem_essImage f := by
    have := Localization.essSurj L W
    obtain ⟨X, ⟨eX⟩⟩ : exists (X : C), Nonempty (L.obj X ≅ f.left) :=
      ⟨_, ⟨L.objObjPreimageIso f.left⟩⟩
    obtain ⟨Y, ⟨eY⟩⟩ : exists (Y : C), Nonempty (L.obj Y ≅ f.right) :=
      ⟨_, ⟨L.objObjPreimageIso f.right⟩⟩
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L W (eX.hom ≫ f.hom ≫ eY.inv)
    refine ⟨Arrow.mk φ.f, ⟨Iso.symm ?_⟩⟩
    refine Arrow.isoMk eX.symm (eY.symm ≪≫ Localization.isoOfHom L W φ.s φ.hs) ?_
    dsimp
    simp only [← cancel_epi eX.hom, Iso.hom_inv_id_assoc, reassoc_of% hφ,
      MorphismProperty.LeftFraction.map_comp_map_s]

end


namespace MorphismProperty

variable {W}

/-- The right fraction in the opposite category corresponding to a left fraction. -/
@[simps]
/--
Definition of `LeftFraction.op` / `LeftFraction.op` 的定义

English:
definition LeftFraction.op
  signature: {X Y : C} (φ : W.LeftFraction X Y)
  body: Opposite.op φ.Y'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

中文:
定义 LeftFraction.op
  签名: {X Y : C} (φ : W.LeftFraction X Y)
  定义体: Opposite.op φ.Y'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

Depends on / 依赖: Opposite, Opposite.op
-/
def LeftFraction.op {X Y : C} (φ : W.LeftFraction X Y) :
    W.op.RightFraction (Opposite.op Y) (Opposite.op X) where
  X' := Opposite.op φ.Y'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

/-- The left fraction in the opposite category corresponding to a right fraction. -/
@[simps]
/--
Definition of `RightFraction.op` / `RightFraction.op` 的定义

English:
definition RightFraction.op
  signature: {X Y : C} (φ : W.RightFraction X Y)
  body: Opposite.op φ.X'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

中文:
定义 RightFraction.op
  签名: {X Y : C} (φ : W.RightFraction X Y)
  定义体: Opposite.op φ.X'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

Depends on / 依赖: Opposite, Opposite.op
-/
def RightFraction.op {X Y : C} (φ : W.RightFraction X Y) :
    W.op.LeftFraction (Opposite.op Y) (Opposite.op X) where
  Y' := Opposite.op φ.X'
  s := φ.s.op
  hs := φ.hs
  f := φ.f.op

/-- The right fraction corresponding to a left fraction in the opposite category. -/
@[simps]
/--
Definition of `LeftFraction.unop` / `LeftFraction.unop` 的定义

English:
definition LeftFraction.unop
  signature: {W : MorphismProperty Cᵒᵖ}
  body: Opposite.unop φ.Y'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

中文:
定义 LeftFraction.unop
  签名: {W : Morphism命题erty Cᵒᵖ}
  定义体: Opposite.unop φ.Y'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

Depends on / 依赖: Opposite, Opposite.unop
-/
def LeftFraction.unop {W : MorphismProperty Cᵒᵖ}
    {X Y : Cᵒᵖ} (φ : W.LeftFraction X Y) :
    W.unop.RightFraction (Opposite.unop Y) (Opposite.unop X) where
  X' := Opposite.unop φ.Y'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

/-- The left fraction corresponding to a right fraction in the opposite category. -/
@[simps]
/--
Definition of `RightFraction.unop` / `RightFraction.unop` 的定义

English:
definition RightFraction.unop
  signature: {W : MorphismProperty Cᵒᵖ}
  body: Opposite.unop φ.X'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

中文:
定义 RightFraction.unop
  签名: {W : Morphism命题erty Cᵒᵖ}
  定义体: Opposite.unop φ.X'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

Depends on / 依赖: Opposite, Opposite.unop
-/
def RightFraction.unop {W : MorphismProperty Cᵒᵖ}
    {X Y : Cᵒᵖ} (φ : W.RightFraction X Y) :
    W.unop.LeftFraction (Opposite.unop Y) (Opposite.unop X) where
  Y' := Opposite.unop φ.X'
  s := φ.s.unop
  hs := φ.hs
  f := φ.f.unop

set_option backward.defeqAttrib.useBackward true in
/--
lemma `RightFraction.op_map` / 引理 `RightFraction.op_map`

English:
lemma RightFraction.op_map
  proof: by
  dsimp [map, LeftFraction.map]
  rw [op_inv]

中文:
引理 RightFraction.op_map
  证明: by
  dsimp [map, LeftFraction.map]
  rw [op_inv]

Depends on / 依赖: LeftFraction, LeftFraction.map, op_inv
-/
lemma RightFraction.op_map
    {X Y : C} (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (φ.map L hL).op = φ.op.map L.op hL.op := by
  dsimp [map, LeftFraction.map]
  rw [op_inv]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `LeftFraction.op_map` / 引理 `LeftFraction.op_map`

English:
lemma LeftFraction.op_map
  proof: by
  dsimp [map, RightFraction.map]
  rw [op_inv]

中文:
引理 LeftFraction.op_map
  证明: by
  dsimp [map, RightFraction.map]
  rw [op_inv]

Depends on / 依赖: RightFraction, RightFraction.map, op_inv
-/
lemma LeftFraction.op_map
    {X Y : C} (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (φ.map L hL).op = φ.op.map L.op hL.op := by
  dsimp [map, RightFraction.map]
  rw [op_inv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : W.HasLeftCalculusOfFractions] : W.op.HasRightCalculusOfFractions where
  body: by
    obtain ⟨ψ, eq⟩ := h.exists_leftFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    obtain ⟨X', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op X', t.op, ht, Quiver.Hom.unop_inj fac⟩

中文:
实例 [h
  签名: : W.HasLeftCalculusOfFractions] : W.op.HasRightCalculusOfFractions where
  定义体: by
    obtain ⟨ψ, eq⟩ := h.exists_leftFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    obtain ⟨X', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op X', t.op, ht, Quiver.Hom.unop_inj fac⟩

Depends on / 依赖: Opposite, Opposite.op, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, exists_leftFraction, h.exists_leftFraction, h.ext, op_inj, s.unop, t.op, unop_inj
-/
instance [h : W.HasLeftCalculusOfFractions] : W.op.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_leftFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    obtain ⟨X', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op X', t.op, ht, Quiver.Hom.unop_inj fac⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : W.HasRightCalculusOfFractions] : W.op.HasLeftCalculusOfFractions where
  body: by
    obtain ⟨ψ, eq⟩ := h.exists_rightFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X' X Y f₁ f₂ s hs eq := by
    obtain ⟨Y', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op Y', t.op, ht, Quiver.Hom.unop_inj fac⟩

中文:
实例 [h
  签名: : W.HasRightCalculusOfFractions] : W.op.HasLeftCalculusOfFractions where
  定义体: by
    obtain ⟨ψ, eq⟩ := h.exists_rightFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X' X Y f₁ f₂ s hs eq := by
    obtain ⟨Y', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op Y', t.op, ht, Quiver.Hom.unop_inj fac⟩

Depends on / 依赖: Opposite, Opposite.op, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, exists_rightFraction, h.exists_rightFraction, h.ext, op_inj, s.unop, t.op, unop_inj
-/
instance [h : W.HasRightCalculusOfFractions] : W.op.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_rightFraction φ.unop
    exact ⟨ψ.op, Quiver.Hom.unop_inj eq⟩
  ext X' X Y f₁ f₂ s hs eq := by
    obtain ⟨Y', t, ht, fac⟩ := h.ext f₁.unop f₂.unop s.unop hs (Quiver.Hom.op_inj eq)
    exact ⟨Opposite.op Y', t.op, ht, Quiver.Hom.unop_inj fac⟩

instance (W : MorphismProperty Cᵒᵖ) [h : W.HasLeftCalculusOfFractions] :
    W.unop.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_leftFraction φ.op
    exact ⟨ψ.unop, Quiver.Hom.op_inj eq⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    obtain ⟨X', t, ht, fac⟩ := h.ext f₁.op f₂.op s.op hs (Quiver.Hom.unop_inj eq)
    exact ⟨Opposite.unop X', t.unop, ht, Quiver.Hom.op_inj fac⟩

instance (W : MorphismProperty Cᵒᵖ) [h : W.HasRightCalculusOfFractions] :
    W.unop.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨ψ, eq⟩ := h.exists_rightFraction φ.op
    exact ⟨ψ.unop, Quiver.Hom.op_inj eq⟩
  ext X' X Y f₁ f₂ s hs eq := by
    obtain ⟨Y', t, ht, fac⟩ := h.ext f₁.op f₂.op s.op hs (Quiver.Hom.unop_inj eq)
    exact ⟨Opposite.unop Y', t.unop, ht, Quiver.Hom.op_inj fac⟩

/--
Definition of `RightFractionRel` / `RightFractionRel` 的定义

English:
definition RightFractionRel
  signature: {X Y : C} (z₁ z₂ : W.RightFraction X Y)
  body: exists (Z : C) (t₁ : Z ⟶ z₁.X') (t₂ : Z ⟶ z₂.X') (_ : t₁ ≫ z₁.s = t₂ ≫ z₂.s)
    (_ : t₁ ≫ z₁.f = t₂ ≫ z₂.f), W (t₁ ≫ z₁.s)

中文:
定义 RightFractionRel
  签名: {X Y : C} (z₁ z₂ : W.RightFraction X Y)
  定义体: exists (Z : C) (t₁ : Z ⟶ z₁.X') (t₂ : Z ⟶ z₂.X') (_ : t₁ ≫ z₁.s = t₂ ≫ z₂.s)
    (_ : t₁ ≫ z₁.f = t₂ ≫ z₂.f), W (t₁ ≫ z₁.s)
-/
def RightFractionRel {X Y : C} (z₁ z₂ : W.RightFraction X Y) : Prop :=
  exists (Z : C) (t₁ : Z ⟶ z₁.X') (t₂ : Z ⟶ z₂.X') (_ : t₁ ≫ z₁.s = t₂ ≫ z₂.s)
    (_ : t₁ ≫ z₁.f = t₂ ≫ z₂.f), W (t₁ ≫ z₁.s)

/--
lemma `RightFractionRel.op` / 引理 `RightFractionRel.op`

English:
lemma RightFractionRel.op
  statement: {X Y : C} {z₁ z₂ : W.RightFraction X Y}
  proof: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩

中文:
引理 RightFractionRel.op
  结论: {X Y : C} {z₁ z₂ : W.RightFraction X Y}
  证明: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩

Depends on / 依赖: Opposite, Opposite.op, Quiver, Quiver.Hom.unop_inj, unop_inj
-/
lemma RightFractionRel.op {X Y : C} {z₁ z₂ : W.RightFraction X Y}
    (h : RightFractionRel z₁ z₂) : LeftFractionRel z₁.op z₂.op := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩

/--
lemma `RightFractionRel.unop` / 引理 `RightFractionRel.unop`

English:
lemma RightFractionRel.unop
  statement: {W : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}
  proof: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩

中文:
引理 RightFractionRel.unop
  结论: {W : Morphism命题erty Cᵒᵖ} {X Y : Cᵒᵖ}
  证明: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩

Depends on / 依赖: Opposite, Opposite.unop, Quiver, Quiver.Hom.op_inj, op_inj
-/
lemma RightFractionRel.unop {W : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}
    {z₁ z₂ : W.RightFraction X Y}
    (h : RightFractionRel z₁ z₂) : LeftFractionRel z₁.unop z₂.unop := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩

/--
lemma `LeftFractionRel.op` / 引理 `LeftFractionRel.op`

English:
lemma LeftFractionRel.op
  statement: {X Y : C} {z₁ z₂ : W.LeftFraction X Y}
  proof: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩

中文:
引理 LeftFractionRel.op
  结论: {X Y : C} {z₁ z₂ : W.LeftFraction X Y}
  证明: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩

Depends on / 依赖: Opposite, Opposite.op, Quiver, Quiver.Hom.unop_inj, unop_inj
-/
lemma LeftFractionRel.op {X Y : C} {z₁ z₂ : W.LeftFraction X Y}
    (h : LeftFractionRel z₁ z₂) : RightFractionRel z₁.op z₂.op := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.op Z, t₁.op, t₂.op, Quiver.Hom.unop_inj hs,
    Quiver.Hom.unop_inj hf, ht⟩

/--
lemma `LeftFractionRel.unop` / 引理 `LeftFractionRel.unop`

English:
lemma LeftFractionRel.unop
  statement: {W : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}
  proof: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩

中文:
引理 LeftFractionRel.unop
  结论: {W : Morphism命题erty Cᵒᵖ} {X Y : Cᵒᵖ}
  证明: by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩

Depends on / 依赖: Opposite, Opposite.unop, Quiver, Quiver.Hom.op_inj, op_inj
-/
lemma LeftFractionRel.unop {W : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ}
    {z₁ z₂ : W.LeftFraction X Y}
    (h : LeftFractionRel z₁ z₂) : RightFractionRel z₁.unop z₂.unop := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ := h
  exact ⟨Opposite.unop Z, t₁.unop, t₂.unop, Quiver.Hom.op_inj hs,
    Quiver.Hom.op_inj hf, ht⟩

/--
lemma `leftFractionRel_op_iff` / 引理 `leftFractionRel_op_iff`

English:
lemma leftFractionRel_op_iff
  proof: ⟨fun h => h.unop, fun h => h.op⟩

中文:
引理 leftFractionRel_op_iff
  证明: ⟨fun h => h.unop, fun h => h.op⟩

Depends on / 依赖: h.op, h.unop
-/
lemma leftFractionRel_op_iff
    {X Y : C} (z₁ z₂ : W.RightFraction X Y) :
    LeftFractionRel z₁.op z₂.op ↔ RightFractionRel z₁ z₂ :=
  ⟨fun h => h.unop, fun h => h.op⟩

/--
lemma `rightFractionRel_op_iff` / 引理 `rightFractionRel_op_iff`

English:
lemma rightFractionRel_op_iff
  proof: ⟨fun h => h.unop, fun h => h.op⟩

中文:
引理 rightFractionRel_op_iff
  证明: ⟨fun h => h.unop, fun h => h.op⟩

Depends on / 依赖: h.op, h.unop
-/
lemma rightFractionRel_op_iff
    {X Y : C} (z₁ z₂ : W.LeftFraction X Y) :
    RightFractionRel z₁.op z₂.op ↔ LeftFractionRel z₁ z₂ :=
  ⟨fun h => h.unop, fun h => h.op⟩

namespace RightFractionRel

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: {X Y : C} (z : W.RightFraction X Y)
  statement: RightFractionRel z z
  proof: (LeftFractionRel.refl z.op).unop

中文:
引理 refl
  条件: {X Y : C} (z : W.RightFraction X Y)
  结论: RightFractionRel z z
  证明: (LeftFractionRel.refl z.op).unop

Depends on / 依赖: LeftFractionRel, LeftFractionRel.refl, z.op
-/
lemma refl {X Y : C} (z : W.RightFraction X Y) : RightFractionRel z z :=
  (LeftFractionRel.refl z.op).unop

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: {X Y : C} {z₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂)
  proof: h.op.symm.unop

中文:
引理 symm
  条件: {X Y : C} {z₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂)
  证明: h.op.symm.unop

Depends on / 依赖: h.op.symm.unop
-/
lemma symm {X Y : C} {z₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂) :
    RightFractionRel z₂ z₁ :=
  h.op.symm.unop

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: {X Y : C} {z₁ z₂ z₃ : W.RightFraction X Y}
  proof: (h₁₂.op.trans h₂₃.op).unop

中文:
引理 trans
  结论: {X Y : C} {z₁ z₂ z₃ : W.RightFraction X Y}
  证明: (h₁₂.op.trans h₂₃.op).unop

Depends on / 依赖: op.trans
-/
lemma trans {X Y : C} {z₁ z₂ z₃ : W.RightFraction X Y}
    [HasRightCalculusOfFractions W]
    (h₁₂ : RightFractionRel z₁ z₂) (h₂₃ : RightFractionRel z₂ z₃) :
    RightFractionRel z₁ z₃ :=
  (h₁₂.op.trans h₂₃.op).unop

end RightFractionRel

/--
lemma `equivalenceRightFractionRel` / 引理 `equivalenceRightFractionRel`

English:
lemma equivalenceRightFractionRel
  given: (X Y : C) [HasRightCalculusOfFractions W]
  proof: RightFractionRel.refl
  symm := RightFractionRel.symm
  trans := RightFractionRel.trans

中文:
引理 equivalenceRightFractionRel
  条件: (X Y : C) [HasRightCalculusOfFractions W]
  证明: RightFractionRel.refl
  symm := RightFractionRel.symm
  trans := RightFractionRel.trans

Depends on / 依赖: RightFractionRel, RightFractionRel.refl
-/
lemma equivalenceRightFractionRel (X Y : C) [HasRightCalculusOfFractions W] :
    @_root_.Equivalence (W.RightFraction X Y) RightFractionRel where
  refl := RightFractionRel.refl
  symm := RightFractionRel.symm
  trans := RightFractionRel.trans

end MorphismProperty

section

variable [W.HasRightCalculusOfFractions]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Localization.exists_rightFraction` / 引理 `Localization.exists_rightFraction`

English:
lemma Localization.exists_rightFraction
  given: {X Y : C} (f : L.obj X ⟶ L.obj Y)
  proof: by
  obtain ⟨φ, eq⟩ := Localization.exists_leftFraction L.op W.op f.op
  refine ⟨φ.unop, Quiver.Hom.op_inj ?_⟩
  rw [eq]; rw [MorphismProperty.RightFraction.op_map]
  rfl

中文:
引理 Localization.exists_rightFraction
  条件: {X Y : C} (f : L.obj X ⟶ L.obj Y)
  证明: by
  obtain ⟨φ, eq⟩ := Localization.exists_leftFraction L.op W.op f.op
  refine ⟨φ.unop, Quiver.Hom.op_inj ?_⟩
  rw [eq]; rw [MorphismProperty.RightFraction.op_map]
  rfl

Depends on / 依赖: L.op, Localization, Localization.exists_leftFraction, MorphismProperty, MorphismProperty.RightFraction.op_map, Quiver, Quiver.Hom.op_inj, RightFraction, W.op, exists_leftFraction, f.op, op_inj, op_map
-/
lemma Localization.exists_rightFraction {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    exists (φ : W.RightFraction X Y), f = φ.map L (Localization.inverts L W) := by
  obtain ⟨φ, eq⟩ := Localization.exists_leftFraction L.op W.op f.op
  refine ⟨φ.unop, Quiver.Hom.op_inj ?_⟩
  rw [eq]; rw [MorphismProperty.RightFraction.op_map]
  rfl

/--
lemma `MorphismProperty.RightFraction.map_eq_iff` / 引理 `MorphismProperty.RightFraction.map_eq_iff`

English:
lemma MorphismProperty.RightFraction.map_eq_iff
  proof: by
  rw [← leftFractionRel_op_iff]; rw [← LeftFraction.map_eq_iff L.op W.op φ.op ψ.op]; rw [← φ.op_map L (Localization.inverts _ _)]; rw [← ψ.op_map L (Localization.inverts _ _)]
  constructor
  · apply Quiver.Hom.unop_inj
  · apply Quiver.Hom.op_inj

中文:
引理 MorphismProperty.RightFraction.map_eq_iff
  证明: by
  rw [← leftFractionRel_op_iff]; rw [← LeftFraction.map_eq_iff L.op W.op φ.op ψ.op]; rw [← φ.op_map L (Localization.inverts _ _)]; rw [← ψ.op_map L (Localization.inverts _ _)]
  constructor
  · apply Quiver.Hom.unop_inj
  · apply Quiver.Hom.op_inj

Depends on / 依赖: L.op, LeftFraction, LeftFraction.map_eq_iff, Localization, Localization.inverts, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, W.op, inverts, leftFractionRel_op_iff, map_eq_iff, op_inj, op_map, unop_inj
-/
lemma MorphismProperty.RightFraction.map_eq_iff
    {X Y : C} (φ ψ : W.RightFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      RightFractionRel φ ψ := by
  rw [← leftFractionRel_op_iff]; rw [← LeftFraction.map_eq_iff L.op W.op φ.op ψ.op]; rw [← φ.op_map L (Localization.inverts _ _)]; rw [← ψ.op_map L (Localization.inverts _ _)]
  constructor
  · apply Quiver.Hom.unop_inj
  · apply Quiver.Hom.op_inj

set_option backward.defeqAttrib.useBackward true in
/--
lemma `MorphismProperty.map_eq_iff_precomp` / 引理 `MorphismProperty.map_eq_iff_precomp`

English:
lemma MorphismProperty.map_eq_iff_precomp
  given: {Y Z : C} (f₁ f₂ : Y ⟶ Z)
  proof: by
  constructor
  · intro h
    rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [RightFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs

中文:
引理 MorphismProperty.map_eq_iff_precomp
  条件: {Y Z : C} (f₁ f₂ : Y ⟶ Z)
  证明: by
  constructor
  · intro h
    rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [RightFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs

Depends on / 依赖: L.map_comp, Localization, Localization.inverts, Localization.isoOfHom, Localization.isoOfHom_hom, RightFraction, RightFraction.map_eq_iff, RightFraction.map_ofHom, cancel_epi, inverts, isoOfHom, isoOfHom_hom, map_comp, map_eq_iff, map_ofHom
-/
lemma MorphismProperty.map_eq_iff_precomp {Y Z : C} (f₁ f₂ : Y ⟶ Z) :
    L.map f₁ = L.map f₂ ↔ exists (X : C) (s : X ⟶ Y) (_ : W s), s ≫ f₁ = s ≫ f₂ := by
  constructor
  · intro h
    rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [← RightFraction.map_ofHom W _ L (Localization.inverts _ _)]; rw [RightFraction.map_eq_iff] at h
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    dsimp at t₁ t₂ hst hft ht
    grind
  · rintro ⟨Z, s, hs, fac⟩
    simp only [← cancel_epi (Localization.isoOfHom L W s hs).hom,
      Localization.isoOfHom_hom, ← L.map_comp, fac]

include W in
/--
lemma `Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions` / 引理 `Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions`

English:
lemma Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
  proof: by
    have := Localization.essSurj_mapArrow L.op W.op
    obtain ⟨g, ⟨e⟩⟩ : exists (g : _), Nonempty (L.op.mapArrow.obj g ≅ Arrow.mk f.hom.op) :=
      ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
    exact ⟨Arrow.mk g.hom.unop, ⟨Arrow.isoMk (Arrow.rightFunc.mapIso e.symm).unop
      (Arrow.leftFunc.mapIso

中文:
引理 Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
  证明: by
    have := Localization.essSurj_mapArrow L.op W.op
    obtain ⟨g, ⟨e⟩⟩ : exists (g : _), Nonempty (L.op.mapArrow.obj g ≅ Arrow.mk f.hom.op) :=
      ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
    exact ⟨Arrow.mk g.hom.unop, ⟨Arrow.isoMk (Arrow.rightFunc.mapIso e.symm).unop
      (Arrow.leftFunc.mapIso

Depends on / 依赖: Arrow.isoMk, Arrow.leftFunc.mapIso, Arrow.mk, Arrow.rightFunc.mapIso, Functor, Functor.objObjPreimageIso, L.op, L.op.mapArrow.obj, Localization, Localization.essSurj_mapArrow, Nonempty, Quiver, Quiver.Hom.op_inj, W.op, e.inv.w.symm, e.symm, essSurj_mapArrow, f.hom.op, g.hom.unop, leftFunc
-/
lemma Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions :
    L.mapArrow.EssSurj where
  mem_essImage f := by
    have := Localization.essSurj_mapArrow L.op W.op
    obtain ⟨g, ⟨e⟩⟩ : exists (g : _), Nonempty (L.op.mapArrow.obj g ≅ Arrow.mk f.hom.op) :=
      ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
    exact ⟨Arrow.mk g.hom.unop, ⟨Arrow.isoMk (Arrow.rightFunc.mapIso e.symm).unop
      (Arrow.leftFunc.mapIso e.symm).unop (Quiver.Hom.op_inj e.inv.w.symm)⟩⟩

end

end CategoryTheory
