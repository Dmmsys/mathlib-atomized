/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-! # Bicategories of spans in a category

In this file, given a category `C` and two morphism properties
Wₗ and Wᵣ in C that are stable under compositions, contain identities and
such that for any morphism `b : x₃ ⟶ x₄` in Wₗ and any morphism `r : x₂ → x₃` in Wᵣ,
there exists a pullback square
```
     t
  x₁ --> x₂
  | |
l | | r
  v v
  x₃ --> x₄
     b
```
in `C` such that `t` satisfies `Wₗ` and `l` satisfies `Wᵣ`,
we construct the bicategory of spans in C with left morphism in Wₗ and right morphism
in Wᵣ (TODO @robin-carlier).

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]
  (Wₗ : MorphismProperty C)
  (Wᵣ : MorphismProperty C)

/--
Definition of `Span` / `Span` 的定义

English:
structure Span
  parameters: (c c' : C)
  axioms and operations (5):
    - apex : C
    - l : apex ⟶ c
    - r : apex ⟶ c'
    - wl : Wₗ l
    - wr : Wᵣ r

中文:
结构 Span
  参数: (c c' : C)
  公理与运算 (5 个):
    - apex : C
    - l : apex ⟶ c
    - r : apex ⟶ c'
    - wl : Wₗ l
    - wr : Wᵣ r
-/
structure Span (c c' : C) where
  /-- the apex of the span -/
  apex : C
  /-- the left map -/
  l : apex ⟶ c
  /-- the right map -/
  r : apex ⟶ c'
  wl : Wₗ l
  wr : Wᵣ r

namespace Span

variable {Wₗ Wᵣ} {c c' : C}

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (S₁ S₂ : Span Wₗ Wᵣ c c')
  axioms and operations (3):
    - hom : S₁.apex ⟶ S₂.apex
    - hom_l : hom ≫ S₂.l = S₁.l  [default: by cat_disch]
    - hom_r : hom ≫ S₂.r = S₁.r  [default: by cat_disch]

中文:
结构 Hom
  参数: (S₁ S₂ : Span Wₗ Wᵣ c c')
  公理与运算 (3 个):
    - hom : S₁.apex ⟶ S₂.apex
    - hom_l : hom ≫ S₂.l = S₁.l  [默认: by cat_disch]
    - hom_r : hom ≫ S₂.r = S₁.r  [默认: by cat_disch]

Depends on / 依赖: cat_disch, hom_r
-/
structure Hom (S₁ S₂ : Span Wₗ Wᵣ c c') : Type _ where
  /-- the map between the apices -/
  hom : S₁.apex ⟶ S₂.apex
  hom_l : hom ≫ S₂.l = S₁.l := by cat_disch
  hom_r : hom ≫ S₂.r = S₁.r := by cat_disch

attribute [reassoc (attr := simp)] Hom.hom_l Hom.hom_r
attribute [grind =] Hom.hom_l Hom.hom_r

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Span Wₗ Wᵣ c c')
  body: Hom
  comp φ φ' := { hom := φ.hom ≫ φ'.hom }
  id S := { hom := 𝟙 _ }

中文:
实例 :
  签名: Category (Span Wₗ Wᵣ c c')
  定义体: Hom
  comp φ φ' := { hom := φ.hom ≫ φ'.hom }
  id S := { hom := 𝟙 _ }
-/
instance : Category (Span Wₗ Wᵣ c c') where
  Hom := Hom
  comp φ φ' := { hom := φ.hom ≫ φ'.hom }
  id S := { hom := 𝟙 _ }

attribute [grind =] id_hom comp_hom

@[ext, grind ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom)
  proof: by
  cases f
  cases g
  grind

中文:
引理 hom_ext
  条件: {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom)
  证明: by
  cases f
  cases g
  grind
-/
lemma hom_ext {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  grind

set_option mathlib.tactic.category.grind true in
/-- Construct an isomorphism of spans from an isomorphism between the
apices that is compatible with the projections. -/
@[simps (attr := grind =)]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex)
  body: e.hom
  inv.hom := e.inv

中文:
定义 mkIso
  签名: {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex)
  定义体: e.hom
  inv.hom := e.inv

Depends on / 依赖: cat_disch, e.hom, e.inv, hom.hom, inv.hom
-/
def mkIso {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex)
    (hₗ : e.hom ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e.hom ≫ S'.r = S.r := by cat_disch) :
    S ≅ S' where
  hom.hom := e.hom
  inv.hom := e.inv

variable [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition]

open Limits in
instance {c c' c'' : C} (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') : HasPullback S₁.r S₂.l :=
  letI : HasPullback S₂.l S₁.r := hasPullback_ofHasPullbacksAgainst S₂.wl S₁.wr
  hasPullback_symmetry _ _

instance (S₁ : Span Wₗ Wᵣ c c') : Wₗ.IsStableUnderBaseChangeAlong S₁.r :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wr

instance (S₁ : Span Wₗ Wᵣ c c') : Wᵣ.IsStableUnderBaseChangeAlong S₁.l :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wl

/-- The identity span, where both legs are identity morphisms. -/
@[simps (attr := grind =)]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (c : C)
  body: c
  l := 𝟙 _
  r := 𝟙 _
  wl := MorphismProperty.ContainsIdentities.id_mem _
  wr := MorphismProperty.ContainsIdentities.id_mem _

中文:
定义 id
  签名: (c : C)
  定义体: c
  l := 𝟙 _
  r := 𝟙 _
  wl := MorphismProperty.ContainsIdentities.id_mem _
  wr := MorphismProperty.ContainsIdentities.id_mem _
-/
def id (c : C) :
    Span Wₗ Wᵣ c c where
  apex := c
  l := 𝟙 _
  r := 𝟙 _
  wl := MorphismProperty.ContainsIdentities.id_mem _
  wr := MorphismProperty.ContainsIdentities.id_mem _

open Limits MorphismProperty in
/-- The composition of two spans: if the relevant pullback exists and if the
morphism properties are stable under the relevant base change, it is given by the
total span
```
     P
    / \
   / \
  X₁ X₂
 / \ / \
c c' c''
```
where the top diamond is a pullback square
-/
@[simps (attr := grind =)]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {c c' c'' : C}
  body: pullback S₁.r S₂.l
  l := pullback.fst S₁.r S₂.l ≫ S₁.l
  r := pullback.snd S₁.r S₂.l ≫ S₂.r
  wl :=
    IsStableUnderComposition.comp_mem
      _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.flip <| .of_hasPullback S₁.r S₂.l) S₂.wl) S₁.wl
  wr :=
    IsStableUnderComposition.comp_mem
    _

中文:
定义 comp
  签名: {c c' c'' : C}
  定义体: pullback S₁.r S₂.l
  l := pullback.fst S₁.r S₂.l ≫ S₁.l
  r := pullback.snd S₁.r S₂.l ≫ S₂.r
  wl :=
    IsStableUnderComposition.comp_mem
      _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.flip <| .of_hasPullback S₁.r S₂.l) S₂.wl) S₁.wl
  wr :=
    IsStableUnderComposition.comp_mem
    _

Depends on / 依赖: pullback
-/
noncomputable def comp {c c' c'' : C}
    (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') :
    Span Wₗ Wᵣ c c'' where
  apex := pullback S₁.r S₂.l
  l := pullback.fst S₁.r S₂.l ≫ S₁.l
  r := pullback.snd S₁.r S₂.l ≫ S₂.r
  wl :=
    IsStableUnderComposition.comp_mem
      _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.flip <| .of_hasPullback S₁.r S₂.l) S₂.wl) S₁.wl
  wr :=
    IsStableUnderComposition.comp_mem
    _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.of_hasPullback S₁.r S₂.l) S₁.wr) S₂.wr

end Span

end CategoryTheory
