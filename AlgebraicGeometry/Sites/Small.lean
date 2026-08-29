/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Small sites

In this file we define the small sites associated to morphism properties and give
generating pretopologies.

## Main definitions

- `AlgebraicGeometry.Scheme.overGrothendieckTopology`: the Grothendieck topology on `Over S`
  obtained by localizing the topology on `Scheme` induced by `P` at `S`.
- `AlgebraicGeometry.Scheme.overPretopology`: the pretopology on `Over S` defined by
  `P`-coverings of `S`-schemes. The induced topology agrees with
  `AlgebraicGeometry.Scheme.overGrothendieckTopology`.
- `AlgebraicGeometry.Scheme.smallGrothendieckTopology`: the by the inclusion
  `P.Over ⊤ S ⥤ Over S` induced topology on `P.Over ⊤ S`.
- `AlgebraicGeometry.Scheme.smallPretopology`: the pretopology on `P.Over ⊤ S` defined by
  `P`-coverings of `S`-schemes with `P`. The induced topology agrees
  with `AlgebraicGeometry.Scheme.smallGrothendieckTopology`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P Q : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
  [P.IsStableUnderBaseChange]

/--
Definition of `Cover.toPresieveOver` / `Cover.toPresieveOver` 的定义

English:
definition Cover.toPresieveOver
  signature: {X : Over S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
  body: Presieve.ofArrows (fun i => (𝒰.X i).asOver S) (fun i => (𝒰.f i).asOver S)

中文:
定义 Cover.toPresieveOver
  签名: {X : Over S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
  定义体: Presieve.ofArrows (fun i => (𝒰.X i).asOver S) (fun i => (𝒰.f i).asOver S)

Depends on / 依赖: Presieve, Presieve.ofArrows, asOver, ofArrows
-/
def Cover.toPresieveOver {X : Over S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    Presieve X :=
  Presieve.ofArrows (fun i => (𝒰.X i).asOver S) (fun i => (𝒰.f i).asOver S)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Cover.toPresieveOverProp` / `Cover.toPresieveOverProp` 的定义

English:
definition Cover.toPresieveOverProp
  signature: {X : Q.Over ⊤ S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
  body: Presieve.ofArrows (fun i => (𝒰.X i).asOverProp S (h i)) (fun i => (𝒰.f i).asOverProp S)

中文:
定义 Cover.toPresieveOverProp
  签名: {X : Q.Over ⊤ S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
  定义体: Presieve.ofArrows (fun i => (𝒰.X i).asOverProp S (h i)) (fun i => (𝒰.f i).asOverProp S)

Depends on / 依赖: Presieve, Presieve.ofArrows, asOverProp, ofArrows
-/
def Cover.toPresieveOverProp {X : Q.Over ⊤ S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
    (h : forall j, Q (𝒰.X j ↘ S)) : Presieve X :=
  Presieve.ofArrows (fun i => (𝒰.X i).asOverProp S (h i)) (fun i => (𝒰.f i).asOverProp S)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `Cover.overEquiv_generate_toPresieveOver_eq_ofArrows` / 引理 `Cover.overEquiv_generate_toPresieveOver_eq_ofArrows`

English:
lemma Cover.overEquiv_generate_toPresieveOver_eq_ofArrows
  statement: {X : Over S}
  proof: by
  ext V f
  simp only [Sieve.overEquiv_iff, Sieve.generate_apply]
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    exact ⟨𝒰.X k, h.left, 𝒰.f k, ⟨k⟩, congrArg CommaMorphism.left hcomp⟩
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : 𝒰.f k ≫ X.hom = 𝒰.X k ↘ S := comp_over (𝒰.f k) S
    refine ⟨(𝒰.X k).asOver S, Over.homMk h (by simp [← hcomp, this]), (𝒰.f k).asOver S, ⟨k⟩, ?_⟩
    ext : 1
    simpa

中文:
引理 Cover.overEquiv_generate_toPresieveOver_eq_ofArrows
  结论: {X : Over S}
  证明: by
  ext V f
  simp only [Sieve.overEquiv_iff, Sieve.generate_apply]
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    exact ⟨𝒰.X k, h.left, 𝒰.f k, ⟨k⟩, congrArg CommaMorphism.left hcomp⟩
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : 𝒰.f k ≫ X.hom = 𝒰.X k ↘ S := comp_over (𝒰.f k) S
    refine ⟨(𝒰.X k).asOver S, Over.homMk h (by simp [← hcomp, this]), (𝒰.f k).asOver S, ⟨k⟩, ?_⟩
    ext : 1
    simpa

Depends on / 依赖: CommaMorphism, CommaMorphism.left, Over.homMk, Sieve.generate_apply, Sieve.overEquiv_iff, X.hom, asOver, comp_over, generate_apply, h.left, overEquiv_iff
-/
lemma Cover.overEquiv_generate_toPresieveOver_eq_ofArrows {X : Over S}
    (𝒰 : Cover.{u} (precoverage P) X.left)
    [𝒰.Over S] : Sieve.overEquiv X (Sieve.generate 𝒰.toPresieveOver) =
      Sieve.ofArrows 𝒰.X 𝒰.f := by
  ext V f
  simp only [Sieve.overEquiv_iff, Sieve.generate_apply]
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    exact ⟨𝒰.X k, h.left, 𝒰.f k, ⟨k⟩, congrArg CommaMorphism.left hcomp⟩
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : 𝒰.f k ≫ X.hom = 𝒰.X k ↘ S := comp_over (𝒰.f k) S
    refine ⟨(𝒰.X k).asOver S, Over.homMk h (by simp [← hcomp, this]), (𝒰.f k).asOver S, ⟨k⟩, ?_⟩
    ext : 1
    simpa

/--
lemma `Cover.toPresieveOver_le_arrows_iff` / 引理 `Cover.toPresieveOver_le_arrows_iff`

English:
lemma Cover.toPresieveOver_le_arrows_iff
  statement: {X : Over S} (R : Sieve X)
  proof: by
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← (Sieve.overEquiv X).map_rel_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

中文:
引理 Cover.toPresieveOver_le_arrows_iff
  结论: {X : Over S} (R : 筛 X)
  证明: by
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← (Sieve.overEquiv X).map_rel_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

Depends on / 依赖: Sieve.giGenerate.gc.le_iff_le, Sieve.overEquiv, giGenerate, le_iff_le, map_rel_iff, overEquiv, overEquiv_generate_toPresieveOver_eq_ofArrows, simp_rw
-/
lemma Cover.toPresieveOver_le_arrows_iff {X : Over S} (R : Sieve X)
    (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    𝒰.toPresieveOver <= R.arrows ↔
      Presieve.ofArrows 𝒰.X 𝒰.f <= (Sieve.overEquiv X R).arrows := by
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← (Sieve.overEquiv X).map_rel_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

variable [P.IsMultiplicative] [P.RespectsIso]

variable (P Q S)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `overPretopology` / `overPretopology` 的定义

English:
definition overPretopology
  signature: : Pretopology (Over S) where
  body: {R | exists (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver}
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using!
      (Presieve.ofArrows_pullback f (fun i => (𝒰.X i).asOver S) (fun i => (𝒰.f i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.f j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j => (𝒰.f j).asOver S) _ (fun Y f H j => ((V f H).X j).asOver S)
        (fun Y f H j => ((V f H).f j).asOver S)
    apply hV

中文:
定义 overPretopology
  签名: : Pretopology (Over S) where
  定义体: {R | exists (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver}
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using!
      (Presieve.ofArrows_pullback f (fun i => (𝒰.X i).asOver S) (fun i => (𝒰.f i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.f j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j => (𝒰.f j).asOver S) _ (fun Y f H j => ((V f H).X j).asOver S)
        (fun Y f H j => ((V f H).f j).asOver S)
    apply hV

Depends on / 依赖: Y.left, precoverage, toPresieveOver
-/
def overPretopology : Pretopology (Over S) where
  coverings Y := {R | exists (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver}
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using!
      (Presieve.ofArrows_pullback f (fun i => (𝒰.X i).asOver S) (fun i => (𝒰.f i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.f j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j => (𝒰.f j).asOver S) _ (fun Y f H j => ((V f H).X j).asOver S)
        (fun Y f H j => ((V f H).f j).asOver S)
    apply hV

/--
Definition of `overGrothendieckTopology` / `overGrothendieckTopology` 的定义

English:
abbreviation overGrothendieckTopology
  signature: : GrothendieckTopology (Over S)
  body: (Scheme.grothendieckTopology P).over S

中文:
缩写 overGrothendieckTopology
  签名: : Grothendieck拓扑 (Over S)
  定义体: (Scheme.grothendieckTopology P).over S

Depends on / 依赖: Scheme, Scheme.grothendieckTopology, grothendieckTopology
-/
abbrev overGrothendieckTopology : GrothendieckTopology (Over S) :=
  (Scheme.grothendieckTopology P).over S

/--
lemma `overGrothendieckTopology_eq_toGrothendieck_overPretopology` / 引理 `overGrothendieckTopology_eq_toGrothendieck_overPretopology`

English:
lemma overGrothendieckTopology_eq_toGrothendieck_overPretopology
  proof: by
  ext X R
  rw [GrothendieckTopology.mem_over_iff]
  constructor
  · intro hR
    obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hR
    rw [mem_grothendieckTopology_iff] at hR
    let (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    let : 𝒰.Over S :=
      { over := inferInstance
        isOver_map := fun i => ⟨rfl⟩ }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    rw [mem_grothendieckTopology_iff]
    use 𝒰
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

中文:
引理 overGrothendieckTopology_eq_toGrothendieck_overPretopology
  证明: by
  ext X R
  rw [GrothendieckTopology.mem_over_iff]
  constructor
  · intro hR
    obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hR
    rw [mem_grothendieckTopology_iff] at hR
    let (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    let : 𝒰.Over S :=
      { over := inferInstance
        isOver_map := fun i => ⟨rfl⟩ }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    rw [mem_grothendieckTopology_iff]
    use 𝒰
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

Depends on / 依赖: Cover.toPresieveOver_le_arrow, Cover.toPresieveOver_le_arrows_iff, GrothendieckTopology, GrothendieckTopology.mem_over_iff, X.hom, exists_cover_of_mem_grothendieckTopology, isOver_map, mem_grothendieckTopology_iff, mem_over_iff, toPresieveOver, toPresieveOver_le_arrow, toPresieveOver_le_arrows_iff
-/
lemma overGrothendieckTopology_eq_toGrothendieck_overPretopology :
    S.overGrothendieckTopology P = (S.overPretopology P).toGrothendieck := by
  ext X R
  rw [GrothendieckTopology.mem_over_iff]
  constructor
  · intro hR
    obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hR
    rw [mem_grothendieckTopology_iff] at hR
    let (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    let : 𝒰.Over S :=
      { over := inferInstance
        isOver_map := fun i => ⟨rfl⟩ }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    rw [mem_grothendieckTopology_iff]
    use 𝒰
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

variable {S}

/--
lemma `mem_overGrothendieckTopology` / 引理 `mem_overGrothendieckTopology`

English:
lemma mem_overGrothendieckTopology
  given: (X : Over S) (R : Sieve X)
  proof: by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
    use 𝒰, h
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

中文:
引理 mem_overGrothendieckTopology
  条件: (X : Over S) (R : 筛 X)
  证明: by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
    use 𝒰, h
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

Depends on / 依赖: overGrothendieckTopology_eq_toGrothendieck_overPretopology, toPresieveOver
-/
lemma mem_overGrothendieckTopology (X : Over S) (R : Sieve X) :
    R in S.overGrothendieckTopology P X ↔
      exists (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S), 𝒰.toPresieveOver <= R.arrows := by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
    use 𝒰, h
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

variable [Q.IsStableUnderComposition]

variable (S) {P Q} in
/--
lemma `locallyCoverDense_of_le` / 引理 `locallyCoverDense_of_le`

English:
lemma locallyCoverDense_of_le
  given: (hPQ : P <= Q)
  proof: by
    intro ⟨T, hT⟩
    rw [mem_overGrothendieckTopology] at hT ⊢
    obtain ⟨𝒰, h, hle⟩ := hT
    use 𝒰, h
    rintro - - ⟨i⟩
    have p : Q (𝒰.X i ↘ S) := by
      rw [← comp_over (𝒰.f i) S]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop i) X.prop
    use (𝒰.X i).asOverProp S p, MorphismProperty.Over.homMk (𝒰.f i) (comp_over (𝒰.f i) S), 𝟙 _
    exact ⟨hle _ _ ⟨i⟩, rfl⟩

中文:
引理 locallyCoverDense_of_le
  条件: (hPQ : P <= Q)
  证明: by
    intro ⟨T, hT⟩
    rw [mem_overGrothendieckTopology] at hT ⊢
    obtain ⟨𝒰, h, hle⟩ := hT
    use 𝒰, h
    rintro - - ⟨i⟩
    have p : Q (𝒰.X i ↘ S) := by
      rw [← comp_over (𝒰.f i) S]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop i) X.prop
    use (𝒰.X i).asOverProp S p, MorphismProperty.Over.homMk (𝒰.f i) (comp_over (𝒰.f i) S), 𝟙 _
    exact ⟨hle _ _ ⟨i⟩, rfl⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.Over.homMk, Q.comp_mem, X.prop, asOverProp, comp_mem, comp_over, map_prop, mem_overGrothendieckTopology
-/
lemma locallyCoverDense_of_le (hPQ : P <= Q) :
    (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) where
  functorPushforward_functorPullback_mem X := by
    intro ⟨T, hT⟩
    rw [mem_overGrothendieckTopology] at hT ⊢
    obtain ⟨𝒰, h, hle⟩ := hT
    use 𝒰, h
    rintro - - ⟨i⟩
    have p : Q (𝒰.X i ↘ S) := by
      rw [← comp_over (𝒰.f i) S]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop i) X.prop
    use (𝒰.X i).asOverProp S p, MorphismProperty.Over.homMk (𝒰.f i) (comp_over (𝒰.f i) S), 𝟙 _
    exact ⟨hle _ _ ⟨i⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S)
  body: locallyCoverDense_of_le S le_rfl

中文:
实例 :
  签名: (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S)
  定义体: locallyCoverDense_of_le S le_rfl

Depends on / 依赖: le_rfl, locallyCoverDense_of_le
-/
instance : (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
  locallyCoverDense_of_le S le_rfl

variable (S) {Q} in
/--
Definition of `smallGrothendieckTopology` / `smallGrothendieckTopology` 的定义

English:
abbreviation smallGrothendieckTopology
  signature: : GrothendieckTopology (Q.Over ⊤ S)
  body: (MorphismProperty.Over.forget Q ⊤ S).restrictedTopology (S.overGrothendieckTopology P)

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE := smallGrothendieckTopology

中文:
缩写 smallGrothendieckTopology
  签名: : Grothendieck拓扑 (Q.Over ⊤ S)
  定义体: (MorphismProperty.Over.forget Q ⊤ S).restrictedTopology (S.overGrothendieckTopology P)

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE := smallGrothendieckTopology

Depends on / 依赖: MorphismProperty, MorphismProperty.Over.forget, S.overGrothendieckTopology, forget, overGrothendieckTopology, restrictedTopology
-/
abbrev smallGrothendieckTopology : GrothendieckTopology (Q.Over ⊤ S) :=
  (MorphismProperty.Over.forget Q ⊤ S).restrictedTopology (S.overGrothendieckTopology P)

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE := smallGrothendieckTopology

variable [Q.IsStableUnderBaseChange] [Q.HasOfPostcompProperty Q]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `smallPretopology` / `smallPretopology` 的定义

English:
definition smallPretopology
  signature: : Pretopology (Q.Over ⊤ S) where
  body: {R | exists (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S) (h : forall j : 𝒰.I₀, Q (𝒰.X j ↘ S)),
      R = 𝒰.toPresieveOverProp h}
  has_isos {X Y} f := ⟨coverOfIsIso f.left, inferInstance, fun _ => Y.prop,
    (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, p, rfl⟩
    refine ⟨𝒰.pullbackCoverOverProp' S f.left (Q := Q) Y.prop X.prop p, inferInstance, ?_, ?_⟩
    · intro j
      apply MorphismProperty.Comma.prop
    · exact (Presieve.ofArrows_pullback f (fun i => ⟨(𝒰.X i).asOver S, p i⟩)
        (fun i => ⟨(𝒰.f i).asOver S, trivial, trivial⟩)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, p, rfl⟩ H
    choose V h pV hV using H
    let 𝒱j (j : 𝒰.I₀) : (Cover (precoverage P) ((𝒰.X j).asOverProp S (p j)).left) :=
      V ((𝒰.f j).asOverProp S) ⟨j⟩
    refine ⟨𝒰.bind (fun j => 𝒱j j), inferInstance, fun j => pV _ _ _, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j => ((𝒰.f j).asOverProp S)) _
        (fun Y f H j => ((V f H).X j).asOverProp S (pV _ _ _))
        (fun Y f H j => ((V f H).f j).asOverProp S)
    apply hV

中文:
定义 smallPretopology
  签名: : Pretopology (Q.Over ⊤ S) where
  定义体: {R | exists (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S) (h : forall j : 𝒰.I₀, Q (𝒰.X j ↘ S)),
      R = 𝒰.toPresieveOverProp h}
  has_isos {X Y} f := ⟨coverOfIsIso f.left, inferInstance, fun _ => Y.prop,
    (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, p, rfl⟩
    refine ⟨𝒰.pullbackCoverOverProp' S f.left (Q := Q) Y.prop X.prop p, inferInstance, ?_, ?_⟩
    · intro j
      apply MorphismProperty.Comma.prop
    · exact (Presieve.ofArrows_pullback f (fun i => ⟨(𝒰.X i).asOver S, p i⟩)
        (fun i => ⟨(𝒰.f i).asOver S, trivial, trivial⟩)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, p, rfl⟩ H
    choose V h pV hV using H
    let 𝒱j (j : 𝒰.I₀) : (Cover (precoverage P) ((𝒰.X j).asOverProp S (p j)).left) :=
      V ((𝒰.f j).asOverProp S) ⟨j⟩
    refine ⟨𝒰.bind (fun j => 𝒱j j), inferInstance, fun j => pV _ _ _, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j => ((𝒰.f j).asOverProp S)) _
        (fun Y f H j => ((V f H).X j).asOverProp S (pV _ _ _))
        (fun Y f H j => ((V f H).f j).asOverProp S)
    apply hV

Depends on / 依赖: MorphismProperty, MorphismProperty.Comma.prop, Presieve, Presieve.ofArrows_pUnit, Presieve.ofArrows_pullback, X.prop, Y.left, Y.prop, asOver, coverOfIsIso, f.left, has_isos, ofArrows_pUnit, ofArrows_pullback, precoverage, pullbackCoverOverProp, pullbacks, toPresieveOverProp
-/
def smallPretopology : Pretopology (Q.Over ⊤ S) where
  coverings Y :=
    {R | exists (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S) (h : forall j : 𝒰.I₀, Q (𝒰.X j ↘ S)),
      R = 𝒰.toPresieveOverProp h}
  has_isos {X Y} f := ⟨coverOfIsIso f.left, inferInstance, fun _ => Y.prop,
    (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, p, rfl⟩
    refine ⟨𝒰.pullbackCoverOverProp' S f.left (Q := Q) Y.prop X.prop p, inferInstance, ?_, ?_⟩
    · intro j
      apply MorphismProperty.Comma.prop
    · exact (Presieve.ofArrows_pullback f (fun i => ⟨(𝒰.X i).asOver S, p i⟩)
        (fun i => ⟨(𝒰.f i).asOver S, trivial, trivial⟩)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, p, rfl⟩ H
    choose V h pV hV using H
    let 𝒱j (j : 𝒰.I₀) : (Cover (precoverage P) ((𝒰.X j).asOverProp S (p j)).left) :=
      V ((𝒰.f j).asOverProp S) ⟨j⟩
    refine ⟨𝒰.bind (fun j => 𝒱j j), inferInstance, fun j => pV _ _ _, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j => ((𝒰.f j).asOverProp S)) _
        (fun Y f H j => ((V f H).X j).asOverProp S (pV _ _ _))
        (fun Y f H j => ((V f H).f j).asOverProp S)
    apply hV

set_option backward.isDefEq.respectTransparency false in
variable (S) {P Q} in
/--
lemma `smallGrothendieckTopology_eq_toGrothendieck_smallPretopology` / 引理 `smallGrothendieckTopology_eq_toGrothendieck_smallPretopology`

English:
lemma smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
  given: (hPQ : P <= Q)
  proof: by
  ext X R
  have : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
    locallyCoverDense_of_le S hPQ
  simp only [smallGrothendieckTopology, Functor.mem_restrictedTopology_iff,
    mem_overGrothendieckTopology, Pretopology.mem_toGrothendieck]
  constructor
  · intro ⟨𝒰, h, le⟩
    have hj (j : 𝒰.I₀) : Q (𝒰.X j ↘ S) := by
      rw [← comp_over (𝒰.f j)]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop _) X.prop
    refine ⟨𝒰.toPresieveOverProp hj, ?_, ?_⟩
    · use 𝒰, h, hj
    · rintro - - ⟨i⟩
      let fi : (𝒰.X i).asOverProp S (hj i) ⟶ X := (𝒰.f i).asOverProp S
      have : R.functorPushforward _ ((MorphismProperty.Over.forget Q ⊤ S).map fi) := le _ _ ⟨i⟩
      rwa [Sieve.functorPushforward_apply,
        Sieve.mem_functorPushforward_iff_of_full_of_faithful] at this
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, le⟩
    use 𝒰, h
    rintro - - ⟨i⟩
    exact ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S, 𝟙 _, le _ _ ⟨i⟩, rfl⟩

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology :=
  smallGrothendieckTopology_eq_toGrothendieck_smallPretopology

中文:
引理 smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
  条件: (hPQ : P <= Q)
  证明: by
  ext X R
  have : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
    locallyCoverDense_of_le S hPQ
  simp only [smallGrothendieckTopology, Functor.mem_restrictedTopology_iff,
    mem_overGrothendieckTopology, Pretopology.mem_toGrothendieck]
  constructor
  · intro ⟨𝒰, h, le⟩
    have hj (j : 𝒰.I₀) : Q (𝒰.X j ↘ S) := by
      rw [← comp_over (𝒰.f j)]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop _) X.prop
    refine ⟨𝒰.toPresieveOverProp hj, ?_, ?_⟩
    · use 𝒰, h, hj
    · rintro - - ⟨i⟩
      let fi : (𝒰.X i).asOverProp S (hj i) ⟶ X := (𝒰.f i).asOverProp S
      have : R.functorPushforward _ ((MorphismProperty.Over.forget Q ⊤ S).map fi) := le _ _ ⟨i⟩
      rwa [Sieve.functorPushforward_apply,
        Sieve.mem_functorPushforward_iff_of_full_of_faithful] at this
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, le⟩
    use 𝒰, h
    rintro - - ⟨i⟩
    exact ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S, 𝟙 _, le _ _ ⟨i⟩, rfl⟩

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology :=
  smallGrothendieckTopology_eq_toGrothendieck_smallPretopology

Depends on / 依赖: Functor, Functor.mem_restrictedTopology_iff, LocallyCoverDense, MorphismProperty, MorphismProperty.Over.forget, Pretopology, Pretopology.mem_toGrothendieck, Q.comp_mem, X.prop, comp_mem, comp_over, forget, locallyCoverDense_of_le, map_prop, mem_overGrothendieckTopology, mem_restrictedTopology_iff, mem_toGrothendieck, overGrothendieckTopology, smallGrothendieckTopology, toPresieveOverProp
-/
lemma smallGrothendieckTopology_eq_toGrothendieck_smallPretopology (hPQ : P <= Q) :
    S.smallGrothendieckTopology P = (S.smallPretopology P Q).toGrothendieck := by
  ext X R
  have : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
    locallyCoverDense_of_le S hPQ
  simp only [smallGrothendieckTopology, Functor.mem_restrictedTopology_iff,
    mem_overGrothendieckTopology, Pretopology.mem_toGrothendieck]
  constructor
  · intro ⟨𝒰, h, le⟩
    have hj (j : 𝒰.I₀) : Q (𝒰.X j ↘ S) := by
      rw [← comp_over (𝒰.f j)]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop _) X.prop
    refine ⟨𝒰.toPresieveOverProp hj, ?_, ?_⟩
    · use 𝒰, h, hj
    · rintro - - ⟨i⟩
      let fi : (𝒰.X i).asOverProp S (hj i) ⟶ X := (𝒰.f i).asOverProp S
      have : R.functorPushforward _ ((MorphismProperty.Over.forget Q ⊤ S).map fi) := le _ _ ⟨i⟩
      rwa [Sieve.functorPushforward_apply,
        Sieve.mem_functorPushforward_iff_of_full_of_faithful] at this
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, le⟩
    use 𝒰, h
    rintro - - ⟨i⟩
    exact ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S, 𝟙 _, le _ _ ⟨i⟩, rfl⟩

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology :=
  smallGrothendieckTopology_eq_toGrothendieck_smallPretopology

variable {P Q}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mem_toGrothendieck_smallPretopology` / 引理 `mem_toGrothendieck_smallPretopology`

English:
lemma mem_toGrothendieck_smallPretopology
  given: (X : Q.Over ⊤ S) (R : Sieve X)
  proof: by
  rw [Pretopology.mem_toGrothendieck]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.X (𝒰.idx x)).asOverProp S (p _), (𝒰.f (𝒰.idx x)).asOverProp S, y, hle _ _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.idx x
  · choose Y f y hf hP hy using h
    let 𝒰 : X.left.Cover (precoverage P) :=
      { I₀ := X.left,
        X := fun i => (Y i).left
        f := fun i => (f i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ⟨x, y x, hy x⟩, hP⟩ }
    let : 𝒰.Over S :=
      { over := fun i => inferInstance
        isOver_map := fun i => inferInstance }
    refine ⟨𝒰.toPresieveOverProp fun i => MorphismProperty.Comma.prop _, ?_, ?_⟩
    · use 𝒰, inferInstance, fun i => MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

中文:
引理 mem_toGrothendieck_smallPretopology
  条件: (X : Q.Over ⊤ S) (R : 筛 X)
  证明: by
  rw [Pretopology.mem_toGrothendieck]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.X (𝒰.idx x)).asOverProp S (p _), (𝒰.f (𝒰.idx x)).asOverProp S, y, hle _ _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.idx x
  · choose Y f y hf hP hy using h
    let 𝒰 : X.left.Cover (precoverage P) :=
      { I₀ := X.left,
        X := fun i => (Y i).left
        f := fun i => (f i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ⟨x, y x, hy x⟩, hP⟩ }
    let : 𝒰.Over S :=
      { over := fun i => inferInstance
        isOver_map := fun i => inferInstance }
    refine ⟨𝒰.toPresieveOverProp fun i => MorphismProperty.Comma.prop _, ?_, ?_⟩
    · use 𝒰, inferInstance, fun i => MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

Depends on / 依赖: Pretopology, Pretopology.mem_toGrothendieck, X.left, X.left.Cover, asOverProp, covers, map_prop, mem_toGrothendieck, precoverage
-/
lemma mem_toGrothendieck_smallPretopology (X : Q.Over ⊤ S) (R : Sieve X) :
    R in (S.smallPretopology P Q).toGrothendieck X ↔
      forall x : X.left, exists (Y : Q.Over ⊤ S) (f : Y ⟶ X) (y : Y.left),
        R f ∧ P f.left ∧ f.left y = x := by
  rw [Pretopology.mem_toGrothendieck]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.X (𝒰.idx x)).asOverProp S (p _), (𝒰.f (𝒰.idx x)).asOverProp S, y, hle _ _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.idx x
  · choose Y f y hf hP hy using h
    let 𝒰 : X.left.Cover (precoverage P) :=
      { I₀ := X.left,
        X := fun i => (Y i).left
        f := fun i => (f i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ⟨x, y x, hy x⟩, hP⟩ }
    let : 𝒰.Over S :=
      { over := fun i => inferInstance
        isOver_map := fun i => inferInstance }
    refine ⟨𝒰.toPresieveOverProp fun i => MorphismProperty.Comma.prop _, ?_, ?_⟩
    · use 𝒰, inferInstance, fun i => MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mem_smallGrothendieckTopology` / 引理 `mem_smallGrothendieckTopology`

English:
lemma mem_smallGrothendieckTopology
  given: [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X)
  proof: by
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

中文:
引理 mem_smallGrothendieckTopology
  条件: [P.有OfPostcompProperty P] (X : P.Over ⊤ S) (R : 筛 X)
  证明: by
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

Depends on / 依赖: le_rfl, smallGrothendieckTopology_eq_toGrothendieck_smallPretopology, toPresieveOverProp
-/
lemma mem_smallGrothendieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) :
    R in S.smallGrothendieckTopology P X ↔
      exists (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S) (h : forall j, P (𝒰.X j ↘ S)),
          𝒰.toPresieveOverProp h <= R.arrows := by
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

end AlgebraicGeometry.Scheme
