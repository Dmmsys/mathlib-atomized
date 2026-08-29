/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Covers of schemes over a base

In this file we define the typeclass `Cover.Over`. For a cover `𝒰` of an `S`-scheme `X`,
the datum `𝒰.Over S` contains `S`-scheme structures on the components of `𝒰` and asserts
that the component maps are morphisms of `S`-schemes.

We provide instances of `𝒰.Over S` for standard constructions on covers.

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} (S : Scheme.{u})

/--
Definition of `asOverProp` / `asOverProp` 的定义

English:
abbreviation asOverProp
  signature: (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S))
  body: ⟨X.asOver S, h⟩

中文:
缩写 asOverProp
  签名: (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S))
  定义体: ⟨X.asOver S, h⟩

Depends on / 依赖: X.asOver, asOver
-/
abbrev asOverProp (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S)) : P.Over ⊤ S :=
  ⟨X.asOver S, h⟩

/--
Definition of `Hom.asOverProp` / `Hom.asOverProp` 的定义

English:
abbreviation Hom.asOverProp
  signature: {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
  body: ⟨f.asOver S, trivial, trivial⟩

中文:
缩写 Hom.asOverProp
  签名: {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
  定义体: ⟨f.asOver S, trivial, trivial⟩

Depends on / 依赖: asOver, f.asOver
-/
abbrev Hom.asOverProp {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
    [f.IsOver S] {hX : P (X ↘ S)} {hY : P (Y ↘ S)} : X.asOverProp S hX ⟶ Y.asOverProp S hY :=
  ⟨f.asOver S, trivial, trivial⟩

/--
Definition of `Cover.Over` / `Cover.Over` 的定义

English:
class Cover.Over
  parameters: {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
  axioms and operations (2):
    - over((j : 𝒰.I₀)) : (𝒰.X j).Over S  [default: by infer_instance]
    - isOver_map((j : 𝒰.I₀)) : (𝒰.f j).IsOver S  [default: by infer_instance]

中文:
类 Cover.Over
  参数: {P : Morphism命题erty Scheme.{u}} [P.IsStableUnderBaseChange]
  公理与运算 (2 个):
    - over((j : 𝒰.I₀)) : (𝒰.X j).Over S  [默认: by infer_instance]
    - isOver_map((j : 𝒰.I₀)) : (𝒰.f j).IsOver S  [默认: by infer_instance]
-/
protected class Cover.Over {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [IsJointlySurjectivePreserving P] {X : Scheme.{u}} [X.Over S]
    (𝒰 : X.Cover (precoverage P)) where
  over (j : 𝒰.I₀) : (𝒰.X j).Over S := by infer_instance
  isOver_map (j : 𝒰.I₀) : (𝒰.f j).IsOver S := by infer_instance

attribute [instance_reducible] Cover.Over.over
attribute [instance] Cover.Over.over Cover.Over.isOver_map

variable [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) [X.Over S] [Y.Over S]
  body: inferInstanceAs X.Over S
isOver_map _ := inferInstanceAs f.IsOver S

中文:
实例 [P.ContainsIdentities]
  签名: [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) [X.Over S] [Y.Over S]
  定义体: inferInstanceAs X.Over S
isOver_map _ := inferInstanceAs f.IsOver S
-/
instance [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) [X.Over S] [Y.Over S]
    [f.IsOver S] [IsIso f] : (coverOfIsIso (P := P) f).Over S where
over _ := inferInstanceAs X.Over S
isOver_map _ := inferInstanceAs f.IsOver S

section

variable {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) [W.Over S] [X.Over S]
  [𝒰.Over S] [f.IsOver S]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a cover of `S`-schemes along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullback₁`, as here we take
the pullback in `Over S`, whose underlying scheme is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps]
/--
Definition of `Cover.pullbackCoverOver` / `Cover.pullbackCoverOver` 的定义

English:
definition Cover.pullbackCoverOver
  signature: : W.Cover (precoverage P) where
  body: 𝒰.I₀
  X x := (pullback (f.asOver S) ((𝒰.f x).asOver S)).left
  f x := (pullback.fst (f.asOver S) ((𝒰.f x).asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_

中文:
定义 Cover.pullbackCoverOver
  签名: : W.Cover (precoverage P) where
  定义体: 𝒰.I₀
  X x := (pullback (f.asOver S) ((𝒰.f x).asOver S)).left
  f x := (pullback.fst (f.asOver S) ((𝒰.f x).asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_
-/
def Cover.pullbackCoverOver : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback (f.asOver S) ((𝒰.f x).asOver S)).left
  f x := (pullback.fst (f.asOver S) ((𝒰.f x).asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₁ f).f i) _
        ((PreservesPullback.iso (Over.forget S) (f.asOver S) ((𝒰.f _).asOver S)).inv)
        (PreservesPullback.iso_inv_fst _ _ _) x).mp hy
    · dsimp only
      rw [← Over.forget_map]; rw [← PreservesPullback.iso_hom_fst]; rw [P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ (𝒰.map_prop j)

instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOver S f).X j).Over S where
  hom := (pullback (f.asOver S) ((𝒰.f j).asOver S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝒰.pullbackCoverOver S f).Over S
  body: { comp_over := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.f j).asOver S)) }

中文:
实例 :
  签名: (𝒰.pullbackCoverOver S f).Over S
  定义体: { comp_over := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.f j).asOver S)) }

Depends on / 依赖: Over.w, asOver, comp_over, f.asOver, pullback, pullback.fst
-/
instance : (𝒰.pullbackCoverOver S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.f j).asOver S)) }

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOver` with the arguments in the
fiber products flipped. -/
@[simps]
/--
Definition of `Cover.pullbackCoverOver'` / `Cover.pullbackCoverOver'` 的定义

English:
definition Cover.pullbackCoverOver'
  signature: : W.Cover (precoverage P) where
  body: 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOver S) (f.asOver S)).left
  f x := (pullback.snd ((𝒰.f x).asOver S) (f.asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_

中文:
定义 Cover.pullbackCoverOver'
  签名: : W.Cover (precoverage P) where
  定义体: 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOver S) (f.asOver S)).left
  f x := (pullback.snd ((𝒰.f x).asOver S) (f.asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_
-/
def Cover.pullbackCoverOver' : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOver S) (f.asOver S)).left
  f x := (pullback.snd ((𝒰.f x).asOver S) (f.asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₂ f).f _) _
        ((PreservesPullback.iso (Over.forget S) ((𝒰.f _).asOver S) (f.asOver S)).inv)
        (PreservesPullback.iso_inv_snd _ _ _) x).mp hy
    · dsimp only
      rw [← Over.forget_map]; rw [← PreservesPullback.iso_hom_snd]; rw [P.cancel_left_of_respectsIso]
      exact P.pullback_snd _ _ (𝒰.map_prop j)

instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOver' S f).X j).Over S where
  hom := (pullback ((𝒰.f j).asOver S) (f.asOver S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝒰.pullbackCoverOver' S f).Over S
  body: { comp_over := by exact Over.w (pullback.snd ((𝒰.f j).asOver S) (f.asOver S)) }

中文:
实例 :
  签名: (𝒰.pullbackCoverOver' S f).Over S
  定义体: { comp_over := by exact Over.w (pullback.snd ((𝒰.f j).asOver S) (f.asOver S)) }

Depends on / 依赖: Over.w, asOver, comp_over, f.asOver, pullback, pullback.snd
-/
instance : (𝒰.pullbackCoverOver' S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.snd ((𝒰.f j).asOver S) (f.asOver S)) }

variable {Q : MorphismProperty Scheme.{u}} [Q.HasOfPostcompProperty Q]
  [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]

variable (hX : Q (X ↘ S)) (hW : Q (W ↘ S)) (hQ : forall j, Q (𝒰.X j ↘ S))

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a cover of `S`-schemes with `Q` along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullbackCover`, as here we take
the pullback in `Q.Over ⊤ S`, whose underlying scheme is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps -isSimp]
/--
Definition of `Cover.pullbackCoverOverProp` / `Cover.pullbackCoverOverProp` 的定义

English:
definition Cover.pullbackCoverOverProp
  signature: : W.Cover (precoverage P) where
  body: 𝒰.I₀
  X x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)).left
  f x := (pullback.fst (f.asOverProp S) ((𝒰.f x).asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ 

中文:
定义 Cover.pullbackCoverOverProp
  签名: : W.Cover (precoverage P) where
  定义体: 𝒰.I₀
  X x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)).left
  f x := (pullback.fst (f.asOverProp S) ((𝒰.f x).asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ 
-/
def Cover.pullbackCoverOverProp : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)).left
  f x := (pullback.fst (f.asOverProp S) ((𝒰.f x).asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₁ f).f i) _
        ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
          (f.asOverProp S) ((𝒰.f _).asOverProp S)).inv)
        (PreservesPullback.iso_inv_fst _ _ _) x).mp hy
    · simp only [← CategoryTheory.Over.forget_map]
      rw [MorphismProperty.Comma.toCommaMorphism_eq_hom]; rw [← MorphismProperty.Comma.forget_map]; rw [← Functor.comp_map]
      rw [← PreservesPullback.iso_hom_fst]; rw [P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ (𝒰.map_prop j)

instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOverProp S f hX hW hQ).X j).Over S where
  hom := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f j).asOverProp (hX := hQ j) (hY := hX) S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝒰.pullbackCoverOverProp S f hX hW hQ).Over S
  body: { comp_over := by exact (pullback.fst (f.asOverProp S) ((𝒰.f j).asOverProp S)).w }

中文:
实例 :
  签名: (𝒰.pullbackCoverOver命题 S f hX hW hQ).Over S
  定义体: { comp_over := by exact (pullback.fst (f.asOverProp S) ((𝒰.f j).asOverProp S)).w }

Depends on / 依赖: asOverProp, comp_over, f.asOverProp, pullback, pullback.fst
-/
instance : (𝒰.pullbackCoverOverProp S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.fst (f.asOverProp S) ((𝒰.f j).asOverProp S)).w }

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp` with the arguments in the
fiber products flipped. -/
@[simps -isSimp]
/--
Definition of `Cover.pullbackCoverOverProp'` / `Cover.pullbackCoverOverProp'` 的定义

English:
definition Cover.pullbackCoverOverProp'
  signature: : W.Cover (precoverage P) where
  body: 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  f x := (pullback.snd ((𝒰.f x).asOverProp S) (f.asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ 

中文:
定义 Cover.pullbackCoverOverProp'
  签名: : W.Cover (precoverage P) where
  定义体: 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  f x := (pullback.snd ((𝒰.f x).asOverProp S) (f.asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ 
-/
def Cover.pullbackCoverOverProp' : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  f x := (pullback.snd ((𝒰.f x).asOverProp S) (f.asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₂ f).f i) _
        ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
          ((𝒰.f _).asOverProp S) (f.asOverProp S)).inv)
        (PreservesPullback.iso_inv_snd _ _ _) x).mp hy
    · simp only [← CategoryTheory.Over.forget_map]
      rw [MorphismProperty.Comma.toCommaMorphism_eq_hom]; rw [← MorphismProperty.Comma.forget_map]; rw [← Functor.comp_map]
      rw [← PreservesPullback.iso_hom_snd]; rw [P.cancel_left_of_respectsIso]
      exact P.pullback_snd _ _ (𝒰.map_prop j)

instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOverProp' S f hX hW hQ).X j).Over S where
  hom := (pullback ((𝒰.f j).asOverProp (hX := hQ j) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝒰.pullbackCoverOverProp' S f hX hW hQ).Over S
  body: { comp_over := by exact (pullback.snd ((𝒰.f j).asOverProp S) (f.asOverProp S)).w }

中文:
实例 :
  签名: (𝒰.pullbackCoverOver命题' S f hX hW hQ).Over S
  定义体: { comp_over := by exact (pullback.snd ((𝒰.f j).asOverProp S) (f.asOverProp S)).w }

Depends on / 依赖: asOverProp, comp_over, f.asOverProp, pullback, pullback.snd
-/
instance : (𝒰.pullbackCoverOverProp' S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.snd ((𝒰.f j).asOverProp S) (f.asOverProp S)).w }

end

variable [P.IsStableUnderComposition]
variable {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (𝒱 : forall x, (𝒰.X x).Cover (precoverage P))
  [X.Over S] [𝒰.Over S] [forall x, (𝒱 x).Over S]

instance (j : (𝒰.bind 𝒱).I₀) : ((𝒰.bind 𝒱).X j).Over S :=
inferInstanceAs ((𝒱 j.1).X j.2).Over S

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (𝒱 : forall x, (𝒰.X x).Cover (precoverage P))
    [X.Over S] [𝒰.Over S] [forall x, (𝒱 x).Over S] : Cover.Over S (𝒰.bind 𝒱) where
over := fun ⟨i, j⟩ => inferInstanceAs ((𝒱 i).X j).Over S
  isOver_map := fun ⟨i, j⟩ => { comp_over := by simp; rfl }

end AlgebraicGeometry.Scheme
