/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Birationality and Rationality of schemes.

This file defines partial isomorphisms between schemes and uses them to formalize
birationality and rationality.

## Main definitions

- `Scheme.PartialIso X Y`: an isomorphism between a dense open subscheme of `X` and a
  dense open subscheme of `Y`.
- `Scheme.Birational X Y`: `X` and `Y` are birational, i.e. there exists a `PartialIso X Y`.
- `Scheme.BirationalOver sX sY`: `X` and `Y` are birational over `S` via structure maps
  `sX : X ⟶ S` and `sY : Y ⟶ S`.
- `Scheme.IsRationalOver sX`: `X` is rational over `S` via structure map `sX : X ⟶ S`,
  i.e. birational over `S` to some affine space `𝔸(n; S)`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/--
Definition of `PartialIso` / `PartialIso` 的定义

English:
structure PartialIso
  parameters: (X Y : Scheme.{u})
  axioms and operations (5):
    - source : X.Opens
    - dense_source : Dense (source : Set X)
    - target : Y.Opens
    - dense_target : Dense (target : Set Y)
    - iso : source.toScheme ≅ target.toScheme

中文:
结构 PartialIso
  参数: (X Y : 概形.{u})
  公理与运算 (5 个):
    - source : X.Opens
    - dense_source : 稠密 (source : 集合 X)
    - target : Y.Opens
    - dense_target : 稠密 (target : 集合 Y)
    - iso : source.toScheme ≅ target.toScheme

Depends on / 依赖: LocallyOfFinitePresentation, UniversallyOpen, UniversallyOpen.of_flat, of_flat
-/
structure PartialIso (X Y : Scheme.{u}) where
  /-- The source open subscheme of a partial isomorphism. -/
  source : X.Opens
  dense_source : Dense (source : Set X)
  /-- The target open subscheme of a partial isomorphism. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying isomorphism of a partial isomorphism. -/
  iso : source.toScheme ≅ target.toScheme

namespace PartialIso

variable {X Y Z S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}

variable (sX sY) in
/--
Definition of `IsOver` / `IsOver` 的定义

English:
abbreviation IsOver
  signature: (f : X.PartialIso Y)
  body: f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX

中文:
缩写 是Over
  签名: (f : X.PartialIso Y)
  定义体: f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX

Depends on / 依赖: f.iso.hom, f.source, f.target, source, target
-/
abbrev IsOver (f : X.PartialIso Y) : Prop :=
  f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX

/--
lemma `ext_iff` / 引理 `ext_iff`

English:
lemma ext_iff
  given: (f g : X.PartialIso Y)
  proof: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]

中文:
引理 ext_iff
  条件: (f g : X.PartialIso Y)
  证明: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]

Depends on / 依赖: forall_exists_index
-/
lemma ext_iff (f g : X.PartialIso Y) :
    f = g ↔ exists (e : f.source = g.source) (e' : g.target = f.target),
      f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
  proof: by
  rw [ext_iff]
  exact ⟨e, e', H⟩

中文:
引理 ext
  结论: (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
  证明: by
  rw [ext_iff]
  exact ⟨e, e', H⟩

Depends on / 依赖: WeaklyEtale, ext_iff
-/
lemma ext (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
    (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

variable (X) in
/-- The identity partial isomorphism on `X`, defined on all of `X`. -/
@[refl, simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : X.PartialIso X where
  body: ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

中文:
定义 refl
  签名: : X.PartialIso X where
  定义体: ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _
-/
def refl : X.PartialIso X where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

/-- The inverse of a partial isomorphism. -/
@[symm, simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : X.PartialIso Y)
  body: f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

中文:
定义 symm
  签名: (f : X.PartialIso Y)
  定义体: f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

Depends on / 依赖: f.target, target
-/
def symm (f : X.PartialIso Y) : Y.PartialIso X where
  source := f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsOver.symm` / 引理 `IsOver.symm`

English:
lemma IsOver.symm
  given: {f : X.PartialIso Y} (hf : f.IsOver sX sY)
  statement: f.symm.IsOver sY sX
  proof: by
  simpa [IsOver, ← cancel_epi f.iso.hom] using Eq.symm hf

中文:
引理 是Over.symm
  条件: {f : X.PartialIso Y} (hf : f.是Over sX sY)
  结论: f.symm.是Over sY sX
  证明: by
  simpa [IsOver, ← cancel_epi f.iso.hom] using Eq.symm hf

Depends on / 依赖: Eq.symm, IsOver, cancel_epi, f.iso.hom
-/
lemma IsOver.symm {f : X.PartialIso Y} (hf : f.IsOver sX sY) : f.symm.IsOver sY sX := by
  simpa [IsOver, ← cancel_epi f.iso.hom] using Eq.symm hf

/-- Compose two partial isomorphisms along a proof that the target of `f` equals the source
of `g`. See `trans` for the version that does not require this. -/
@[simps]
/--
Definition of `trans'` / `trans'` 的定义

English:
definition trans'
  signature: (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source)
  body: f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

中文:
定义 trans'
  签名: (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source)
  定义体: f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

Depends on / 依赖: f.source, source
-/
noncomputable def trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source) :
    X.PartialIso Z where
  source := f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsOver.trans'` / 引理 `IsOver.trans'`

English:
lemma IsOver.trans'
  statement: {f : X.PartialIso Y} {g : Y.PartialIso Z} {e : f.target = g.source}
  proof: by
  simp [IsOver, ← hf, hg]

中文:
引理 是Over.trans'
  结论: {f : X.PartialIso Y} {g : Y.PartialIso Z} {e : f.target = g.source}
  证明: by
  simp [IsOver, ← hf, hg]

Depends on / 依赖: IsOver
-/
lemma IsOver.trans' {f : X.PartialIso Y} {g : Y.PartialIso Z} {e : f.target = g.source}
    (hf : f.IsOver sX sY) (hg : g.IsOver sY sZ) : (trans' f g e).IsOver sX sZ := by
  simp [IsOver, ← hf, hg]

/-- Restrict the source of a partial isomorphism to a smaller dense open. -/
@[simps]
/--
Definition of `restrictSource` / `restrictSource` 的定义

English:
definition restrictSource
  signature: (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
  body: U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := Opens.isDominant_ι f.dense_target
f.target.ι.denseRange.dense_image f.target.ι.continuous
f.iso.hom.denseRange.dense_image f.iso.hom.continuous
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))

中文:
定义 restrictSource
  签名: (f : X.PartialIso Y) (U : Opens X) (hU : 稠密 (U : 集合 X))
  定义体: U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := Opens.isDominant_ι f.dense_target
f.target.ι.denseRange.dense_image f.target.ι.continuous
f.iso.hom.denseRange.dense_image f.iso.hom.continuous
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))
-/
noncomputable def restrictSource (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
    (hU' : U <= f.source) : X.PartialIso Y where
  source := U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := Opens.isDominant_ι f.dense_target
f.target.ι.denseRange.dense_image f.target.ι.continuous
f.iso.hom.denseRange.dense_image f.iso.hom.continuous
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsOver.restrictSource` / 引理 `IsOver.restrictSource`

English:
lemma IsOver.restrictSource
  statement: {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens X)
  proof: by
  simp [IsOver, hf]

中文:
引理 是Over.restrictSource
  结论: {f : X.PartialIso Y} (hf : f.是Over sX sY) (U : Opens X)
  证明: by
  simp [IsOver, hf]

Depends on / 依赖: IsOver, MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
lemma IsOver.restrictSource {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens X)
    (hU : Dense (U : Set X)) (hU' : U <= f.source) :
    (f.restrictSource U hU hU').IsOver sX sY := by
  simp [IsOver, hf]

/-- Restrict the target of a partial isomorphism to a smaller dense open. -/
@[simps! source target iso]
/--
Definition of `restrictTarget` / `restrictTarget` 的定义

English:
definition restrictTarget
  signature: (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
  body: (f.symm.restrictSource U hU hU').symm

中文:
定义 restrictTarget
  签名: (f : X.PartialIso Y) (U : Opens Y) (hU : 稠密 (U : 集合 Y))
  定义体: (f.symm.restrictSource U hU hU').symm

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, f.symm.restrictSource, pullback_snd, restrictSource
-/
noncomputable def restrictTarget (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
    (hU' : U <= f.target) : X.PartialIso Y :=
  (f.symm.restrictSource U hU hU').symm

/--
lemma `IsOver.restrictTarget` / 引理 `IsOver.restrictTarget`

English:
lemma IsOver.restrictTarget
  statement: {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens Y)
  proof: (hf.symm.restrictSource U hU hU').symm

中文:
引理 是Over.restrictTarget
  结论: {f : X.PartialIso Y} (hf : f.是Over sX sY) (U : Opens Y)
  证明: (hf.symm.restrictSource U hU hU').symm

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, hf.symm.restrictSource, restrict, restrictSource
-/
lemma IsOver.restrictTarget {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens Y)
    (hU : Dense (U : Set Y)) (hU' : U <= f.target) :
    (f.restrictTarget U hU hU').IsOver sX sY :=
  (hf.symm.restrictSource U hU hU').symm

/-- Compose two partial isomorphisms, restricting to the intersection of the intermediate opens. -/
@[trans, simps! source target iso]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : X.PartialIso Y) (g : Y.PartialIso Z)
  body: have := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  (f.restrictTarget _ this inf_le_left).trans' (g.restrictSource _ this inf_le_right) rfl

中文:
定义 trans
  签名: (f : X.PartialIso Y) (g : Y.PartialIso Z)
  定义体: have := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  (f.restrictTarget _ this inf_le_left).trans' (g.restrictSource _ this inf_le_right) rfl

Depends on / 依赖: Scheme, Scheme.Hom.resLE, dense_source, dense_target, f.dense_target.inter_of_isOpen_right, f.restrictTarget, g.dense_source, g.restrictSource, g.source, inf_le_left, inf_le_right, infer_instance, inter_of_isOpen_right, restrictSource, restrictTarget, source
-/
noncomputable def trans (f : X.PartialIso Y) (g : Y.PartialIso Z) : X.PartialIso Z :=
  have := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  (f.restrictTarget _ this inf_le_left).trans' (g.restrictSource _ this inf_le_right) rfl

/--
lemma `IsOver.trans` / 引理 `IsOver.trans`

English:
lemma IsOver.trans
  statement: {f : X.PartialIso Y} {g : Y.PartialIso Z} (hf : f.IsOver sX sY)
  proof: (hf.restrictTarget _ _ _).trans' (hg.restrictSource _ _ _)

中文:
引理 是Over.trans
  结论: {f : X.PartialIso Y} {g : Y.PartialIso Z} (hf : f.是Over sX sY)
  证明: (hf.restrictTarget _ _ _).trans' (hg.restrictSource _ _ _)

Depends on / 依赖: hf.restrictTarget, hg.restrictSource, restrictSource, restrictTarget
-/
lemma IsOver.trans {f : X.PartialIso Y} {g : Y.PartialIso Z} (hf : f.IsOver sX sY)
    (hg : g.IsOver sY sZ) : (f.trans g).IsOver sX sZ :=
  (hf.restrictTarget _ _ _).trans' (hg.restrictSource _ _ _)

/-- The underlying partial map of a partial isomorphism. -/
@[simps]
/--
Definition of `toPartialMap` / `toPartialMap` 的定义

English:
definition toPartialMap
  signature: (f : X.PartialIso Y)
  body: f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

中文:
定义 toPartialMap
  签名: (f : X.PartialIso Y)
  定义体: f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

Depends on / 依赖: f.source, source
-/
def toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where
  domain := f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

/--
Definition of `toRationalMap` / `toRationalMap` 的定义

English:
abbreviation toRationalMap
  signature: (f : X.PartialIso Y)
  body: f.toPartialMap.toRationalMap

中文:
缩写 toRationalMap
  签名: (f : X.PartialIso Y)
  定义体: f.toPartialMap.toRationalMap

Depends on / 依赖: f.toPartialMap.toRationalMap, toPartialMap, toRationalMap
-/
abbrev toRationalMap (f : X.PartialIso Y) : X ⤏ Y := f.toPartialMap.toRationalMap

/-- A scheme isomorphism viewed as a partial isomorphism defined on all of `X` and `Y`. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (f : X ≅ Y)
  body: ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

中文:
定义 ofIso
  签名: (f : X ≅ Y)
  定义体: ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm
-/
noncomputable def ofIso (f : X ≅ Y) : X.PartialIso Y where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end PartialIso

/-- `X` and `Y` are birational if there exists a partial isomorphism between them. -/
@[stacks 0A20 "(1)"]
/--
Definition of `Birational` / `Birational` 的定义

English:
definition Birational
  signature: (X Y : Scheme.{u})
  body: Nonempty (PartialIso X Y)

中文:
定义 Birational
  签名: (X Y : 概形.{u})
  定义体: Nonempty (PartialIso X Y)

Depends on / 依赖: Nonempty, PartialIso
-/
def Birational (X Y : Scheme.{u}) : Prop := Nonempty (PartialIso X Y)

/--
Definition of `Birational.partialIso` / `Birational.partialIso` 的定义

English:
definition Birational.partialIso
  signature: {X Y : Scheme.{u}} (h : Birational X Y)
  body: Classical.choice h

@[refl]

中文:
定义 Birational.partialIso
  签名: {X Y : 概形.{u}} (h : Birational X Y)
  定义体: Classical.choice h

@[refl]

Depends on / 依赖: Classical, Classical.choice, choice
-/
noncomputable def Birational.partialIso {X Y : Scheme.{u}} (h : Birational X Y) :
    PartialIso X Y :=
  Classical.choice h

@[refl]
/--
lemma `Birational.refl` / 引理 `Birational.refl`

English:
lemma Birational.refl
  given: (X : Scheme.{u})
  statement: Birational X X
  proof: ⟨.refl X⟩

@[symm]

中文:
引理 Birational.refl
  条件: (X : 概形.{u})
  结论: Birational X X
  证明: ⟨.refl X⟩

@[symm]
-/
lemma Birational.refl (X : Scheme.{u}) : Birational X X :=
  ⟨.refl X⟩

@[symm]
/--
lemma `Birational.symm` / 引理 `Birational.symm`

English:
lemma Birational.symm
  given: {X Y : Scheme.{u}} (h : Birational X Y)
  statement: Birational Y X
  proof: ⟨h.partialIso.symm⟩

@[trans]

中文:
引理 Birational.symm
  条件: {X Y : 概形.{u}} (h : Birational X Y)
  结论: Birational Y X
  证明: ⟨h.partialIso.symm⟩

@[trans]

Depends on / 依赖: h.partialIso.symm, partialIso
-/
lemma Birational.symm {X Y : Scheme.{u}} (h : Birational X Y) : Birational Y X :=
  ⟨h.partialIso.symm⟩

@[trans]
/--
lemma `Birational.trans` / 引理 `Birational.trans`

English:
lemma Birational.trans
  given: {X Y Z : Scheme.{u}} (h₁ : Birational X Y) (h₂ : Birational Y Z)
  proof: ⟨h₁.partialIso.trans h₂.partialIso⟩

中文:
引理 Birational.trans
  条件: {X Y Z : 概形.{u}} (h₁ : Birational X Y) (h₂ : Birational Y Z)
  证明: ⟨h₁.partialIso.trans h₂.partialIso⟩

Depends on / 依赖: partialIso, partialIso.trans
-/
lemma Birational.trans {X Y Z : Scheme.{u}} (h₁ : Birational X Y) (h₂ : Birational Y Z) :
    Birational X Z :=
  ⟨h₁.partialIso.trans h₂.partialIso⟩

/--
Definition of `BirationalOver` / `BirationalOver` 的定义

English:
definition BirationalOver
  signature: {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  body: exists f : PartialIso X Y, f.IsOver sX sY

中文:
定义 BirationalOver
  签名: {S X Y : 概形.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  定义体: exists f : PartialIso X Y, f.IsOver sX sY

Depends on / 依赖: IsOver, PartialIso, f.IsOver
-/
def BirationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) : Prop :=
  exists f : PartialIso X Y, f.IsOver sX sY

/--
Definition of `BirationalOver.partialIso` / `BirationalOver.partialIso` 的定义

English:
definition BirationalOver.partialIso
  signature: {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  body: h.choose

中文:
定义 BirationalOver.partialIso
  签名: {S X Y : 概形.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  定义体: h.choose

Depends on / 依赖: h.choose
-/
noncomputable def BirationalOver.partialIso {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) :=
  h.choose

/--
lemma `BirationalOver.partialIso_isOver` / 引理 `BirationalOver.partialIso_isOver`

English:
lemma BirationalOver.partialIso_isOver
  statement: {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  proof: h.choose_spec

中文:
引理 BirationalOver.partialIso_isOver
  结论: {S X Y : 概形.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  证明: h.choose_spec

Depends on / 依赖: choose_spec, h.choose_spec
-/
lemma BirationalOver.partialIso_isOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) : h.partialIso.IsOver sX sY :=
  h.choose_spec

set_option backward.defeqAttrib.useBackward true in
/--
lemma `BirationalOver.refl` / 引理 `BirationalOver.refl`

English:
lemma BirationalOver.refl
  given: {S X : Scheme.{u}} (sX : X ⟶ S)
  statement: BirationalOver sX sX
  proof: ⟨.refl X, by simp [PartialIso.IsOver]⟩

中文:
引理 BirationalOver.refl
  条件: {S X : 概形.{u}} (sX : X ⟶ S)
  结论: BirationalOver sX sX
  证明: ⟨.refl X, by simp [PartialIso.IsOver]⟩

Depends on / 依赖: IsOver, PartialIso, PartialIso.IsOver
-/
lemma BirationalOver.refl {S X : Scheme.{u}} (sX : X ⟶ S) : BirationalOver sX sX :=
  ⟨.refl X, by simp [PartialIso.IsOver]⟩

/--
lemma `BirationalOver.symm` / 引理 `BirationalOver.symm`

English:
lemma BirationalOver.symm
  statement: {S X Y : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
  proof: ⟨h.partialIso.symm, h.partialIso_isOver.symm⟩

中文:
引理 BirationalOver.symm
  结论: {S X Y : 概形.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
  证明: ⟨h.partialIso.symm, h.partialIso_isOver.symm⟩

Depends on / 依赖: h.partialIso.symm, h.partialIso_isOver.symm, partialIso, partialIso_isOver
-/
lemma BirationalOver.symm {S X Y : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    (h : BirationalOver sX sY) : BirationalOver sY sX :=
  ⟨h.partialIso.symm, h.partialIso_isOver.symm⟩

/--
lemma `BirationalOver.trans` / 引理 `BirationalOver.trans`

English:
lemma BirationalOver.trans
  statement: {S X Y Z : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
  proof: ⟨h₁.partialIso.trans h₂.partialIso, h₁.partialIso_isOver.trans h₂.partialIso_isOver⟩

中文:
引理 BirationalOver.trans
  结论: {S X Y Z : 概形.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
  证明: ⟨h₁.partialIso.trans h₂.partialIso, h₁.partialIso_isOver.trans h₂.partialIso_isOver⟩

Depends on / 依赖: partialIso, partialIso.trans, partialIso_isOver, partialIso_isOver.trans
-/
lemma BirationalOver.trans {S X Y Z : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
    (h₁ : BirationalOver sX sY) (h₂ : BirationalOver sY sZ) :
    BirationalOver sX sZ :=
  ⟨h₁.partialIso.trans h₂.partialIso, h₁.partialIso_isOver.trans h₂.partialIso_isOver⟩

/-- `X` is rational over `S` (or `S`-rational) if it is birational over `S` to some
affine space `𝔸(n; S)`. Note that we do not require `n` to be finite here. -/
@[mk_iff]
/--
Definition of `IsRationalOver` / `IsRationalOver` 的定义

English:
class IsRationalOver
  parameters: {S X : Scheme.{u}} (sX : X ⟶ S)
  axioms and operations (1):
    - exists_birationalOver_affineSpace((sX)) : exists (n : Type u), BirationalOver sX (𝔸(n; S) ↘ S)

中文:
类 是RationalOver
  参数: {S X : 概形.{u}} (sX : X ⟶ S)
  公理与运算 (1 个):
    - exists_birationalOver_affineSpace((sX)) : 存在 (n : 类型u), BirationalOver sX (𝔸(n; S) ↘ S)
-/
class IsRationalOver {S X : Scheme.{u}} (sX : X ⟶ S) : Prop where
  exists_birationalOver_affineSpace (sX) : exists (n : Type u), BirationalOver sX (𝔸(n; S) ↘ S)

instance (S : Scheme.{u}) (n : Type u) : IsRationalOver (𝔸(n; S) ↘ S) where
  exists_birationalOver_affineSpace := ⟨n, .refl _⟩

/--
lemma `BirationalOver.isRationalOver` / 引理 `BirationalOver.isRationalOver`

English:
lemma BirationalOver.isRationalOver
  statement: {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  proof: by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sY
  exact ⟨n, h.trans hn⟩

中文:
引理 BirationalOver.isRationalOver
  结论: {S X Y : 概形.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
  证明: by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sY
  exact ⟨n, h.trans hn⟩

Depends on / 依赖: IsRationalOver, IsRationalOver.exists_birationalOver_affineSpace, exists_birationalOver_affineSpace, h.trans
-/
lemma BirationalOver.isRationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsRationalOver sY] (h : BirationalOver sX sY) : IsRationalOver sX := by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sY
  exact ⟨n, h.trans hn⟩

section DenseOpen

variable {X S : Scheme.{u}} (U : Opens X) (sX : X ⟶ S)

/-- A dense open set `U : Opens X` induces a partial isomorphism between `U` and `X`. -/
@[simps]
/--
Definition of `Opens.partialIsoOfDense` / `Opens.partialIsoOfDense` 的定义

English:
definition Opens.partialIsoOfDense
  signature: (hU : Dense (U : Set X))
  body: ⊤
  dense_source := dense_univ
  target := U
  dense_target := hU
  iso := U.toScheme.topIso

中文:
定义 Opens.partialIsoOfDense
  签名: (hU : 稠密 (U : 集合 X))
  定义体: ⊤
  dense_source := dense_univ
  target := U
  dense_target := hU
  iso := U.toScheme.topIso
-/
def Opens.partialIsoOfDense (hU : Dense (U : Set X)) : PartialIso U X where
  source := ⊤
  dense_source := dense_univ
  target := U
  dense_target := hU
  iso := U.toScheme.topIso

/--
lemma `Opens.birational_of_dense` / 引理 `Opens.birational_of_dense`

English:
lemma Opens.birational_of_dense
  given: (hU : Dense (U : Set X))
  statement: Birational U X
  proof: ⟨U.partialIsoOfDense hU⟩

中文:
引理 Opens.birational_of_dense
  条件: (hU : 稠密 (U : 集合 X))
  结论: Birational U X
  证明: ⟨U.partialIsoOfDense hU⟩

Depends on / 依赖: U.partialIsoOfDense, partialIsoOfDense
-/
lemma Opens.birational_of_dense (hU : Dense (U : Set X)) : Birational U X :=
  ⟨U.partialIsoOfDense hU⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `Opens.birationalOver_of_dense` / 引理 `Opens.birationalOver_of_dense`

English:
lemma Opens.birationalOver_of_dense
  given: (hU : Dense (U : Set X))
  statement: BirationalOver (U.ι ≫ sX) sX
  proof: ⟨U.partialIsoOfDense hU, by simp [PartialIso.IsOver]⟩

中文:
引理 Opens.birationalOver_of_dense
  条件: (hU : 稠密 (U : 集合 X))
  结论: BirationalOver (U.ι ≫ sX) sX
  证明: ⟨U.partialIsoOfDense hU, by simp [PartialIso.IsOver]⟩

Depends on / 依赖: IsOver, PartialIso, PartialIso.IsOver, U.partialIsoOfDense, partialIsoOfDense
-/
lemma Opens.birationalOver_of_dense (hU : Dense (U : Set X)) : BirationalOver (U.ι ≫ sX) sX :=
  ⟨U.partialIsoOfDense hU, by simp [PartialIso.IsOver]⟩

/--
lemma `Opens.isRationalOver_of_dense` / 引理 `Opens.isRationalOver_of_dense`

English:
lemma Opens.isRationalOver_of_dense
  given: (hU : Dense (U : Set X)) [IsRationalOver sX]
  proof: by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sX
  exact ⟨n, (U.birationalOver_of_dense sX hU).trans hn⟩

中文:
引理 Opens.isRationalOver_of_dense
  条件: (hU : 稠密 (U : 集合 X)) [是RationalOver sX]
  证明: by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sX
  exact ⟨n, (U.birationalOver_of_dense sX hU).trans hn⟩

Depends on / 依赖: IsRationalOver, IsRationalOver.exists_birationalOver_affineSpace, U.birationalOver_of_dense, birationalOver_of_dense, exists_birationalOver_affineSpace
-/
lemma Opens.isRationalOver_of_dense (hU : Dense (U : Set X)) [IsRationalOver sX] :
    IsRationalOver (U.ι ≫ sX) := by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sX
  exact ⟨n, (U.birationalOver_of_dense sX hU).trans hn⟩

end DenseOpen

section OpenImmersion

variable {X U S : Scheme.{u}}

/-- A dominant open immersion `f : U ⟶ X` induces a partial isomorphism between `U` and `X`. -/
@[simps! source target iso]
/--
Definition of `Hom.partialIso` / `Hom.partialIso` 的定义

English:
definition Hom.partialIso
  signature: (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f]
  body: (PartialIso.ofIso f.isoOpensRange).trans' (f.opensRange.partialIsoOfDense f.denseRange) rfl

中文:
定义 态射.partialIso
  签名: (f : U ⟶ X) [是开浸入 f] [是Dominant f]
  定义体: (PartialIso.ofIso f.isoOpensRange).trans' (f.opensRange.partialIsoOfDense f.denseRange) rfl

Depends on / 依赖: PartialIso, PartialIso.ofIso, denseRange, f.denseRange, f.isoOpensRange, f.opensRange.partialIsoOfDense, isoOpensRange, opensRange, partialIsoOfDense
-/
noncomputable def Hom.partialIso (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : U.PartialIso X :=
  (PartialIso.ofIso f.isoOpensRange).trans' (f.opensRange.partialIsoOfDense f.denseRange) rfl

/--
lemma `Hom.birational` / 引理 `Hom.birational`

English:
lemma Hom.birational
  given: (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f]
  statement: Birational U X
  proof: ⟨f.partialIso⟩

中文:
引理 态射.birational
  条件: (f : U ⟶ X) [是开浸入 f] [是Dominant f]
  结论: Birational U X
  证明: ⟨f.partialIso⟩

Depends on / 依赖: f.partialIso, partialIso
-/
lemma Hom.birational (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : Birational U X :=
  ⟨f.partialIso⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `Hom.birationalOver` / 引理 `Hom.birationalOver`

English:
lemma Hom.birationalOver
  statement: (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] (sX : X ⟶ S) (sU : U ⟶ S)
  proof: ⟨f.partialIso, by simp [PartialIso.IsOver, hf]⟩

中文:
引理 态射.birationalOver
  结论: (f : U ⟶ X) [是开浸入 f] [是Dominant f] (sX : X ⟶ S) (sU : U ⟶ S)
  证明: ⟨f.partialIso, by simp [PartialIso.IsOver, hf]⟩

Depends on / 依赖: IsOver, PartialIso, PartialIso.IsOver, f.partialIso, partialIso
-/
lemma Hom.birationalOver (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] (sX : X ⟶ S) (sU : U ⟶ S)
    (hf : f ≫ sX = sU) : BirationalOver sU sX :=
  ⟨f.partialIso, by simp [PartialIso.IsOver, hf]⟩

end OpenImmersion

end AlgebraicGeometry.Scheme
