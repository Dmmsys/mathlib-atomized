/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Grothendieck topology defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated (pre)topology on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

## Implementation details

The pretopology is obtained from the precoverage `AlgebraicGeometry.Scheme.precoverage` defined in
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`. The definition is postponed to this file,
because the former does not have `HasPullbacks Scheme`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/--
Definition of `pretopology` / `pretopology` 的定义

English:
definition pretopology
  signature: (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
  body: (precoverage P).toPretopology

中文:
定义 pretopology
  签名: (P : Morphism命题erty Scheme.{u}) [P.IsStableUnderBaseChange]
  定义体: (precoverage P).toPretopology

Depends on / 依赖: precoverage, toPretopology
-/
def pretopology (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] : Pretopology Scheme.{u} :=
  (precoverage P).toPretopology

/--
Definition of `grothendieckTopology` / `grothendieckTopology` 的定义

English:
abbreviation grothendieckTopology
  signature: (P : MorphismProperty Scheme.{u})
  body: (precoverage P).toGrothendieck

中文:
缩写 grothendieckTopology
  签名: (P : Morphism命题erty Scheme.{u})
  定义体: (precoverage P).toGrothendieck

Depends on / 依赖: precoverage, toGrothendieck
-/
abbrev grothendieckTopology (P : MorphismProperty Scheme.{u}) :
    GrothendieckTopology Scheme.{u} :=
  (precoverage P).toGrothendieck

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: jointlySurjectivePrecoverage.IsStableUnderBaseChange
  body: isStableUnderBaseChange_comap_jointlySurjectivePrecoverage _
    fun f g _ => pullbackComparison_forget_surjective f g

中文:
实例 :
  签名: jointlySurjectivePrecoverage.IsStableUnderBaseChange
  定义体: isStableUnderBaseChange_comap_jointlySurjectivePrecoverage _
    fun f g _ => pullbackComparison_forget_surjective f g

Depends on / 依赖: isStableUnderBaseChange_comap_jointlySurjectivePrecoverage, pullbackComparison_forget_surjective
-/
instance : jointlySurjectivePrecoverage.IsStableUnderBaseChange :=
  isStableUnderBaseChange_comap_jointlySurjectivePrecoverage _
    fun f g _ => pullbackComparison_forget_surjective f g

/--
Definition of `jointlySurjectivePretopology` / `jointlySurjectivePretopology` 的定义

English:
definition jointlySurjectivePretopology
  signature: : Pretopology Scheme.{u}
  body: jointlySurjectivePrecoverage.toPretopology

中文:
定义 jointlySurjectivePretopology
  签名: : Pretopology Scheme.{u}
  定义体: jointlySurjectivePrecoverage.toPretopology

Depends on / 依赖: jointlySurjectivePrecoverage, jointlySurjectivePrecoverage.toPretopology, toPretopology
-/
def jointlySurjectivePretopology : Pretopology Scheme.{u} :=
  jointlySurjectivePrecoverage.toPretopology

variable {P : MorphismProperty Scheme.{u}}

@[grind ←]
/--
lemma `Cover.mem_grothendieckTopology` / 引理 `Cover.mem_grothendieckTopology`

English:
lemma Cover.mem_grothendieckTopology
  given: {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P))
  proof: Precoverage.generate_mem_toGrothendieck 𝒰.mem₀

中文:
引理 Cover.mem_grothendieckTopology
  条件: {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P))
  证明: Precoverage.generate_mem_toGrothendieck 𝒰.mem₀

Depends on / 依赖: Precoverage, Precoverage.generate_mem_toGrothendieck, generate_mem_toGrothendieck
-/
lemma Cover.mem_grothendieckTopology {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) :
    Sieve.ofArrows 𝒰.X 𝒰.f in grothendieckTopology P X :=
  Precoverage.generate_mem_toGrothendieck 𝒰.mem₀

/--
lemma `bot_mem_grothendieckTopology` / 引理 `bot_mem_grothendieckTopology`

English:
lemma bot_mem_grothendieckTopology
  given: (X : Scheme.{u}) [IsEmpty X]
  statement: ⊥ in grothendieckTopology P X
  proof: by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_precoverage _ X)

中文:
引理 bot_mem_grothendieckTopology
  条件: (X : Scheme.{u}) [IsEmpty X]
  结论: ⊥ in grothendieckTopology P X
  证明: by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_precoverage _ X)

Depends on / 依赖: Precoverage, Precoverage.generate_mem_toGrothendieck, Sieve.generate_bot, bot_mem_precoverage, generate_bot, generate_mem_toGrothendieck
-/
lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ in grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_precoverage _ X)

variable [P.IsStableUnderBaseChange] [P.IsMultiplicative]

@[grind ←]
/--
lemma `Cover.mem_pretopology` / 引理 `Cover.mem_pretopology`

English:
lemma Cover.mem_pretopology
  given: {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)}
  proof: 𝒰.mem₀

中文:
引理 Cover.mem_pretopology
  条件: {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)}
  证明: 𝒰.mem₀
-/
lemma Cover.mem_pretopology {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)} :
    Presieve.ofArrows 𝒰.X 𝒰.f in pretopology P X :=
  𝒰.mem₀

/--
lemma `mem_pretopology_iff` / 引理 `mem_pretopology_iff`

English:
lemma mem_pretopology_iff
  given: {X : Scheme.{u}} {R : Presieve X}
  proof: Precoverage.mem_iff_exists_zeroHypercover

alias ⟨exists_cover_of_mem_pretopology, _⟩ := mem_pretopology_iff

中文:
引理 mem_pretopology_iff
  条件: {X : Scheme.{u}} {R : Presieve X}
  证明: Precoverage.mem_iff_exists_zeroHypercover

alias ⟨exists_cover_of_mem_pretopology, _⟩ := mem_pretopology_iff

Depends on / 依赖: Precoverage, Precoverage.mem_iff_exists_zeroHypercover, mem_iff_exists_zeroHypercover
-/
lemma mem_pretopology_iff {X : Scheme.{u}} {R : Presieve X} :
    R in pretopology P X ↔ exists (𝒰 : Cover.{u + 1} (precoverage P) X),
    R = Presieve.ofArrows 𝒰.X 𝒰.f :=
  Precoverage.mem_iff_exists_zeroHypercover

alias ⟨exists_cover_of_mem_pretopology, _⟩ := mem_pretopology_iff

/--
lemma `mem_grothendieckTopology_iff` / 引理 `mem_grothendieckTopology_iff`

English:
lemma mem_grothendieckTopology_iff
  given: {X : Scheme.{u}} {S : Sieve X}
  proof: by
  simp_rw [grothendieckTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ => ?_, fun ⟨𝒰, hle⟩ => ⟨.ofArrows 𝒰.X 𝒰.f, 𝒰.mem_pretopology, hle⟩⟩
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨(𝒰 : Scheme.Cover _ _), rfl⟩ := hR
  use

中文:
引理 mem_grothendieckTopology_iff
  条件: {X : Scheme.{u}} {S : Sieve X}
  证明: by
  simp_rw [grothendieckTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ => ?_, fun ⟨𝒰, hle⟩ => ⟨.ofArrows 𝒰.X 𝒰.f, 𝒰.mem_pretopology, hle⟩⟩
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨(𝒰 : Scheme.Cover _ _), rfl⟩ := hR
  use

Depends on / 依赖: Precoverage, Precoverage.mem_iff_exists_zeroHypercover, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition, Scheme, Scheme.Cover, grothendieckTopology, le_trans, mem_iff_exists_zeroHypercover, mem_pretopology, mem_toGrothendieck_iff_of_isStableUnderComposition, ofArrows, simp_rw
-/
lemma mem_grothendieckTopology_iff {X : Scheme.{u}} {S : Sieve X} :
    S in grothendieckTopology P X ↔
      exists (𝒰 : Cover.{u} (precoverage P) X), Presieve.ofArrows 𝒰.X 𝒰.f <= S := by
  simp_rw [grothendieckTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ => ?_, fun ⟨𝒰, hle⟩ => ⟨.ofArrows 𝒰.X 𝒰.f, 𝒰.mem_pretopology, hle⟩⟩
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨(𝒰 : Scheme.Cover _ _), rfl⟩ := hR
  use 𝒰.ulift, le_trans (fun Y g ⟨i⟩ => .mk _) hle

alias ⟨exists_cover_of_mem_grothendieckTopology, _⟩ := mem_grothendieckTopology_iff

section

/--
Definition of `jointlySurjectiveTopology` / `jointlySurjectiveTopology` 的定义

English:
definition jointlySurjectiveTopology
  signature: : GrothendieckTopology Scheme.{u}
  body: jointlySurjectivePretopology.toGrothendieck.copy
(fun X => {s | ↑s in jointlySurjectivePretopology X})
    funext fun _ => Set.ext fun s =>
      ⟨fun ⟨_, hp, hps⟩ x => let ⟨Y, u, hu, hmem⟩ := hp x;
        ⟨Y, u, Presieve.map_monotone hps _ _ hu, hmem⟩,
      fun hs => ⟨s, hs, le_rfl⟩⟩

中文:
定义 jointlySurjectiveTopology
  签名: : GrothendieckTopology Scheme.{u}
  定义体: jointlySurjectivePretopology.toGrothendieck.copy
(fun X => {s | ↑s in jointlySurjectivePretopology X})
    funext fun _ => Set.ext fun s =>
      ⟨fun ⟨_, hp, hps⟩ x => let ⟨Y, u, hu, hmem⟩ := hp x;
        ⟨Y, u, Presieve.map_monotone hps _ _ hu, hmem⟩,
      fun hs => ⟨s, hs, le_rfl⟩⟩

Depends on / 依赖: Presieve, Presieve.map_monotone, Set.ext, jointlySurjectivePretopology, jointlySurjectivePretopology.toGrothendieck.copy, le_rfl, map_monotone, toGrothendieck
-/
def jointlySurjectiveTopology : GrothendieckTopology Scheme.{u} :=
  jointlySurjectivePretopology.toGrothendieck.copy
(fun X => {s | ↑s in jointlySurjectivePretopology X})
    funext fun _ => Set.ext fun s =>
      ⟨fun ⟨_, hp, hps⟩ x => let ⟨Y, u, hu, hmem⟩ := hp x;
        ⟨Y, u, Presieve.map_monotone hps _ _ hu, hmem⟩,
      fun hs => ⟨s, hs, le_rfl⟩⟩

/--
theorem `mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology` / 定理 `mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology`

English:
theorem mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
  proof: Iff.rfl

中文:
定理 mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
    {X : Scheme.{u}} {s : Sieve X} :
    s in jointlySurjectiveTopology X ↔ ↑s in jointlySurjectivePretopology X :=
  Iff.rfl

/--
lemma `jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology` / 引理 `jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology`

English:
lemma jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology
  proof: GrothendieckTopology.copy_eq

中文:
引理 jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology
  证明: GrothendieckTopology.copy_eq

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.copy_eq, copy_eq
-/
lemma jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology :
    jointlySurjectiveTopology.{u} = jointlySurjectivePretopology.toGrothendieck :=
  GrothendieckTopology.copy_eq

variable (P)

/--
lemma `pretopology_eq_inf` / 引理 `pretopology_eq_inf`

English:
lemma pretopology_eq_inf
  statement: pretopology P = jointlySurjectivePretopology ⊓ P.pretopology
  proof: rfl

中文:
引理 pretopology_eq_inf
  结论: pretopology P = jointlySurjectivePretopology ⊓ P.pretopology
  证明: rfl
-/
lemma pretopology_eq_inf : pretopology P = jointlySurjectivePretopology ⊓ P.pretopology := rfl

/--
lemma `grothendieckTopology_eq_inf` / 引理 `grothendieckTopology_eq_inf`

English:
lemma grothendieckTopology_eq_inf
  proof: by
  rw [grothendieckTopology]; rw [← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  rfl

中文:
引理 grothendieckTopology_eq_inf
  证明: by
  rw [grothendieckTopology]; rw [← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  rfl

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck, grothendieckTopology, toGrothendieck_toPretopology_eq_toGrothendieck
-/
lemma grothendieckTopology_eq_inf :
    grothendieckTopology P = (jointlySurjectivePretopology ⊓ P.pretopology).toGrothendieck := by
  rw [grothendieckTopology]; rw [← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  rfl

end

section

variable {P Q : MorphismProperty Scheme.{u}}

/--
lemma `grothendieckTopology_monotone` / 引理 `grothendieckTopology_monotone`

English:
lemma grothendieckTopology_monotone
  given: (hPQ : P <= Q)
  proof: Precoverage.toGrothendieck_mono (precoverage_mono hPQ)

中文:
引理 grothendieckTopology_monotone
  条件: (hPQ : P <= Q)
  证明: Precoverage.toGrothendieck_mono (precoverage_mono hPQ)

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_mono, precoverage_mono, toGrothendieck_mono
-/
lemma grothendieckTopology_monotone (hPQ : P <= Q) :
    grothendieckTopology P <= grothendieckTopology Q :=
  Precoverage.toGrothendieck_mono (precoverage_mono hPQ)

variable [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/--
lemma `pretopology_monotone` / 引理 `pretopology_monotone`

English:
lemma pretopology_monotone
  given: (hPQ : P <= Q)
  statement: pretopology P <= pretopology Q
  proof: precoverage_mono hPQ

中文:
引理 pretopology_monotone
  条件: (hPQ : P <= Q)
  结论: pretopology P <= pretopology Q
  证明: precoverage_mono hPQ

Depends on / 依赖: precoverage_mono
-/
lemma pretopology_monotone (hPQ : P <= Q) : pretopology P <= pretopology Q :=
  precoverage_mono hPQ

end

end AlgebraicGeometry.Scheme
