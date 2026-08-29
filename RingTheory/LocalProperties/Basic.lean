/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.RingHomProperties

/-!
# Local properties of commutative rings

In this file, we define local properties in general.

## Naming Conventions

* `localization_P` : `P` holds for `S⁻¹R` if `P` holds for `R`.
* `P_of_localization_maximal` : `P` holds for `R` if `P` holds for `Rₘ` for all maximal `m`.
* `P_of_localization_prime` : `P` holds for `R` if `P` holds for `Rₘ` for all prime `m`.
* `P_ofLocalizationSpan` : `P` holds for `R` if given a spanning set `{fᵢ}`, `P` holds for all
  `R_{fᵢ}`.

## Main definitions

* `LocalizationPreserves` : A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`.
* `OfLocalizationMaximal` : A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`.
* `RingHom.LocalizationPreserves` : A property `P` of ring homs is said to be preserved by
  localization if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`.
* `RingHom.OfLocalizationSpan` : A property `P` of ring homs satisfies
  `RingHom.OfLocalizationSpan` if `P` holds for `R →+* S` whenever there exists a
  set `{ r }` that spans `R` such that `P` holds for `Rᵣ →+* Sᵣ`.

## Main results

* The triviality of an ideal or an element:
  `ideal_eq_bot_of_localization`, `eq_zero_of_localization`

-/

@[expose] public section

open scoped Pointwise

universe u

section Properties

variable {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S)
variable (R' S' : Type u) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

section CommRing

variable (P : forall (R : Type u) [CommRing R], Prop)

/--
Definition of `LocalizationPreserves` / `LocalizationPreserves` 的定义

English:
definition LocalizationPreserves
  signature: : Prop
  body: forall {R : Type u} [hR : CommRing R] (M : Submonoid R) (S : Type u) [hS : CommRing S] [Algebra R S]
    [IsLocalization M S], @P R hR -> @P S hS

中文:
定义 LocalizationPreserves
  签名: : 命题
  定义体: forall {R : Type u} [hR : CommRing R] (M : Submonoid R) (S : Type u) [hS : CommRing S] [Algebra R S]
    [IsLocalization M S], @P R hR -> @P S hS

Depends on / 依赖: Algebra, CommRing, IsLocalization, Submonoid
-/
def LocalizationPreserves : Prop :=
  forall {R : Type u} [hR : CommRing R] (M : Submonoid R) (S : Type u) [hS : CommRing S] [Algebra R S]
    [IsLocalization M S], @P R hR -> @P S hS

/--
Definition of `OfLocalizationMaximal` / `OfLocalizationMaximal` 的定义

English:
definition OfLocalizationMaximal
  signature: : Prop
  body: forall (R : Type u) [CommRing R],
    (forall (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J)) -> P R

中文:
定义 OfLocalizationMaximal
  签名: : 命题
  定义体: forall (R : Type u) [CommRing R],
    (forall (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J)) -> P R

Depends on / 依赖: AtPrime, CommRing, IsMaximal, J.IsMaximal, Localization, Localization.AtPrime
-/
def OfLocalizationMaximal : Prop :=
  forall (R : Type u) [CommRing R],
    (forall (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J)) -> P R

end CommRing

section RingHom

variable (P : forall {R S : Type u} [CommRing R] [CommRing S] (_ : R ->+* S), Prop)

/--
Definition of `RingHom.ContainsIdentities` / `RingHom.ContainsIdentities` 的定义

English:
definition RingHom.ContainsIdentities
  body: forall (R : Type u) [CommRing R], P (RingHom.id R)

中文:
定义 环态射.余ntainsIdentities
  定义体: forall (R : Type u) [CommRing R], P (RingHom.id R)

Depends on / 依赖: CommRing, RingHom, RingHom.id
-/
def RingHom.ContainsIdentities := forall (R : Type u) [CommRing R], P (RingHom.id R)

/--
Definition of `RingHom.LocalizationPreserves` / `RingHom.LocalizationPreserves` 的定义

English:
definition RingHom.LocalizationPreserves
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (M : Submonoid R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization M R']
    [IsLocalization (M.map f) S'],
    P f -> P (IsLocalization.map S' f (Submonoid.le_comap_map M) : R' ->+* S')

中文:
定义 环态射.LocalizationPreserves
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (M : Submonoid R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization M R']
    [IsLocalization (M.map f) S'],
    P f -> P (IsLocalization.map S' f (Submonoid.le_comap_map M) : R' ->+* S')

Depends on / 依赖: Algebra, CommRing, IsLocalization, IsLocalization.map, M.map, Submonoid, Submonoid.le_comap_map, le_comap_map
-/
def RingHom.LocalizationPreserves :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (M : Submonoid R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization M R']
    [IsLocalization (M.map f) S'],
    P f -> P (IsLocalization.map S' f (Submonoid.le_comap_map M) : R' ->+* S')

/--
Definition of `RingHom.LocalizationAwayPreserves` / `RingHom.LocalizationAwayPreserves` 的定义

English:
definition RingHom.LocalizationAwayPreserves
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (r : R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'],
    P f -> P (IsLocalization.Away.map R' S' f r : R' ->+* S')

中文:
定义 环态射.LocalizationAwayPreserves
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (r : R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'],
    P f -> P (IsLocalization.Away.map R' S' f r : R' ->+* S')

Depends on / 依赖: Algebra, CommRing, IsLocalization, IsLocalization.Away, IsLocalization.Away.map
-/
def RingHom.LocalizationAwayPreserves :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (r : R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'],
    P f -> P (IsLocalization.Away.map R' S' f r : R' ->+* S')

/--
Definition of `RingHom.OfLocalizationFiniteSpan` / `RingHom.OfLocalizationFiniteSpan` 的定义

English:
definition RingHom.OfLocalizationFiniteSpan
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : forall r : s, P (Localization.awayMap f r)), P f

中文:
定义 环态射.OfLocalizationFiniteSpan
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : forall r : s, P (Localization.awayMap f r)), P f

Depends on / 依赖: CommRing, Finset, Ideal.span, Localization, Localization.awayMap, awayMap
-/
def RingHom.OfLocalizationFiniteSpan :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : forall r : s, P (Localization.awayMap f r)), P f

/--
Definition of `RingHom.OfLocalizationSpan` / `RingHom.OfLocalizationSpan` 的定义

English:
definition RingHom.OfLocalizationSpan
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : forall r : s, P (Localization.awayMap f r)), P f

中文:
定义 环态射.OfLocalizationSpan
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : forall r : s, P (Localization.awayMap f r)), P f

Depends on / 依赖: CommRing, Ideal.span, Localization, Localization.awayMap, awayMap
-/
def RingHom.OfLocalizationSpan :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : forall r : s, P (Localization.awayMap f r)), P f

/--
Definition of `RingHom.HoldsForLocalization` / `RingHom.HoldsForLocalization` 的定义

English:
definition RingHom.HoldsForLocalization
  signature: : Prop
  body: forall ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S], P (algebraMap R S)

中文:
定义 环态射.HoldsForLocalization
  签名: : 命题
  定义体: forall ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S], P (algebraMap R S)

Depends on / 依赖: Algebra, CommRing, IsLocalization, Submonoid, algebraMap
-/
def RingHom.HoldsForLocalization : Prop :=
  forall ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S], P (algebraMap R S)

/--
Definition of `RingHom.HoldsForLocalizationAway` / `RingHom.HoldsForLocalizationAway` 的定义

English:
definition RingHom.HoldsForLocalizationAway
  signature: : Prop
  body: forall ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)

中文:
定义 环态射.HoldsForLocalizationAway
  签名: : 命题
  定义体: forall ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)

Depends on / 依赖: Algebra, CommRing, IsLocalization, IsLocalization.Away, algebraMap
-/
def RingHom.HoldsForLocalizationAway : Prop :=
  forall ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)

/--
Definition of `RingHom.StableUnderCompositionWithLocalizationAwaySource` / `RingHom.StableUnderCompositionWithLocalizationAwaySource` 的定义

English:
definition RingHom.StableUnderCompositionWithLocalizationAwaySource
  signature: : Prop
  body: forall ⦃R : Type u⦄ (S : Type u) ⦃T : Type u⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (f : S ->+* T), P f -> P (f.comp (algebraMap R S))

中文:
定义 环态射.StableUnderCompositionWithLocalizationAwaySource
  签名: : 命题
  定义体: forall ⦃R : Type u⦄ (S : Type u) ⦃T : Type u⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (f : S ->+* T), P f -> P (f.comp (algebraMap R S))

Depends on / 依赖: Algebra, CommRing, IsLocalization, IsLocalization.Away, algebraMap, f.comp
-/
def RingHom.StableUnderCompositionWithLocalizationAwaySource : Prop :=
  forall ⦃R : Type u⦄ (S : Type u) ⦃T : Type u⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (f : S ->+* T), P f -> P (f.comp (algebraMap R S))

/--
Definition of `RingHom.StableUnderCompositionWithLocalizationAwayTarget` / `RingHom.StableUnderCompositionWithLocalizationAwayTarget` 的定义

English:
definition RingHom.StableUnderCompositionWithLocalizationAwayTarget
  signature: : Prop
  body: forall ⦃R S : Type u⦄ (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra S T] (s : S)
    [IsLocalization.Away s T] (f : R ->+* S), P f -> P ((algebraMap S T).comp f)

中文:
定义 环态射.StableUnderCompositionWithLocalizationAwayTarget
  签名: : 命题
  定义体: forall ⦃R S : Type u⦄ (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra S T] (s : S)
    [IsLocalization.Away s T] (f : R ->+* S), P f -> P ((algebraMap S T).comp f)

Depends on / 依赖: Algebra, CommRing, IsLocalization, IsLocalization.Away, algebraMap
-/
def RingHom.StableUnderCompositionWithLocalizationAwayTarget : Prop :=
  forall ⦃R S : Type u⦄ (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra S T] (s : S)
    [IsLocalization.Away s T] (f : R ->+* S), P f -> P ((algebraMap S T).comp f)

/--
Definition of `RingHom.StableUnderCompositionWithLocalizationAway` / `RingHom.StableUnderCompositionWithLocalizationAway` 的定义

English:
definition RingHom.StableUnderCompositionWithLocalizationAway
  signature: : Prop
  body: StableUnderCompositionWithLocalizationAwaySource P ∧
    StableUnderCompositionWithLocalizationAwayTarget P

中文:
定义 环态射.StableUnderCompositionWithLocalizationAway
  签名: : 命题
  定义体: StableUnderCompositionWithLocalizationAwaySource P ∧
    StableUnderCompositionWithLocalizationAwayTarget P

Depends on / 依赖: StableUnderCompositionWithLocalizationAwaySource, StableUnderCompositionWithLocalizationAwayTarget
-/
def RingHom.StableUnderCompositionWithLocalizationAway : Prop :=
  StableUnderCompositionWithLocalizationAwaySource P ∧
    StableUnderCompositionWithLocalizationAwayTarget P

/--
Definition of `RingHom.OfLocalizationFiniteSpanTarget` / `RingHom.OfLocalizationFiniteSpanTarget` 的定义

English:
definition RingHom.OfLocalizationFiniteSpanTarget
  signature: : Prop
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Finset S)
    (_ : Ideal.span (s : Set S) = ⊤)
    (_ : forall r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

中文:
定义 环态射.OfLocalizationFiniteSpanTarget
  签名: : 命题
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Finset S)
    (_ : Ideal.span (s : Set S) = ⊤)
    (_ : forall r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

Depends on / 依赖: CommRing, Finset, Ideal.span, Localization, Localization.Away, algebraMap
-/
def RingHom.OfLocalizationFiniteSpanTarget : Prop :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Finset S)
    (_ : Ideal.span (s : Set S) = ⊤)
    (_ : forall r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

/--
Definition of `RingHom.OfLocalizationSpanTarget` / `RingHom.OfLocalizationSpanTarget` 的定义

English:
definition RingHom.OfLocalizationSpanTarget
  signature: : Prop
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Set S) (_ : Ideal.span s = ⊤)
    (_ : forall r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

中文:
定义 环态射.OfLocalizationSpanTarget
  签名: : 命题
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Set S) (_ : Ideal.span s = ⊤)
    (_ : forall r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

Depends on / 依赖: CommRing, Ideal.span, Localization, Localization.Away, algebraMap
-/
def RingHom.OfLocalizationSpanTarget : Prop :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S) (s : Set S) (_ : Ideal.span s = ⊤)
    (_ : forall r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

/--
Definition of `RingHom.OfLocalizationPrime` / `RingHom.OfLocalizationPrime` 的定义

English:
definition RingHom.OfLocalizationPrime
  signature: : Prop
  body: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S),
    (forall (J : Ideal S) (_ : J.IsPrime), P (Localization.localRingHom _ J f rfl)) -> P f

中文:
定义 环态射.OfLocalizationPrime
  签名: : 命题
  定义体: forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S),
    (forall (J : Ideal S) (_ : J.IsPrime), P (Localization.localRingHom _ J f rfl)) -> P f

Depends on / 依赖: CommRing, IsPrime, J.IsPrime, Localization, Localization.localRingHom, localRingHom
-/
def RingHom.OfLocalizationPrime : Prop :=
  forall ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R ->+* S),
    (forall (J : Ideal S) (_ : J.IsPrime), P (Localization.localRingHom _ J f rfl)) -> P f

/--
Definition of `RingHom.PropertyIsLocal` / `RingHom.PropertyIsLocal` 的定义

English:
structure RingHom.PropertyIsLocal
  parameters: : Prop where
  axioms and operations (4):
    - localizationAwayPreserves : RingHom.LocalizationAwayPreserves @P
    - ofLocalizationSpanTarget : RingHom.OfLocalizationSpanTarget @P
    - ofLocalizationSpan : RingHom.OfLocalizationSpan @P
    - StableUnderCompositionWithLocalizationAwayTarget : RingHom.StableUnderCompositionWithLocalizationAwayTarget @P

中文:
结构 环态射.PropertyIsLocal
  参数: : 命题 where
  公理与运算 (4 个):
    - localizationAwayPreserves : 环态射.LocalizationAwayPreserves @P
    - ofLocalizationSpanTarget : 环态射.OfLocalizationSpanTarget @P
    - ofLocalizationSpan : 环态射.OfLocalizationSpan @P
    - StableUnderCompositionWithLocalizationAwayTarget : 环态射.StableUnderCompositionWithLocalizationAwayTarget @P
-/
structure RingHom.PropertyIsLocal : Prop where
  localizationAwayPreserves : RingHom.LocalizationAwayPreserves @P
  ofLocalizationSpanTarget : RingHom.OfLocalizationSpanTarget @P
  ofLocalizationSpan : RingHom.OfLocalizationSpan @P
  StableUnderCompositionWithLocalizationAwayTarget :
    RingHom.StableUnderCompositionWithLocalizationAwayTarget @P

/--
theorem `RingHom.ofLocalizationSpan_iff_finite` / 定理 `RingHom.ofLocalizationSpan_iff_finite`

English:
theorem RingHom.ofLocalizationSpan_iff_finite
  proof: by
  delta RingHom.OfLocalizationSpan RingHom.OfLocalizationFiniteSpan
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x 

中文:
定理 环态射.ofLocalizationSpan_iff_finite
  证明: by
  delta RingHom.OfLocalizationSpan RingHom.OfLocalizationFiniteSpan
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x 

Depends on / 依赖: OfLocalizationFiniteSpan, OfLocalizationSpan, RingHom, RingHom.OfLocalizationFiniteSpan, RingHom.OfLocalizationSpan
-/
theorem RingHom.ofLocalizationSpan_iff_finite :
    RingHom.OfLocalizationSpan @P ↔ RingHom.OfLocalizationFiniteSpan @P := by
  delta RingHom.OfLocalizationSpan RingHom.OfLocalizationFiniteSpan
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩

/--
theorem `RingHom.ofLocalizationSpanTarget_iff_finite` / 定理 `RingHom.ofLocalizationSpanTarget_iff_finite`

English:
theorem RingHom.ofLocalizationSpanTarget_iff_finite
  proof: by
  delta RingHom.OfLocalizationSpanTarget RingHom.OfLocalizationFiniteSpanTarget
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h 

中文:
定理 环态射.ofLocalizationSpanTarget_iff_finite
  证明: by
  delta RingHom.OfLocalizationSpanTarget RingHom.OfLocalizationFiniteSpanTarget
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h 

Depends on / 依赖: OfLocalizationFiniteSpanTarget, OfLocalizationSpanTarget, RingHom, RingHom.OfLocalizationFiniteSpanTarget, RingHom.OfLocalizationSpanTarget
-/
theorem RingHom.ofLocalizationSpanTarget_iff_finite :
    RingHom.OfLocalizationSpanTarget @P ↔ RingHom.OfLocalizationFiniteSpanTarget @P := by
  delta RingHom.OfLocalizationSpanTarget RingHom.OfLocalizationFiniteSpanTarget
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `RingHom.OfLocalizationSpan.mk` / 引理 `RingHom.OfLocalizationSpan.mk`

English:
lemma RingHom.OfLocalizationSpan.mk
  statement: (hP : RingHom.RespectsIso P)
  proof: by
  introv R hs hf
  algebraize [f]
  let _ := fun r : R => (Localization.awayMap (algebraMap R S) r).toAlgebra
  refine H s hs (fun r hr => ?_)
  have : algebraMap (Localization.Away r) (Localization.Away r otimes[R] S) =
      ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).symm

中文:
引理 环态射.OfLocalizationSpan.mk
  结论: (hP : 环态射.RespectsIso P)
  证明: by
  introv R hs hf
  algebraize [f]
  let _ := fun r : R => (Localization.awayMap (algebraMap R S) r).toAlgebra
  refine H s hs (fun r hr => ?_)
  have : algebraMap (Localization.Away r) (Localization.Away r otimes[R] S) =
      ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).symm

Depends on / 依赖: IsLocalization, IsLocalization.Away.tensorRightEquiv, IsLocalization.ringHom_ext, Localization, Localization.Away, Localization.awayMap, RingHom, RingHom.algebraMap_toAlgebra, Submonoid, Submonoid.powers, algebraMap, algebraMap_toAlgebra, algebraize, awayMap, introv, otimes, powers, ringHom_ext, tensorRightEquiv, toAlgebra
-/
lemma RingHom.OfLocalizationSpan.mk (hP : RingHom.RespectsIso P)
    (H : forall {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : Set R),
      Ideal.span s = ⊤ ->
      (forall r in s, P (algebraMap (Localization.Away r) (Localization.Away r otimes[R] S))) ->
      P (algebraMap R S)) :
    OfLocalizationSpan P := by
  introv R hs hf
  algebraize [f]
  let _ := fun r : R => (Localization.awayMap (algebraMap R S) r).toAlgebra
  refine H s hs (fun r hr => ?_)
  have : algebraMap (Localization.Away r) (Localization.Away r otimes[R] S) =
      ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).symm : _ ->+* _).comp
        (algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext
    simp [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
  rw [this]
  exact hP.1 _ _ (hf ⟨r, hr⟩)

section HoldsForLocalization

variable {P}

/--
lemma `RingHom.HoldsForLocalization.mk` / 引理 `RingHom.HoldsForLocalization.mk`

English:
lemma RingHom.HoldsForLocalization.mk
  statement: (hP : RespectsIso P)
  proof: by
  introv R _
  rw [← (IsLocalization.algEquiv M (Localization M) S).toAlgHom.comp_algebraMap]
  exact hP.1 _ _ (H _)

中文:
引理 环态射.HoldsForLocalization.mk
  结论: (hP : RespectsIso P)
  证明: by
  introv R _
  rw [← (IsLocalization.algEquiv M (Localization M) S).toAlgHom.comp_algebraMap]
  exact hP.1 _ _ (H _)

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, Localization, TopologicalSpace, algEquiv, comp_algebraMap, continuousMul_of_discreteTopology, introv, toAlgHom, toAlgHom.comp_algebraMap
-/
lemma RingHom.HoldsForLocalization.mk (hP : RespectsIso P)
    (H : forall {R : Type u} [CommRing R] (M : Submonoid R), P (algebraMap R (Localization M))) :
    HoldsForLocalization P := by
  introv R _
  rw [← (IsLocalization.algEquiv M (Localization M) S).toAlgHom.comp_algebraMap]
  exact hP.1 _ _ (H _)

/--
lemma `RingHom.HoldsForLocalization.holdsForLocalizationAway` / 引理 `RingHom.HoldsForLocalization.holdsForLocalizationAway`

English:
lemma RingHom.HoldsForLocalization.holdsForLocalizationAway
  given: (hP : HoldsForLocalization P)
  proof: fun _ _ _ _ _ r _ => hP _ (Submonoid.powers r)

中文:
引理 环态射.HoldsForLocalization.holdsForLocalizationAway
  条件: (hP : HoldsForLocalization P)
  证明: fun _ _ _ _ _ r _ => hP _ (Submonoid.powers r)

Depends on / 依赖: Submonoid, Submonoid.powers, TopologicalSpace, continuousMul_of_indiscreteTopology, powers
-/
lemma RingHom.HoldsForLocalization.holdsForLocalizationAway (hP : HoldsForLocalization P) :
    HoldsForLocalizationAway P :=
  fun _ _ _ _ _ r _ => hP _ (Submonoid.powers r)

/--
lemma `RingHom.HoldsForLocalization.isLocalizationMap` / 引理 `RingHom.HoldsForLocalization.isLocalizationMap`

English:
lemma RingHom.HoldsForLocalization.isLocalizationMap
  proof: by
  have hle : Submonoid.map f M <= T := by simpa [Submonoid.map_le_iff_le_comap]
  let : Algebra (Localization (M.map f)) S' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (M.map f) T hle
  have : IsScalarTower S (Localization (Submonoid.map f M)) S' :=
    IsLocalization.localization_

中文:
引理 环态射.HoldsForLocalization.isLocalizationMap
  证明: by
  have hle : Submonoid.map f M <= T := by simpa [Submonoid.map_le_iff_le_comap]
  let : Algebra (Localization (M.map f)) S' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (M.map f) T hle
  have : IsScalarTower S (Localization (Submonoid.map f M)) S' :=
    IsLocalization.localization_

Depends on / 依赖: Algebra, IsLocalization, IsLocalization.isLocalization_of_submonoid_le, IsLocalization.localizationAlgebraOfSubmonoidLe, IsLocalization.localization_isScalarTower_of_submonoid_le, IsScalarTower, Localization, M.map, Submonoid, Submonoid.map, Submonoid.map_le_iff_le_comap, T.map, algebraMap, isLocalization_of_submonoid_le, localizationAlgebraOfSubmonoidLe, localization_isScalarTower_of_submonoid_le, map_le_iff_le_comap
-/
lemma RingHom.HoldsForLocalization.isLocalizationMap
    (hPc : StableUnderComposition P) (hPp : LocalizationPreserves P)
    (hPl : HoldsForLocalization P)
    {M : Submonoid R} {T : Submonoid S}
    {R' : Type u} [CommRing R'] [Algebra R R'] [IsLocalization M R']
    (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization T S']
    {f : R ->+* S} (hy : M <= Submonoid.comap f T) (hf : P f) :
    P (IsLocalization.map (S := R') S' f hy) := by
  have hle : Submonoid.map f M <= T := by simpa [Submonoid.map_le_iff_le_comap]
  let : Algebra (Localization (M.map f)) S' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (M.map f) T hle
  have : IsScalarTower S (Localization (Submonoid.map f M)) S' :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  have : IsLocalization (T.map (algebraMap S (Localization (M.map f)))) S' :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (M.map f) T hle
  have heq : IsLocalization.map (S := R') S' f hy =
      (algebraMap _ _).comp
        (IsLocalization.map (M := M) (T := M.map f) (S := R') (Localization (M.map f)) f
          (M.le_comap_map)) := by
    apply IsLocalization.ringHom_ext M
    ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [heq]
  exact hPc _ _ (hPp _ _ _ _ hf) (hPl _ (T.map (algebraMap S (Localization (M.map f)))))

/--
lemma `RingHom.HoldsForLocalization.localRingHom` / 引理 `RingHom.HoldsForLocalization.localRingHom`

English:
lemma RingHom.HoldsForLocalization.localRingHom
  statement: (hPc : StableUnderComposition P)
  proof: hPl.isLocalizationMap hPc hPp _ _ hf

中文:
引理 环态射.HoldsForLocalization.localRingHom
  结论: (hPc : StableUnderComposition P)
  证明: hPl.isLocalizationMap hPc hPp _ _ hf

Depends on / 依赖: hPl.isLocalizationMap, isLocalizationMap
-/
lemma RingHom.HoldsForLocalization.localRingHom (hPc : StableUnderComposition P)
    (hPp : LocalizationPreserves P) (hPl : HoldsForLocalization P)
    {R S : Type u} [CommRing R] [CommRing S] {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime]
    {f : R ->+* S} (h : p = q.comap f) (hf : P f) :
    P (Localization.localRingHom p q f h) :=
  hPl.isLocalizationMap hPc hPp _ _ hf

end HoldsForLocalization

/--
theorem `RingHom.HoldsForLocalizationAway.of_bijective` / 定理 `RingHom.HoldsForLocalizationAway.of_bijective`

English:
theorem RingHom.HoldsForLocalizationAway.of_bijective
  proof: by
  let := f.toAlgebra
  have := IsLocalization.of_le_isUnit (S := .powers (1 : R)) (by simp)
  have := IsLocalization.isLocalization_of_algEquiv (.powers (1 : R))
    (AlgEquiv.ofBijective (Algebra.ofId R S) hf)
  exact H _ 1

中文:
定理 环态射.HoldsForLocalizationAway.of_bijective
  证明: by
  let := f.toAlgebra
  have := IsLocalization.of_le_isUnit (S := .powers (1 : R)) (by simp)
  have := IsLocalization.isLocalization_of_algEquiv (.powers (1 : R))
    (AlgEquiv.ofBijective (Algebra.ofId R S) hf)
  exact H _ 1

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.ofId, IsLocalization, IsLocalization.isLocalization_of_algEquiv, IsLocalization.of_le_isUnit, f.toAlgebra, isLocalization_of_algEquiv, ofBijective, of_le_isUnit, powers, toAlgebra
-/
theorem RingHom.HoldsForLocalizationAway.of_bijective
    (H : RingHom.HoldsForLocalizationAway P) (hf : Function.Bijective f) :
    P f := by
  let := f.toAlgebra
  have := IsLocalization.of_le_isUnit (S := .powers (1 : R)) (by simp)
  have := IsLocalization.isLocalization_of_algEquiv (.powers (1 : R))
    (AlgEquiv.ofBijective (Algebra.ofId R S) hf)
  exact H _ 1

variable {P f R' S'}

/--
lemma `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway` / 引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway`

English:
lemma RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
  proof: by
  constructor
  · introv _ _ hf
    exact hPc _ _ (hPl S r) hf
  · introv _ _ hf
    exact hPc _ _ hf (hPl T s)

中文:
引理 环态射.StableUnderComposition.stableUnderCompositionWithLocalizationAway
  证明: by
  constructor
  · introv _ _ hf
    exact hPc _ _ (hPl S r) hf
  · introv _ _ hf
    exact hPc _ _ hf (hPl T s)

Depends on / 依赖: introv
-/
lemma RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
    (hPc : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizationAway P) :
    StableUnderCompositionWithLocalizationAway P := by
  constructor
  · introv _ _ hf
    exact hPc _ _ (hPl S r) hf
  · introv _ _ hf
    exact hPc _ _ hf (hPl T s)

/--
lemma `RingHom.HoldsForLocalizationAway.containsIdentities` / 引理 `RingHom.HoldsForLocalizationAway.containsIdentities`

English:
lemma RingHom.HoldsForLocalizationAway.containsIdentities
  given: (hPl : HoldsForLocalizationAway P)
  proof: by
  introv R
  exact hPl.of_bijective _ _ Function.bijective_id

中文:
引理 环态射.HoldsForLocalizationAway.containsIdentities
  条件: (hPl : HoldsForLocalizationAway P)
  证明: by
  introv R
  exact hPl.of_bijective _ _ Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, bijective_id, hPl.of_bijective, introv, of_bijective
-/
lemma RingHom.HoldsForLocalizationAway.containsIdentities (hPl : HoldsForLocalizationAway P) :
    ContainsIdentities P := by
  introv R
  exact hPl.of_bijective _ _ Function.bijective_id

/--
lemma `RingHom.LocalizationAwayPreserves.respectsIso` / 引理 `RingHom.LocalizationAwayPreserves.respectsIso`

English:
lemma RingHom.LocalizationAwayPreserves.respectsIso
  proof: by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) R :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one (Equiv.refl _).bijective
    have : IsLocalization.Away (f 1) T :=
      IsLocalization.away_of_isUnit_of_bijective _ (by simp) e.bijective
    convert! hP f 

中文:
引理 环态射.LocalizationAwayPreserves.respectsIso
  证明: by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) R :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one (Equiv.refl _).bijective
    have : IsLocalization.Away (f 1) T :=
      IsLocalization.away_of_isUnit_of_bijective _ (by simp) e.bijective
    convert! hP f 

Depends on / 依赖: Equiv.refl, IsLocalization, IsLocalization.A, IsLocalization.Away, IsLocalization.Away.map, IsLocalization.away_of_isUnit_of_bijective, IsLocalization.map_comp, algebraMap, away_of_isUnit_of_bijective, bijective, convert, e.bijective, e.symm.toRingHom.toAlgebra, e.toRingHom.toAlgebra, isUnit_one, map_comp, toAlgebra, toRingHom
-/
lemma RingHom.LocalizationAwayPreserves.respectsIso
    (hP : LocalizationAwayPreserves P) :
    RespectsIso P where
  left {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) R :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one (Equiv.refl _).bijective
    have : IsLocalization.Away (f 1) T :=
      IsLocalization.away_of_isUnit_of_bijective _ (by simp) e.bijective
    convert! hP f 1 R T hf
    trans (IsLocalization.Away.map R T f 1).comp (algebraMap R R)
    · rw [IsLocalization.Away.map, IsLocalization.map_comp]; rfl
    · rfl
  right {R S T} _ _ _ f e hf := by
    let := e.symm.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) R :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.symm.bijective
    have : IsLocalization.Away (f 1) T :=
      IsLocalization.away_of_isUnit_of_bijective _ (by simp) (Equiv.refl _).bijective
    convert! hP f 1 R T hf
    have : RingHomInvPair (e : R ->+* S) e.symm := RingHomInvPair.of_ringEquiv _
    have : (IsLocalization.Away.map R T f 1).comp e.symm.toRingHom = f :=
      IsLocalization.map_comp ..
    conv_lhs => rw [← this, RingHom.comp_assoc]
    simp only [RingEquiv.toRingHom_eq_coe, RingHomCompTriple.comp_eq]

/--
lemma `RingHom.StableUnderCompositionWithLocalizationAway.respectsIso` / 引理 `RingHom.StableUnderCompositionWithLocalizationAway.respectsIso`

English:
lemma RingHom.StableUnderCompositionWithLocalizationAway.respectsIso
  proof: by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) T :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.right T (1 : S) f hf
  right {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) S :=


中文:
引理 环态射.StableUnderCompositionWithLocalizationAway.respectsIso
  证明: by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) T :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.right T (1 : S) f hf
  right {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) S :=


Depends on / 依赖: IsLocalization, IsLocalization.Away, IsLocalization.away_of_isUnit_of_bijective, away_of_isUnit_of_bijective, bijective, e.bijective, e.toRingHom.toAlgebra, hP.left, hP.right, isUnit_one, toAlgebra, toRingHom
-/
lemma RingHom.StableUnderCompositionWithLocalizationAway.respectsIso
    (hP : StableUnderCompositionWithLocalizationAway P) :
    RespectsIso P where
  left {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) T :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.right T (1 : S) f hf
  right {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) S :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.left S (1 : R) f hf

/--
theorem `RingHom.PropertyIsLocal.respectsIso` / 定理 `RingHom.PropertyIsLocal.respectsIso`

English:
theorem RingHom.PropertyIsLocal.respectsIso
  given: (hP : RingHom.PropertyIsLocal @P)
  proof: hP.localizationAwayPreserves.respectsIso

中文:
定理 环态射.PropertyIsLocal.respectsIso
  条件: (hP : 环态射.PropertyIsLocal @P)
  证明: hP.localizationAwayPreserves.respectsIso

Depends on / 依赖: hP.localizationAwayPreserves.respectsIso, localizationAwayPreserves, respectsIso
-/
theorem RingHom.PropertyIsLocal.respectsIso (hP : RingHom.PropertyIsLocal @P) :
    RingHom.RespectsIso @P :=
  hP.localizationAwayPreserves.respectsIso

-- Almost all arguments are implicit since this is not intended to use mid-proof.
/--
theorem `RingHom.LocalizationPreserves.away` / 定理 `RingHom.LocalizationPreserves.away`

English:
theorem RingHom.LocalizationPreserves.away
  given: (H : RingHom.LocalizationPreserves @P)
  proof: by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf

中文:
定理 环态射.LocalizationPreserves.away
  条件: (H : 环态射.LocalizationPreserves @P)
  证明: by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf

Depends on / 依赖: IsLocalization, Submonoid, Submonoid.map_powers, Submonoid.powers, map_powers, powers
-/
theorem RingHom.LocalizationPreserves.away (H : RingHom.LocalizationPreserves @P) :
    RingHom.LocalizationAwayPreserves P := by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf

/--
lemma `RingHom.PropertyIsLocal.HoldsForLocalizationAway` / 引理 `RingHom.PropertyIsLocal.HoldsForLocalizationAway`

English:
lemma RingHom.PropertyIsLocal.HoldsForLocalizationAway
  statement: (hP : RingHom.PropertyIsLocal @P)
  proof: by
  introv R _
  have : algebraMap R S = (algebraMap R S).comp (RingHom.id R) := by simp
  rw [this]
  apply hP.StableUnderCompositionWithLocalizationAwayTarget S r
  apply hPi

中文:
引理 环态射.PropertyIsLocal.HoldsForLocalizationAway
  结论: (hP : 环态射.PropertyIsLocal @P)
  证明: by
  introv R _
  have : algebraMap R S = (algebraMap R S).comp (RingHom.id R) := by simp
  rw [this]
  apply hP.StableUnderCompositionWithLocalizationAwayTarget S r
  apply hPi

Depends on / 依赖: RingHom, RingHom.id, StableUnderCompositionWithLocalizationAwayTarget, algebraMap, hP.StableUnderCompositionWithLocalizationAwayTarget, introv
-/
lemma RingHom.PropertyIsLocal.HoldsForLocalizationAway (hP : RingHom.PropertyIsLocal @P)
    (hPi : ContainsIdentities P) :
    RingHom.HoldsForLocalizationAway @P := by
  introv R _
  have : algebraMap R S = (algebraMap R S).comp (RingHom.id R) := by simp
  rw [this]
  apply hP.StableUnderCompositionWithLocalizationAwayTarget S r
  apply hPi

/--
theorem `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan` / 定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`

English:
theorem RingHom.OfLocalizationSpanTarget.ofLocalizationSpan
  proof: by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span]; rw [Ideal.map_top] at hs
  apply hP _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  rw [← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
    (T := Submonoid.powers (f r))]
  · apply hP' _ r
    exact hs' ⟨r, hr

中文:
定理 环态射.OfLocalizationSpanTarget.ofLocalizationSpan
  证明: by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span]; rw [Ideal.map_top] at hs
  apply hP _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  rw [← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
    (T := Submonoid.powers (f r))]
  · apply hP' _ r
    exact hs' ⟨r, hr

Depends on / 依赖: Ideal.map, Ideal.map_span, Ideal.map_top, IsLocalization, IsLocalization.map_comp, Localization, Localization.Away, Submonoid, Submonoid.powers, apply_fun, introv, map_comp, map_span, map_top, powers
-/
theorem RingHom.OfLocalizationSpanTarget.ofLocalizationSpan
    (hP : RingHom.OfLocalizationSpanTarget @P)
    (hP' : RingHom.StableUnderCompositionWithLocalizationAwaySource @P) :
    RingHom.OfLocalizationSpan @P := by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span]; rw [Ideal.map_top] at hs
  apply hP _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  rw [← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
    (T := Submonoid.powers (f r))]
  · apply hP' _ r
    exact hs' ⟨r, hr⟩

/--
lemma `RingHom.OfLocalizationSpan.ofIsLocalization` / 引理 `RingHom.OfLocalizationSpan.ofIsLocalization`

English:
lemma RingHom.OfLocalizationSpan.ofIsLocalization
  proof: by
  apply hP _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, fᵣ, hfᵣ, hf⟩ := hT r
  let e₁ := (Localization.algEquiv (.powers r.val) Rᵣ).toRingEquiv
  let e₂ := (IsLocalization.algEquiv (.powers (f r.val))
    (Localization (.powers (f r.val))) Sᵣ).symm.toRingEquiv
  have : Localization.awayMa

中文:
引理 环态射.OfLocalizationSpan.ofIsLocalization
  证明: by
  apply hP _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, fᵣ, hfᵣ, hf⟩ := hT r
  let e₁ := (Localization.algEquiv (.powers r.val) Rᵣ).toRingEquiv
  let e₂ := (IsLocalization.algEquiv (.powers (f r.val))
    (Localization (.powers (f r.val))) Sᵣ).symm.toRingEquiv
  have : Localization.awayMa

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, IsLocalization.ringHom_ext, Localization, Localization.algEquiv, Localization.awayMap, RingHom, RingHom.comp_apply, algEquiv, algebraMap, awayMap, comp_apply, powers, r.val, ringHom_ext, symm.toRingEquiv, toRingEquiv, toRingHom, toRingHom.comp
-/
lemma RingHom.OfLocalizationSpan.ofIsLocalization
    (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (s : Set R) (hs : Ideal.span s = ⊤)
    (hT : forall r : s, exists (Rᵣ Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ)
      (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ)
      (_ : IsLocalization.Away (f r.val) Sᵣ) (fᵣ : Rᵣ ->+* Sᵣ)
      (_ : fᵣ.comp (algebraMap R Rᵣ) = (algebraMap S Sᵣ).comp f),
        P fᵣ) : P f := by
  apply hP _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, fᵣ, hfᵣ, hf⟩ := hT r
  let e₁ := (Localization.algEquiv (.powers r.val) Rᵣ).toRingEquiv
  let e₂ := (IsLocalization.algEquiv (.powers (f r.val))
    (Localization (.powers (f r.val))) Sᵣ).symm.toRingEquiv
  have : Localization.awayMap f r.val =
      (e₂.toRingHom.comp fᵣ).comp e₁.toRingHom := by
    apply IsLocalization.ringHom_ext (.powers r.val)
    ext x
    have : fᵣ ((algebraMap R Rᵣ) x) = algebraMap S Sᵣ (f x) := by
      rw [← RingHom.comp_apply]; rw [hfᵣ]; rw [RingHom.comp_apply]
    simp [-AlgEquiv.symm_toRingEquiv, e₂, e₁, Localization.awayMap, IsLocalization.Away.map, this]
  rw [this]
  apply hPi.right
  apply hPi.left
  exact hf

/--
lemma `RingHom.OfLocalizationSpan.ofIsLocalization'` / 引理 `RingHom.OfLocalizationSpan.ofIsLocalization'`

English:
lemma RingHom.OfLocalizationSpan.ofIsLocalization'
  proof: by
  apply hP.ofIsLocalization hPi _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, hf⟩ := hT r
  exact ⟨Rᵣ, Sᵣ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsLocalization.Away.map Rᵣ Sᵣ f r, IsLocalization.map_comp _, hf⟩

中文:
引理 环态射.OfLocalizationSpan.ofIsLocalization'
  证明: by
  apply hP.ofIsLocalization hPi _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, hf⟩ := hT r
  exact ⟨Rᵣ, Sᵣ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsLocalization.Away.map Rᵣ Sᵣ f r, IsLocalization.map_comp _, hf⟩

Depends on / 依赖: IsLocalization, IsLocalization.Away.map, IsLocalization.map_comp, hP.ofIsLocalization, map_comp, ofIsLocalization
-/
lemma RingHom.OfLocalizationSpan.ofIsLocalization'
    (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (s : Set R) (hs : Ideal.span s = ⊤)
    (hT : forall r : s, exists (Rᵣ Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ)
      (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ)
      (_ : IsLocalization.Away (f r.val) Sᵣ),
        P (IsLocalization.Away.map Rᵣ Sᵣ f r)) : P f := by
  apply hP.ofIsLocalization hPi _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, hf⟩ := hT r
  exact ⟨Rᵣ, Sᵣ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsLocalization.Away.map Rᵣ Sᵣ f r, IsLocalization.map_comp _, hf⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `RingHom.OfLocalizationSpanTarget.ofIsLocalization` / 引理 `RingHom.OfLocalizationSpanTarget.ofIsLocalization`

English:
lemma RingHom.OfLocalizationSpanTarget.ofIsLocalization
  proof: by
  apply hP _ s hs
  intro r
  obtain ⟨T, _, _, _, hT⟩ := hT r
  convert! hP'.1 _ (Localization.algEquiv (R := S) (Submonoid.powers (r : S)) T).symm.toRingEquiv hT
  rw [← RingHom.comp_assoc]; rw [RingEquiv.toRingHom_eq_coe]; rw [AlgEquiv.toRingEquiv_toRingHom]; rw [Localization.coe_algEquiv_symm]

中文:
引理 环态射.OfLocalizationSpanTarget.ofIsLocalization
  证明: by
  apply hP _ s hs
  intro r
  obtain ⟨T, _, _, _, hT⟩ := hT r
  convert! hP'.1 _ (Localization.algEquiv (R := S) (Submonoid.powers (r : S)) T).symm.toRingEquiv hT
  rw [← RingHom.comp_assoc]; rw [RingEquiv.toRingHom_eq_coe]; rw [AlgEquiv.toRingEquiv_toRingHom]; rw [Localization.coe_algEquiv_symm]

Depends on / 依赖: AlgEquiv, AlgEquiv.toRingEquiv_toRingHom, IsLocalization, IsLocalization.map_comp, Localization, Localization.algEquiv, Localization.coe_algEquiv_symm, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.comp_assoc, RingHom.comp_id, Submonoid, Submonoid.powers, algEquiv, coe_algEquiv_symm, comp_assoc, comp_id, convert, map_comp
-/
lemma RingHom.OfLocalizationSpanTarget.ofIsLocalization
    (hP : RingHom.OfLocalizationSpanTarget P) (hP' : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (s : Set S) (hs : Ideal.span s = ⊤)
    (hT : forall r : s, exists (T : Type u) (_ : CommRing T) (_ : Algebra S T)
      (_ : IsLocalization.Away (r : S) T), P ((algebraMap S T).comp f)) : P f := by
  apply hP _ s hs
  intro r
  obtain ⟨T, _, _, _, hT⟩ := hT r
  convert! hP'.1 _ (Localization.algEquiv (R := S) (Submonoid.powers (r : S)) T).symm.toRingEquiv hT
  rw [← RingHom.comp_assoc]; rw [RingEquiv.toRingHom_eq_coe]; rw [AlgEquiv.toRingEquiv_toRingHom]; rw [Localization.coe_algEquiv_symm]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]

section

variable {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}

/--
lemma `RingHom.OfLocalizationSpanTarget.and` / 引理 `RingHom.OfLocalizationSpanTarget.and`

English:
lemma RingHom.OfLocalizationSpanTarget.and
  statement: (hP : OfLocalizationSpanTarget P)
  proof: by
  introv R hs hf
  exact ⟨hP f s hs fun r => (hf r).1, hQ f s hs fun r => (hf r).2⟩

中文:
引理 环态射.OfLocalizationSpanTarget.and
  结论: (hP : OfLocalizationSpanTarget P)
  证明: by
  introv R hs hf
  exact ⟨hP f s hs fun r => (hf r).1, hQ f s hs fun r => (hf r).2⟩

Depends on / 依赖: introv
-/
lemma RingHom.OfLocalizationSpanTarget.and (hP : OfLocalizationSpanTarget P)
    (hQ : OfLocalizationSpanTarget Q) :
    OfLocalizationSpanTarget (fun f => P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r => (hf r).1, hQ f s hs fun r => (hf r).2⟩

/--
lemma `RingHom.OfLocalizationSpan.and` / 引理 `RingHom.OfLocalizationSpan.and`

English:
lemma RingHom.OfLocalizationSpan.and
  given: (hP : OfLocalizationSpan P) (hQ : OfLocalizationSpan Q)
  proof: by
  introv R hs hf
  exact ⟨hP f s hs fun r => (hf r).1, hQ f s hs fun r => (hf r).2⟩

中文:
引理 环态射.OfLocalizationSpan.and
  条件: (hP : OfLocalizationSpan P) (hQ : OfLocalizationSpan Q)
  证明: by
  introv R hs hf
  exact ⟨hP f s hs fun r => (hf r).1, hQ f s hs fun r => (hf r).2⟩

Depends on / 依赖: introv
-/
lemma RingHom.OfLocalizationSpan.and (hP : OfLocalizationSpan P) (hQ : OfLocalizationSpan Q) :
    OfLocalizationSpan (fun f => P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r => (hf r).1, hQ f s hs fun r => (hf r).2⟩

/--
lemma `RingHom.LocalizationAwayPreserves.and` / 引理 `RingHom.LocalizationAwayPreserves.and`

English:
lemma RingHom.LocalizationAwayPreserves.and
  statement: (hP : LocalizationAwayPreserves P)
  proof: by
  introv R h
  exact ⟨hP f r R' S' h.1, hQ f r R' S' h.2⟩

中文:
引理 环态射.LocalizationAwayPreserves.and
  结论: (hP : LocalizationAwayPreserves P)
  证明: by
  introv R h
  exact ⟨hP f r R' S' h.1, hQ f r R' S' h.2⟩

Depends on / 依赖: introv
-/
lemma RingHom.LocalizationAwayPreserves.and (hP : LocalizationAwayPreserves P)
    (hQ : LocalizationAwayPreserves Q) :
    LocalizationAwayPreserves (fun f => P f ∧ Q f) := by
  introv R h
  exact ⟨hP f r R' S' h.1, hQ f r R' S' h.2⟩

/--
lemma `RingHom.StableUnderCompositionWithLocalizationAwayTarget.and` / 引理 `RingHom.StableUnderCompositionWithLocalizationAwayTarget.and`

English:
lemma RingHom.StableUnderCompositionWithLocalizationAwayTarget.and
  proof: by
  introv R h hf
  exact ⟨hP T s f hf.1, hQ T s f hf.2⟩

中文:
引理 环态射.StableUnderCompositionWithLocalizationAwayTarget.and
  证明: by
  introv R h hf
  exact ⟨hP T s f hf.1, hQ T s f hf.2⟩

Depends on / 依赖: introv
-/
lemma RingHom.StableUnderCompositionWithLocalizationAwayTarget.and
    (hP : StableUnderCompositionWithLocalizationAwayTarget P)
    (hQ : StableUnderCompositionWithLocalizationAwayTarget Q) :
    StableUnderCompositionWithLocalizationAwayTarget (fun f => P f ∧ Q f) := by
  introv R h hf
  exact ⟨hP T s f hf.1, hQ T s f hf.2⟩

/--
lemma `RingHom.PropertyIsLocal.and` / 引理 `RingHom.PropertyIsLocal.and`

English:
lemma RingHom.PropertyIsLocal.and
  given: (hP : PropertyIsLocal P) (hQ : PropertyIsLocal Q)
  proof: hP.localizationAwayPreserves.and hQ.localizationAwayPreserves
  ofLocalizationSpanTarget := hP.ofLocalizationSpanTarget.and hQ.ofLocalizationSpanTarget
  ofLocalizationSpan := hP.ofLocalizationSpan.and hQ.ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    hP.StableUnderComp

中文:
引理 环态射.PropertyIsLocal.and
  条件: (hP : PropertyIsLocal P) (hQ : PropertyIsLocal Q)
  证明: hP.localizationAwayPreserves.and hQ.localizationAwayPreserves
  ofLocalizationSpanTarget := hP.ofLocalizationSpanTarget.and hQ.ofLocalizationSpanTarget
  ofLocalizationSpan := hP.ofLocalizationSpan.and hQ.ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    hP.StableUnderComp

Depends on / 依赖: hP.localizationAwayPreserves.and, hQ.localizationAwayPreserves, localizationAwayPreserves
-/
lemma RingHom.PropertyIsLocal.and (hP : PropertyIsLocal P) (hQ : PropertyIsLocal Q) :
    PropertyIsLocal (fun f => P f ∧ Q f) where
  localizationAwayPreserves := hP.localizationAwayPreserves.and hQ.localizationAwayPreserves
  ofLocalizationSpanTarget := hP.ofLocalizationSpanTarget.and hQ.ofLocalizationSpanTarget
  ofLocalizationSpan := hP.ofLocalizationSpan.and hQ.ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    hP.StableUnderCompositionWithLocalizationAwayTarget.and
    hQ.StableUnderCompositionWithLocalizationAwayTarget

end

section

variable (hP : RingHom.IsStableUnderBaseChange @P)
variable {R S Rᵣ Sᵣ : Type u} [CommRing R] [CommRing S] [CommRing Rᵣ] [CommRing Sᵣ] [Algebra R Rᵣ]
  [Algebra S Sᵣ]

include hP

/--
lemma `RingHom.IsStableUnderBaseChange.of_isLocalization` / 引理 `RingHom.IsStableUnderBaseChange.of_isLocalization`

English:
lemma RingHom.IsStableUnderBaseChange.of_isLocalization
  statement: [Algebra R S] [Algebra R Sᵣ] [Algebra Rᵣ Sᵣ]
  proof: letI : Algebra.IsPushout R S Rᵣ Sᵣ := Algebra.isPushout_of_isLocalization M Rᵣ S Sᵣ
  hP R S Rᵣ Sᵣ h

中文:
引理 环态射.是StableUnderBaseChange.of_isLocalization
  结论: [代数 R S] [代数 R Sᵣ] [代数 Rᵣ Sᵣ]
  证明: letI : Algebra.IsPushout R S Rᵣ Sᵣ := Algebra.isPushout_of_isLocalization M Rᵣ S Sᵣ
  hP R S Rᵣ Sᵣ h

Depends on / 依赖: Algebra, Algebra.IsPushout, Algebra.isPushout_of_isLocalization, IsPushout, isPushout_of_isLocalization
-/
lemma RingHom.IsStableUnderBaseChange.of_isLocalization [Algebra R S] [Algebra R Sᵣ] [Algebra Rᵣ Sᵣ]
    [IsScalarTower R S Sᵣ] [IsScalarTower R Rᵣ Sᵣ]
    (M : Submonoid R) [IsLocalization M Rᵣ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ]
    (h : P (algebraMap R S)) : P (algebraMap Rᵣ Sᵣ) :=
  letI : Algebra.IsPushout R S Rᵣ Sᵣ := Algebra.isPushout_of_isLocalization M Rᵣ S Sᵣ
  hP R S Rᵣ Sᵣ h

/--
lemma `RingHom.IsStableUnderBaseChange.isLocalization_map` / 引理 `RingHom.IsStableUnderBaseChange.isLocalization_map`

English:
lemma RingHom.IsStableUnderBaseChange.isLocalization_map
  statement: (M : Submonoid R) [IsLocalization M Rᵣ]
  proof: by
  algebraize [f, IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map,
    (IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map).comp (algebraMap R Rᵣ)]
  have : IsScalarTower R S Sᵣ := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map)
  have : IsLocalization (Algebra.algebraM

中文:
引理 环态射.是StableUnderBaseChange.isLocalization_map
  结论: (M : 子幺半群 R) [是Localization M Rᵣ]
  证明: by
  algebraize [f, IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map,
    (IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map).comp (algebraMap R Rᵣ)]
  have : IsScalarTower R S Sᵣ := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map)
  have : IsLocalization (Algebra.algebraM

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, IsLocalization, IsLocalization.map, IsLocalization.map_comp, IsScalarTower, IsScalarTower.of_algebraMap_eq, M.le_comap_map, M.map, algebraMap, algebraMapSubmonoid, algebraize, hP.of_isLocalization, le_comap_map, map_comp, of_algebraMap_eq, of_isLocalization
-/
lemma RingHom.IsStableUnderBaseChange.isLocalization_map (M : Submonoid R) [IsLocalization M Rᵣ]
    (f : R ->+* S) [IsLocalization (M.map f) Sᵣ] (hf : P f) :
    P (IsLocalization.map Sᵣ f M.le_comap_map : Rᵣ ->+* Sᵣ) := by
  algebraize [f, IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map,
    (IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map).comp (algebraMap R Rᵣ)]
  have : IsScalarTower R S Sᵣ := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map)
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ :=
inferInstanceAs IsLocalization (M.map f) Sᵣ
  apply hP.of_isLocalization M hf

/--
lemma `RingHom.IsStableUnderBaseChange.localizationPreserves` / 引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`

English:
lemma RingHom.IsStableUnderBaseChange.localizationPreserves
  statement: LocalizationPreserves P
  proof: by
  introv R hf
  exact hP.isLocalization_map _ _ hf

中文:
引理 环态射.是StableUnderBaseChange.localizationPreserves
  结论: LocalizationPreserves P
  证明: by
  introv R hf
  exact hP.isLocalization_map _ _ hf

Depends on / 依赖: hP.isLocalization_map, introv, isLocalization_map
-/
lemma RingHom.IsStableUnderBaseChange.localizationPreserves : LocalizationPreserves P := by
  introv R hf
  exact hP.isLocalization_map _ _ hf

end

end RingHom

end Properties

section Ideal

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]

/--
theorem `Ideal.localized'_eq_map` / 定理 `Ideal.localized'_eq_map`

English:
theorem Ideal.localized'_eq_map
  given: (I : Ideal R)
  proof: by
  rw [map]; rw [span]; rw [Submodule.localized'_eq_span]; rw [Algebra.coe_linearMap]

中文:
定理 理想.localized'_eq_map
  条件: (I : 理想 R)
  证明: by
  rw [map]; rw [span]; rw [Submodule.localized'_eq_span]; rw [Algebra.coe_linearMap]

Depends on / 依赖: Algebra, Algebra.coe_linearMap, Submodule, Submodule.localized, _eq_span, coe_linearMap, localized
-/
theorem Ideal.localized'_eq_map (I : Ideal R) :
    Submodule.localized' S p (Algebra.linearMap R S) I = I.map (algebraMap R S) := by
  rw [map]; rw [span]; rw [Submodule.localized'_eq_span]; rw [Algebra.coe_linearMap]

/--
theorem `Ideal.localized₀_eq_restrictScalars_map` / 定理 `Ideal.localized₀_eq_restrictScalars_map`

English:
theorem Ideal.localized₀_eq_restrictScalars_map
  given: (I : Ideal R)
  proof: congr(Submodule.restrictScalars R $(localized'_eq_map S p I))

中文:
定理 理想.localized₀_eq_restrictScalars_map
  条件: (I : 理想 R)
  证明: congr(Submodule.restrictScalars R $(localized'_eq_map S p I))

Depends on / 依赖: Submodule, Submodule.restrictScalars, _eq_map, localized, restrictScalars
-/
theorem Ideal.localized₀_eq_restrictScalars_map (I : Ideal R) :
    Submodule.localized₀ p (Algebra.linearMap R S) I = (I.map (algebraMap R S)).restrictScalars R :=
  congr(Submodule.restrictScalars R $(localized'_eq_map S p I))

/--
theorem `Algebra.idealMap_eq_ofEq_comp_toLocalized₀` / 定理 `Algebra.idealMap_eq_ofEq_comp_toLocalized₀`

English:
theorem Algebra.idealMap_eq_ofEq_comp_toLocalized₀
  given: (I : Ideal R)
  proof: rfl

中文:
定理 代数.idealMap_eq_ofEq_comp_toLocalized₀
  条件: (I : 理想 R)
  证明: rfl
-/
theorem Algebra.idealMap_eq_ofEq_comp_toLocalized₀ (I : Ideal R) :
    Algebra.idealMap S I =
      (LinearEquiv.ofEq _ _ <| Ideal.localized₀_eq_restrictScalars_map S p I).toLinearMap ∘ₗ
      Submodule.toLocalized₀ p (Algebra.linearMap R S) I :=
  rfl

/--
theorem `Ideal.mem_of_localization_maximal` / 定理 `Ideal.mem_of_localization_maximal`

English:
theorem Ideal.mem_of_localization_maximal
  statement: {r : R} {J : Ideal R}
  proof: Submodule.mem_of_localization_maximal _ _ _ _ fun P hP => by
    apply (localized'_eq_map (Localization.AtPrime P) P.primeCompl J).symm ▸ h P hP

中文:
定理 理想.mem_of_localization_maximal
  结论: {r : R} {J : 理想 R}
  证明: Submodule.mem_of_localization_maximal _ _ _ _ fun P hP => by
    apply (localized'_eq_map (Localization.AtPrime P) P.primeCompl J).symm ▸ h P hP

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, P.primeCompl, Submodule, Submodule.mem_of_localization_maximal, _eq_map, localized, mem_of_localization_maximal, primeCompl
-/
theorem Ideal.mem_of_localization_maximal {r : R} {J : Ideal R}
    (h : forall (P : Ideal R) (_ : P.IsMaximal),
      algebraMap R _ r in Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    r in J :=
  Submodule.mem_of_localization_maximal _ _ _ _ fun P hP => by
    apply (localized'_eq_map (Localization.AtPrime P) P.primeCompl J).symm ▸ h P hP

/--
theorem `Ideal.le_of_localization_maximal` / 定理 `Ideal.le_of_localization_maximal`

English:
theorem Ideal.le_of_localization_maximal
  statement: {I J : Ideal R}
  proof: fun _ hm => mem_of_localization_maximal fun P hP => h P hP (mem_map_of_mem _ hm)

中文:
定理 理想.le_of_localization_maximal
  结论: {I J : 理想 R}
  证明: fun _ hm => mem_of_localization_maximal fun P hP => h P hP (mem_map_of_mem _ hm)

Depends on / 依赖: mem_map_of_mem, mem_of_localization_maximal
-/
theorem Ideal.le_of_localization_maximal {I J : Ideal R}
    (h : forall (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I <=
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I <= J :=
  fun _ hm => mem_of_localization_maximal fun P hP => h P hP (mem_map_of_mem _ hm)

/--
lemma `Ideal.iInf_ker_le` / 引理 `Ideal.iInf_ker_le`

English:
lemma Ideal.iInf_ker_le
  given: (I : Ideal R)
  proof: by
  intro x hx
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  simp only [Submodule.mem_iInf, RingHom.mem_ker] at hx
  by_cases hle : I <= m
  · simp [hx _ _ hle]
  · simp [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]

中文:
引理 理想.iInf_ker_le
  条件: (I : 理想 R)
  证明: by
  intro x hx
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  simp only [Submodule.mem_iInf, RingHom.mem_ker] at hx
  by_cases hle : I <= m
  · simp [hx _ _ hle]
  · simp [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]

Depends on / 依赖: AtPrime, Ideal.mem_of_localization_maximal, IsLocalization, IsLocalization.AtPrime.map_eq_top_of_not_le, RingHom, RingHom.mem_ker, Submodule, Submodule.mem_iInf, map_eq_top_of_not_le, mem_iInf, mem_ker, mem_of_localization_maximal
-/
lemma Ideal.iInf_ker_le (I : Ideal R) :
    ⨅ (p : Ideal R) (_ : p.IsPrime) (_ : I <= p),
      RingHom.ker (algebraMap R (Localization.AtPrime p)) <= I := by
  intro x hx
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  simp only [Submodule.mem_iInf, RingHom.mem_ker] at hx
  by_cases hle : I <= m
  · simp [hx _ _ hle]
  · simp [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]

/--
theorem `Ideal.eq_of_localization_maximal` / 定理 `Ideal.eq_of_localization_maximal`

English:
theorem Ideal.eq_of_localization_maximal
  statement: {I J : Ideal R}
  proof: le_antisymm (le_of_localization_maximal fun P hP => (h P hP).le)
    (le_of_localization_maximal fun P hP => (h P hP).ge)

中文:
定理 理想.eq_of_localization_maximal
  结论: {I J : 理想 R}
  证明: le_antisymm (le_of_localization_maximal fun P hP => (h P hP).le)
    (le_of_localization_maximal fun P hP => (h P hP).ge)

Depends on / 依赖: le_antisymm, le_of_localization_maximal
-/
theorem Ideal.eq_of_localization_maximal {I J : Ideal R}
    (h : forall (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I = J :=
  le_antisymm (le_of_localization_maximal fun P hP => (h P hP).le)
    (le_of_localization_maximal fun P hP => (h P hP).ge)

/--
theorem `ideal_eq_bot_of_localization'` / 定理 `ideal_eq_bot_of_localization'`

English:
theorem ideal_eq_bot_of_localization'
  statement: (I : Ideal R)
  proof: Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP

中文:
定理 ideal_eq_bot_of_localization'
  结论: (I : 理想 R)
  证明: Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP

Depends on / 依赖: Ideal.eq_of_localization_maximal, eq_of_localization_maximal
-/
theorem ideal_eq_bot_of_localization' (I : Ideal R)
    (h : forall (J : Ideal R) (_ : J.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime J)) I = ⊥) :
    I = ⊥ :=
  Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP

/--
theorem `eq_zero_of_localization` / 定理 `eq_zero_of_localization`

English:
theorem eq_zero_of_localization
  statement: (r : R)
  proof: Module.eq_zero_of_localization_maximal _ (fun _ _ => Algebra.linearMap R _) r h

中文:
定理 eq_zero_of_localization
  结论: (r : R)
  证明: Module.eq_zero_of_localization_maximal _ (fun _ _ => Algebra.linearMap R _) r h

Depends on / 依赖: Algebra, Algebra.linearMap, Module, Module.eq_zero_of_localization_maximal, eq_zero_of_localization_maximal, linearMap
-/
theorem eq_zero_of_localization (r : R)
    (h : forall (J : Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) :
    r = 0 :=
  Module.eq_zero_of_localization_maximal _ (fun _ _ => Algebra.linearMap R _) r h

/--
theorem `ideal_eq_bot_of_localization` / 定理 `ideal_eq_bot_of_localization`

English:
theorem ideal_eq_bot_of_localization
  statement: (I : Ideal R)
  proof: bot_unique fun r hr => eq_zero_of_localization r fun J hJ => (h J hJ).le ⟨r, hr, rfl⟩

中文:
定理 ideal_eq_bot_of_localization
  结论: (I : 理想 R)
  证明: bot_unique fun r hr => eq_zero_of_localization r fun J hJ => (h J hJ).le ⟨r, hr, rfl⟩

Depends on / 依赖: bot_unique, eq_zero_of_localization
-/
theorem ideal_eq_bot_of_localization (I : Ideal R)
    (h : forall (J : Ideal R) (_ : J.IsMaximal),
      IsLocalization.coeSubmodule (Localization.AtPrime J) I = ⊥) :
    I = ⊥ :=
  bot_unique fun r hr => eq_zero_of_localization r fun J hJ => (h J hJ).le ⟨r, hr, rfl⟩

end Ideal
