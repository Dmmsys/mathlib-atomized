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

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable (R' S' : Type u) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

section CommRing

variable (P : ∀ (R : Type u) [CommRing R], Prop)

/-- A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`. -/
/-
**LocalizationPreserves** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocalizationPreserves : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`.
-/
def LocalizationPreserves : Prop :=
  ∀ {R : Type u} [hR : CommRing R] (M : Submonoid R) (S : Type u) [hS : CommRing S] [Algebra R S]
    [IsLocalization M S], @P R hR → @P S hS

/-- A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`. -/
/-
**OfLocalizationMaximal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OfLocalizationMaximal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`.
-/
def OfLocalizationMaximal : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J)) → P R

end CommRing

section RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

/-- A property `P` of ring homs is said to contain identities if `P` holds
for the identity homomorphism of every ring. -/
/-
**RingHom.ContainsIdentities** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.ContainsIdentities
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs is said to contain identities if `P` holds
for the identity homomorphism of every ring.
-/
def RingHom.ContainsIdentities := ∀ (R : Type u) [CommRing R], P (RingHom.id R)

/-- A property `P` of ring homs is said to be preserved by localization
if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`. -/
/-
**RingHom.LocalizationPreserves** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.LocalizationPreserves
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs is said to be preserved by localization
if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`.
-/
def RingHom.LocalizationPreserves :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (M : Submonoid R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization M R']
    [IsLocalization (M.map f) S'],
    P f → P (IsLocalization.map S' f (Submonoid.le_comap_map M) : R' →+* S')

/-- A property `P` of ring homs is said to be preserved by localization away
if `P` holds for `Rᵣ →+* Sᵣ` whenever `P` holds for `R →+* S`. -/
/-
**RingHom.LocalizationAwayPreserves** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.LocalizationAwayPreserves
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs is said to be preserved by localization away
if `P` holds for `Rᵣ →+* Sᵣ` whenever `P` holds for `R →+* S`.
-/
def RingHom.LocalizationAwayPreserves :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (r : R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'],
    P f → P (IsLocalization.Away.map R' S' f r : R' →+* S')

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this is easier to prove. -/
/-
**RingHom.OfLocalizationFiniteSpan** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationFiniteSpan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans
 `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this is easier to prove.
-/
def RingHom.OfLocalizationFiniteSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : ∀ r : s, P (Localization.awayMap f r)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this has less restrictions when applying. -/
/-
**RingHom.OfLocalizationSpan** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `R` su
ch that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this has less restrictions when app
lying.
-/
def RingHom.OfLocalizationSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P (Localization.awayMap f r)), P f

/-- A property `P` of ring homs satisfies `RingHom.HoldsForLocalization`
if `P` holds for each localization map `R →+* M⁻¹R`. -/
/-
**RingHom.HoldsForLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.HoldsForLocalization : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.HoldsForLocalization`
if `P` holds for each localization map `R →+* M⁻¹R`.
-/
def RingHom.HoldsForLocalization : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S], P (algebraMap R S)

/-- A property `P` of ring homs satisfies `RingHom.HoldsForLocalizationAway`
if `P` holds for each localization map `R →+* Rᵣ`. -/
/-
**RingHom.HoldsForLocalizationAway** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.HoldsForLocalizationAway : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.HoldsForLocalizationAway`
if `P` holds for each localization map `R →+* Rᵣ`.
-/
def RingHom.HoldsForLocalizationAway : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAwaySource`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the source. -/
/-
**RingHom.StableUnderCompositionWithLocalizationAwaySource** 是 Mathlib 中的一个定义，位于
命名空间 ``。
形式化陈述：RingHom.StableUnderCompositionWithLocalizationAwaySource : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocaliz
ationAwaySource`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the source.
-/
def RingHom.StableUnderCompositionWithLocalizationAwaySource : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) ⦃T : Type u⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (f : S →+* T), P f → P (f.comp (algebraMap R S))

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the target. -/
/-
**RingHom.StableUnderCompositionWithLocalizationAwayTarget** 是 Mathlib 中的一个定义，位于
命名空间 ``。
形式化陈述：RingHom.StableUnderCompositionWithLocalizationAwayTarget : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocaliz
ationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the target.
-/
def RingHom.StableUnderCompositionWithLocalizationAwayTarget : Prop :=
  ∀ ⦃R S : Type u⦄ (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra S T] (s : S)
    [IsLocalization.Away s T] (f : R →+* S), P f → P ((algebraMap S T).comp f)

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the left and on the right. -/
/-
**RingHom.StableUnderCompositionWithLocalizationAway** 是 Mathlib 中的一个定义，位于命名空间 `
`。
形式化陈述：RingHom.StableUnderCompositionWithLocalizationAway : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocaliz
ationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the left and on the right.
-/
def RingHom.StableUnderCompositionWithLocalizationAway : Prop :=
  StableUnderCompositionWithLocalizationAwaySource P ∧
    StableUnderCompositionWithLocalizationAwayTarget P

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpanTarget`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this is easier to prove. -/
/-
**RingHom.OfLocalizationFiniteSpanTarget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationFiniteSpanTarget : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpanTarget`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans
 `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this is easier to prove.
-/
def RingHom.OfLocalizationFiniteSpanTarget : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset S)
    (_ : Ideal.span (s : Set S) = ⊤)
    (_ : ∀ r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationSpanTarget`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this has less restrictions when applying. -/
/-
**RingHom.OfLocalizationSpanTarget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpanTarget : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.OfLocalizationSpanTarget`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `S` su
ch that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this has less restrictions wh
en applying.
-/
def RingHom.OfLocalizationSpanTarget : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set S) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationPrime`
if `P` holds for `R` whenever `P` holds for `Rₘ` for all prime ideals `p`. -/
/-
**RingHom.OfLocalizationPrime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationPrime : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homs satisfies `RingHom.OfLocalizationPrime`
if `P` holds for `R` whenever `P` holds for `Rₘ` for all prime ideals `p`.
-/
def RingHom.OfLocalizationPrime : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S),
    (∀ (J : Ideal S) (_ : J.IsPrime), P (Localization.localRingHom _ J f rfl)) → P f

/-- A property of ring homs is local if it is preserved by localizations and compositions, and for
each `{ r }` that spans `S`, we have `P (R →+* S) ↔ ∀ r, P (R →+* Sᵣ)`. -/
/-
**RingHom.PropertyIsLocal** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingHom`。
形式化陈述：({R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) 
→ Prop) → Prop
参数：R →+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of ring homs is local if it is preserved by localizations and composi
tions, and for
each `{ r }` that spans `S`, we have `P (R →+* S) ↔ ∀ r, P (R →+* Sᵣ)`.
-/
structure RingHom.PropertyIsLocal : Prop where
  localizationAwayPreserves : RingHom.LocalizationAwayPreserves @P
  ofLocalizationSpanTarget : RingHom.OfLocalizationSpanTarget @P
  ofLocalizationSpan : RingHom.OfLocalizationSpan @P
  StableUnderCompositionWithLocalizationAwayTarget :
    RingHom.StableUnderCompositionWithLocalizationAwayTarget @P
/-
**RingHom.ofLocalizationSpan_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.ofLocalizationSpan_iff_finite : RingHom.OfLocalizationSpan @P ↔ Ri
ngHom.OfLocalizationFiniteSpan @P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₅_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {ε : (a : α) → (b : β a
) →…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
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
/-
**RingHom.ofLocalizationSpanTarget_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.ofLocalizationSpanTarget_iff_finite : RingHom.OfLocalizationSpanTa
rget @P ↔ RingHom.OfLocalizationFiniteSpanTarget @P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₅_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {ε : (a : α) → (b : β a
) →…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
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
/-
**RingHom.OfLocalizationSpan.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpan.mk (hP : RingHom.RespectsIso P) (H : forall {R 
S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : Set R), Ideal.span s = 
⊤ -> (forall r in s, P (algebraMap (Localization.Away r) (Localization.Away r ot
imes[R] S))) -> P (algebraMap R S)) : OfLocalizationSpan P
参数：hP : RingHom.RespectsIso P；H : forall {R S : Type u} [CommRing R] [CommRing S
] [Algebra R S] (s : Set R), Ideal.span s = ⊤ -> (forall r in s, P (algebraMap (
Localization.Away r) (Localization.Away r otimes[R] S))) -> P (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用引理 `Algebra.TensorProduct.tmul_one_eq_one_tmul`：tmul_one_eq_one_tmul (r : R)
 : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma RingHom.OfLocalizationSpan.mk (hP : RingHom.RespectsIso P)
    (H : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : Set R),
      Ideal.span s = ⊤ →
      (∀ r ∈ s, P (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S))) →
      P (algebraMap R S)) :
    OfLocalizationSpan P := by
  introv R hs hf
  algebraize [f]
  let _ := fun r : R => (Localization.awayMap (algebraMap R S) r).toAlgebra
  refine H s hs (fun r hr ↦ ?_)
  have : algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S) =
      ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).symm : _ →+* _).comp
        (algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext
    simp [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
  rw [this]
  exact hP.1 _ _ (hf ⟨r, hr⟩)

section HoldsForLocalization

variable {P}

/-
**RingHom.HoldsForLocalization.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HoldsForLocalization.mk (hP : RespectsIso P) (H : forall {R : Type
 u} [CommRing R] (M : Submonoid R), P (algebraMap R (Localization M))) : HoldsFo
rLocalization P
参数：hP : RespectsIso P；H : forall {R : Type u} [CommRing R] (M : Submonoid R), P 
(algebraMap R (Localization M))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma RingHom.HoldsForLocalization.mk (hP : RespectsIso P)
    (H : ∀ {R : Type u} [CommRing R] (M : Submonoid R), P (algebraMap R (Localization M))) :
    HoldsForLocalization P := by
  introv R _
  rw [← (IsLocalization.algEquiv M (Localization M) S).toAlgHom.comp_algebraMap]
  exact hP.1 _ _ (H _)
/-
**RingHom.HoldsForLocalization.holdsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：RingHom.HoldsForLocalization.holdsForLocalizationAway (hP : HoldsForLocali
zation P) : HoldsForLocalizationAway P
参数：hP : HoldsForLocalization P。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingHom.HoldsForLocalization.holdsForLocalizationAway (hP : HoldsForLocalization P) :
    HoldsForLocalizationAway P :=
  fun _ _ _ _ _ r _ ↦ hP _ (Submonoid.powers r)
/-
**RingHom.HoldsForLocalization.isLocalizationMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HoldsForLocalization.isLocalizationMap (hPc : StableUnderCompositi
on P) (hPp : LocalizationPreserves P) (hPl : HoldsForLocalization P) {M : Submon
oid R} {T : Submonoid S} {R' : Type u} [CommRing R'] [Algebra R R'] [IsLocalizat
ion M R'] (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization T S'] {f : 
R ->+* S} (hy : M <= Submonoid.comap f T) (hf : P f) : P (IsLocalization.map (S
参数：hPc : StableUnderComposition P；hPp : LocalizationPreserves P；hPl : HoldsForLo
calization P；S' : Type u；hy : M <= Submonoid.comap f T；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.localization_isScalarTower_of_submonoid_le`：localization_
isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M <= N) [IsLocalization M
 S] [IsLocalization N T] : @IsScalarTower R S T…
· 使用定理 `IsLocalization.isLocalization_of_submonoid_le`：isLocalization_of_submono
id_le (M N : Submonoid R) (h : M <= N) [IsLocalization M S] [IsLocalization N T]
 [Algebra S T] [IsScalarTower R S T…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RingHom.HoldsForLocalization.isLocalizationMap
    (hPc : StableUnderComposition P) (hPp : LocalizationPreserves P)
    (hPl : HoldsForLocalization P)
    {M : Submonoid R} {T : Submonoid S}
    {R' : Type u} [CommRing R'] [Algebra R R'] [IsLocalization M R']
    (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization T S']
    {f : R →+* S} (hy : M ≤ Submonoid.comap f T) (hf : P f) :
    P (IsLocalization.map (S := R') S' f hy) := by
  have hle : Submonoid.map f M ≤ T := by simpa [Submonoid.map_le_iff_le_comap]
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
/-
**RingHom.HoldsForLocalization.localRingHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HoldsForLocalization.localRingHom (hPc : StableUnderComposition P)
 (hPp : LocalizationPreserves P) (hPl : HoldsForLocalization P) {R S : Type u} [
CommRing R] [CommRing S] {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] {f 
: R ->+* S} (h : p = q.comap f) (hf : P f) : P (Localization.localRingHom p q f 
h)
参数：hPc : StableUnderComposition P；hPp : LocalizationPreserves P；hPl : HoldsForLo
calization P；h : p = q.comap f；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.HoldsForLocalization.isLocalizationMap`：RingHom.HoldsForLocaliza
tion.isLocalizationMap (hPc : StableUnderComposition P) (hPp : LocalizationPrese
rves P) (hPl : HoldsForLocalization …
-/
lemma RingHom.HoldsForLocalization.localRingHom (hPc : StableUnderComposition P)
    (hPp : LocalizationPreserves P) (hPl : HoldsForLocalization P)
    {R S : Type u} [CommRing R] [CommRing S] {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime]
    {f : R →+* S} (h : p = q.comap f) (hf : P f) :
    P (Localization.localRingHom p q f h) :=
  hPl.isLocalizationMap hPc hPp _ _ hf

end HoldsForLocalization

/-
**RingHom.HoldsForLocalizationAway.of_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.HoldsForLocalizationAway.of_bijective (H : RingHom.HoldsForLocaliz
ationAway P) (hf : Function.Bijective f) : P f
参数：H : RingHom.HoldsForLocalizationAway P；hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.of_le_isUnit`：of_le_isUnit {S : Submonoid R} (hS : S <= I
sUnit.submonoid R) : IsLocalization S R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.powers_one`：powers_one : powers (1 : M) = ⊥
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
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
/-
**RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway** 是 
Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway 
(hPc : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizationAway P) : St
ableUnderCompositionWithLocalizationAway P
参数：hPc : RingHom.StableUnderComposition P；hPl : HoldsForLocalizationAway P。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
    (hPc : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizationAway P) :
    StableUnderCompositionWithLocalizationAway P := by
  constructor
  · introv _ _ hf
    exact hPc _ _ (hPl S r) hf
  · introv _ _ hf
    exact hPc _ _ hf (hPl T s)
/-
**RingHom.HoldsForLocalizationAway.containsIdentities** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：RingHom.HoldsForLocalizationAway.containsIdentities (hPl : HoldsForLocaliz
ationAway P) : ContainsIdentities P
参数：hPl : HoldsForLocalizationAway P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.HoldsForLocalizationAway.of_bijective`：RingHom.HoldsForLocalizat
ionAway.of_bijective (H : RingHom.HoldsForLocalizationAway P) (hf : Function.Bij
ective f) : P f
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma RingHom.HoldsForLocalizationAway.containsIdentities (hPl : HoldsForLocalizationAway P) :
    ContainsIdentities P := by
  introv R
  exact hPl.of_bijective _ _ Function.bijective_id
/-
**RingHom.LocalizationAwayPreserves.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.LocalizationAwayPreserves.respectsIso (hP : LocalizationAwayPreser
ves P) : RespectsIso P where left {R S T} _ _ _ f e hf
参数：hP : LocalizationAwayPreserves P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.away_of_isUnit_of_bijective`：away_of_isUnit_of_bijective 
{R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] {r : R} 
(hr : IsUnit r) (H : Function.Bi…
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.Away.map.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (
S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {P : Type u_3}   
[inst_3 : CommSemi…
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
    have : RingHomInvPair (e : R →+* S) e.symm := RingHomInvPair.of_ringEquiv _
    have : (IsLocalization.Away.map R T f 1).comp e.symm.toRingHom = f :=
      IsLocalization.map_comp ..
    conv_lhs => rw [← this, RingHom.comp_assoc]
    simp only [RingEquiv.toRingHom_eq_coe, RingHomCompTriple.comp_eq]
/-
**RingHom.StableUnderCompositionWithLocalizationAway.respectsIso** 是 Mathlib 中的一
个引理，位于命名空间 ``。
形式化陈述：RingHom.StableUnderCompositionWithLocalizationAway.respectsIso (hP : Stabl
eUnderCompositionWithLocalizationAway P) : RespectsIso P where left {R S T} _ _ 
_ f e hf
参数：hP : StableUnderCompositionWithLocalizationAway P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.away_of_isUnit_of_bijective`：away_of_isUnit_of_bijective 
{R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] {r : R} 
(hr : IsUnit r) (H : Function.Bi…
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
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
/-
**RingHom.PropertyIsLocal.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.PropertyIsLocal.respectsIso (hP : RingHom.PropertyIsLocal @P) : Ri
ngHom.RespectsIso @P
参数：hP : RingHom.PropertyIsLocal @P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.LocalizationAwayPreserves.respectsIso`：RingHom.LocalizationAwayP
reserves.respectsIso (hP : LocalizationAwayPreserves P) : RespectsIso P where le
ft {R S T} _ _ _ f e hf
· 使用定理 `RingHom.PropertyIsLocal.localizationAwayPreserves`：∀ {P : {R S : Type u}
 → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pr
opertyIsLocal P → RingHom.LocalizationA…
-/
theorem RingHom.PropertyIsLocal.respectsIso (hP : RingHom.PropertyIsLocal @P) :
    RingHom.RespectsIso @P :=
  hP.localizationAwayPreserves.respectsIso

-- Almost all arguments are implicit since this is not intended to use mid-proof.
/-
**RingHom.LocalizationPreserves.away** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.LocalizationPreserves.away (H : RingHom.LocalizationPreserves @P) 
: RingHom.LocalizationAwayPreserves P
参数：H : RingHom.LocalizationPreserves @P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
-/
theorem RingHom.LocalizationPreserves.away (H : RingHom.LocalizationPreserves @P) :
    RingHom.LocalizationAwayPreserves P := by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf
/-
**RingHom.PropertyIsLocal.HoldsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.PropertyIsLocal.HoldsForLocalizationAway (hP : RingHom.PropertyIsL
ocal @P) (hPi : ContainsIdentities P) : RingHom.HoldsForLocalizationAway @P
参数：hP : RingHom.PropertyIsLocal @P；hPi : ContainsIdentities P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.PropertyIsLocal.StableUnderCompositionWithLocalizationAwayTarget
`：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S
) → Prop},   RingHom.PropertyIsLocal P → RingHom.StableUnderCo…
-/
lemma RingHom.PropertyIsLocal.HoldsForLocalizationAway (hP : RingHom.PropertyIsLocal @P)
    (hPi : ContainsIdentities P) :
    RingHom.HoldsForLocalizationAway @P := by
  introv R _
  have : algebraMap R S = (algebraMap R S).comp (RingHom.id R) := by simp
  rw [this]
  apply hP.StableUnderCompositionWithLocalizationAwayTarget S r
  apply hPi
/-
**RingHom.OfLocalizationSpanTarget.ofLocalizationSpan** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：RingHom.OfLocalizationSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocali
zationSpanTarget @P) (hP' : RingHom.StableUnderCompositionWithLocalizationAwaySo
urce @P) : RingHom.OfLocalizationSpan @P
参数：hP : RingHom.OfLocalizationSpanTarget @P；hP' : RingHom.StableUnderComposition
WithLocalizationAwaySource @P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
-/
theorem RingHom.OfLocalizationSpanTarget.ofLocalizationSpan
    (hP : RingHom.OfLocalizationSpanTarget @P)
    (hP' : RingHom.StableUnderCompositionWithLocalizationAwaySource @P) :
    RingHom.OfLocalizationSpan @P := by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply hP _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  rw [← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
    (T := Submonoid.powers (f r))]
  · apply hP' _ r
    exact hs' ⟨r, hr⟩
/-
**RingHom.OfLocalizationSpan.ofIsLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpan.ofIsLocalization (hP : RingHom.OfLocalizationSp
an P) (hPi : RingHom.RespectsIso P) {R S : Type u} [CommRing R] [CommRing S] (f 
: R ->+* S) (s : Set R) (hs : Ideal.span s = ⊤) (hT : forall r : s, exists (Rᵣ S
ᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ) (_ : Algebra R Rᵣ) (_ : Algebra 
S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ) (_ : IsLocalization.Away (f r.val) Sᵣ) 
(fᵣ : Rᵣ ->+* Sᵣ) (_ : fᵣ.comp (algebraMap R Rᵣ) = (algebraMap S Sᵣ).comp f), P 
fᵣ) : P f
参数：hP : RingHom.OfLocalizationSpan P；hPi : RingHom.RespectsIso P；f : R ->+* S；s 
: Set R；hs : Ideal.span s = ⊤；hT : forall r : s, exists (Rᵣ Sᵣ : Type u) (_ : Co
mmRing Rᵣ) (_ : CommRing Sᵣ) (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocali
zation.Away r.val Rᵣ) (_ : IsLocalization.Away (f r.val) Sᵣ) (fᵣ : Rᵣ ->+* Sᵣ) (
_ : fᵣ.comp (algebraMap R Rᵣ) = (algebraMap S Sᵣ).comp f), P fᵣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma RingHom.OfLocalizationSpan.ofIsLocalization
    (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (Rᵣ Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ)
      (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ)
      (_ : IsLocalization.Away (f r.val) Sᵣ) (fᵣ : Rᵣ →+* Sᵣ)
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
      rw [← RingHom.comp_apply, hfᵣ, RingHom.comp_apply]
    simp [-AlgEquiv.symm_toRingEquiv, e₂, e₁, Localization.awayMap, IsLocalization.Away.map, this]
  rw [this]
  apply hPi.right
  apply hPi.left
  exact hf

/-- Variant of `RingHom.OfLocalizationSpan.ofIsLocalization` where
`fᵣ = IsLocalization.Away.map`. -/
/-
**RingHom.OfLocalizationSpan.ofIsLocalization'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpan.ofIsLocalization' (hP : RingHom.OfLocalizationS
pan P) (hPi : RingHom.RespectsIso P) {R S : Type u} [CommRing R] [CommRing S] (f
 : R ->+* S) (s : Set R) (hs : Ideal.span s = ⊤) (hT : forall r : s, exists (Rᵣ 
Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ) (_ : Algebra R Rᵣ) (_ : Algebra
 S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ) (_ : IsLocalization.Away (f r.val) Sᵣ)
, P (IsLocalization.Away.map Rᵣ Sᵣ f r)) : P f
参数：hP : RingHom.OfLocalizationSpan P；hPi : RingHom.RespectsIso P；f : R ->+* S；s 
: Set R；hs : Ideal.span s = ⊤；hT : forall r : s, exists (Rᵣ Sᵣ : Type u) (_ : Co
mmRing Rᵣ) (_ : CommRing Sᵣ) (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocali
zation.Away r.val Rᵣ) (_ : IsLocalization.Away (f r.val) Sᵣ), P (IsLocalization.
Away.map Rᵣ Sᵣ f r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.OfLocalizationSpan.ofIsLocalization`：RingHom.OfLocalizationSpan.
ofIsLocalization (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso 
P) {R S : Type u} [CommRing R] [C…
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g

--- 原说明 ---
Variant of `RingHom.OfLocalizationSpan.ofIsLocalization` where
`fᵣ = IsLocalization.Away.map`.
-/
lemma RingHom.OfLocalizationSpan.ofIsLocalization'
    (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (Rᵣ Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ)
      (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ)
      (_ : IsLocalization.Away (f r.val) Sᵣ),
        P (IsLocalization.Away.map Rᵣ Sᵣ f r)) : P f := by
  apply hP.ofIsLocalization hPi _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, hf⟩ := hT r
  exact ⟨Rᵣ, Sᵣ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsLocalization.Away.map Rᵣ Sᵣ f r, IsLocalization.map_comp _, hf⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**RingHom.OfLocalizationSpanTarget.ofIsLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：RingHom.OfLocalizationSpanTarget.ofIsLocalization (hP : RingHom.OfLocaliza
tionSpanTarget P) (hP' : RingHom.RespectsIso P) {R S : Type u} [CommRing R] [Com
mRing S] (f : R ->+* S) (s : Set S) (hs : Ideal.span s = ⊤) (hT : forall r : s, 
exists (T : Type u) (_ : CommRing T) (_ : Algebra S T) (_ : IsLocalization.Away 
(r : S) T), P ((algebraMap S T).comp f)) : P f
参数：hP : RingHom.OfLocalizationSpanTarget P；hP' : RingHom.RespectsIso P；f : R ->+
* S；s : Set S；hs : Ideal.span s = ⊤；hT : forall r : s, exists (T : Type u) (_ : 
CommRing T) (_ : Algebra S T) (_ : IsLocalization.Away (r : S) T), P ((algebraMa
p S T).comp f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.toRingHom_eq_coe`：∀ {R : Type u_4} {S : Type u_5} [inst : NonA
ssocSemiring R] [inst_1 : NonAssocSemiring S] (f : R ≃+* S),   f.toRingHom = ↑f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `AlgEquiv.toRingEquiv_toRingHom`：toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂)
 : A₁ ->+* A₂) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Localization.coe_algEquiv_symm`：coe_algEquiv_symm : ((Localization.algEq
uiv M S).symm : S ->+* Localization M) = IsLocalization.map (M
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma RingHom.OfLocalizationSpanTarget.ofIsLocalization
    (hP : RingHom.OfLocalizationSpanTarget P) (hP' : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set S) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T)
      (_ : IsLocalization.Away (r : S) T), P ((algebraMap S T).comp f)) : P f := by
  apply hP _ s hs
  intro r
  obtain ⟨T, _, _, _, hT⟩ := hT r
  convert! hP'.1 _ (Localization.algEquiv (R := S) (Submonoid.powers (r : S)) T).symm.toRingEquiv hT
  rw [← RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, Localization.coe_algEquiv_symm, IsLocalization.map_comp,
    RingHom.comp_id]

section

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-
**RingHom.OfLocalizationSpanTarget.and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpanTarget.and (hP : OfLocalizationSpanTarget P) (hQ
 : OfLocalizationSpanTarget Q) : OfLocalizationSpanTarget (fun f => P f ∧ Q f)
参数：hP : OfLocalizationSpanTarget P；hQ : OfLocalizationSpanTarget Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma RingHom.OfLocalizationSpanTarget.and (hP : OfLocalizationSpanTarget P)
    (hQ : OfLocalizationSpanTarget Q) :
    OfLocalizationSpanTarget (fun f ↦ P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r ↦ (hf r).1, hQ f s hs fun r ↦ (hf r).2⟩
/-
**RingHom.OfLocalizationSpan.and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.OfLocalizationSpan.and (hP : OfLocalizationSpan P) (hQ : OfLocaliz
ationSpan Q) : OfLocalizationSpan (fun f => P f ∧ Q f)
参数：hP : OfLocalizationSpan P；hQ : OfLocalizationSpan Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma RingHom.OfLocalizationSpan.and (hP : OfLocalizationSpan P) (hQ : OfLocalizationSpan Q) :
    OfLocalizationSpan (fun f ↦ P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r ↦ (hf r).1, hQ f s hs fun r ↦ (hf r).2⟩
/-
**RingHom.LocalizationAwayPreserves.and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.LocalizationAwayPreserves.and (hP : LocalizationAwayPreserves P) (
hQ : LocalizationAwayPreserves Q) : LocalizationAwayPreserves (fun f => P f ∧ Q 
f)
参数：hP : LocalizationAwayPreserves P；hQ : LocalizationAwayPreserves Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma RingHom.LocalizationAwayPreserves.and (hP : LocalizationAwayPreserves P)
    (hQ : LocalizationAwayPreserves Q) :
    LocalizationAwayPreserves (fun f ↦ P f ∧ Q f) := by
  introv R h
  exact ⟨hP f r R' S' h.1, hQ f r R' S' h.2⟩
/-
**RingHom.StableUnderCompositionWithLocalizationAwayTarget.and** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：RingHom.StableUnderCompositionWithLocalizationAwayTarget.and (hP : StableU
nderCompositionWithLocalizationAwayTarget P) (hQ : StableUnderCompositionWithLoc
alizationAwayTarget Q) : StableUnderCompositionWithLocalizationAwayTarget (fun f
 => P f ∧ Q f)
参数：hP : StableUnderCompositionWithLocalizationAwayTarget P；hQ : StableUnderCompo
sitionWithLocalizationAwayTarget Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma RingHom.StableUnderCompositionWithLocalizationAwayTarget.and
    (hP : StableUnderCompositionWithLocalizationAwayTarget P)
    (hQ : StableUnderCompositionWithLocalizationAwayTarget Q) :
    StableUnderCompositionWithLocalizationAwayTarget (fun f ↦ P f ∧ Q f) := by
  introv R h hf
  exact ⟨hP T s f hf.1, hQ T s f hf.2⟩
/-
**RingHom.PropertyIsLocal.and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.PropertyIsLocal.and (hP : PropertyIsLocal P) (hQ : PropertyIsLocal
 Q) : PropertyIsLocal (fun f => P f ∧ Q f) where localizationAwayPreserves
参数：hP : PropertyIsLocal P；hQ : PropertyIsLocal Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.LocalizationAwayPreserves.and`：RingHom.LocalizationAwayPreserves
.and (hP : LocalizationAwayPreserves P) (hQ : LocalizationAwayPreserves Q) : Loc
alizationAwayPreserves (fun…
· 使用定理 `RingHom.PropertyIsLocal.localizationAwayPreserves`：∀ {P : {R S : Type u}
 → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pr
opertyIsLocal P → RingHom.LocalizationA…
· 使用引理 `RingHom.OfLocalizationSpanTarget.and`：RingHom.OfLocalizationSpanTarget.a
nd (hP : OfLocalizationSpanTarget P) (hQ : OfLocalizationSpanTarget Q) : OfLocal
izationSpanTarget (fun f =…
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpanTarget`：∀ {P : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pro
pertyIsLocal P → RingHom.OfLocalizatio…
· 使用引理 `RingHom.OfLocalizationSpan.and`：RingHom.OfLocalizationSpan.and (hP : OfL
ocalizationSpan P) (hQ : OfLocalizationSpan Q) : OfLocalizationSpan (fun f => P 
f ∧ Q f)
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpan`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.PropertyI
sLocal P → RingHom.OfLocalizatio…
· 使用引理 `RingHom.StableUnderCompositionWithLocalizationAwayTarget.and`：RingHom.St
ableUnderCompositionWithLocalizationAwayTarget.and (hP : StableUnderCompositionW
ithLocalizationAwayTarget P) (hQ : StableUnderComp…
· 使用定理 `RingHom.PropertyIsLocal.StableUnderCompositionWithLocalizationAwayTarget
`：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S
) → Prop},   RingHom.PropertyIsLocal P → RingHom.StableUnderCo…
-/
lemma RingHom.PropertyIsLocal.and (hP : PropertyIsLocal P) (hQ : PropertyIsLocal Q) :
    PropertyIsLocal (fun f ↦ P f ∧ Q f) where
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

/-- Let `S` be an `R`-algebra and `Sᵣ` and `Rᵣ` be the respective localizations at a submonoid
`M` of `R`. If `P` is stable under base change and `P` holds for `algebraMap R S`, then
`P` holds for `algebraMap Rᵣ Sᵣ`. -/
/-
**RingHom.IsStableUnderBaseChange.of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：RingHom.IsStableUnderBaseChange.of_isLocalization [Algebra R S] [Algebra R
 Sᵣ] [Algebra Rᵣ Sᵣ] [IsScalarTower R S Sᵣ] [IsScalarTower R Rᵣ Sᵣ] (M : Submono
id R) [IsLocalization M Rᵣ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ
] (h : P (algebraMap R S)) : P (algebraMap Rᵣ Sᵣ)
参数：M : Submonoid R；Algebra.algebraMapSubmonoid S M；h : P (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B

--- 原说明 ---
Let `S` be an `R`-algebra and `Sᵣ` and `Rᵣ` be the respective localizations at a
 submonoid
`M` of `R`. If `P` is stable under base change and `P` holds for `algebraMap R S
`, then
`P` holds for `algebraMap Rᵣ Sᵣ`.
-/
lemma RingHom.IsStableUnderBaseChange.of_isLocalization [Algebra R S] [Algebra R Sᵣ] [Algebra Rᵣ Sᵣ]
    [IsScalarTower R S Sᵣ] [IsScalarTower R Rᵣ Sᵣ]
    (M : Submonoid R) [IsLocalization M Rᵣ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ]
    (h : P (algebraMap R S)) : P (algebraMap Rᵣ Sᵣ) :=
  letI : Algebra.IsPushout R S Rᵣ Sᵣ := Algebra.isPushout_of_isLocalization M Rᵣ S Sᵣ
  hP R S Rᵣ Sᵣ h

/-- If `P` is stable under base change and holds for `f`, then `P` holds for `f` localized
at any submonoid `M` of `R`. -/
/-
**RingHom.IsStableUnderBaseChange.isLocalization_map** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：RingHom.IsStableUnderBaseChange.isLocalization_map (M : Submonoid R) [IsLo
calization M Rᵣ] (f : R ->+* S) [IsLocalization (M.map f) Sᵣ] (hf : P f) : P (Is
Localization.map Sᵣ f M.le_comap_map : Rᵣ ->+* Sᵣ)
参数：M : Submonoid R；f : R ->+* S；M.map f；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用引理 `RingHom.IsStableUnderBaseChange.of_isLocalization`：RingHom.IsStableUnder
BaseChange.of_isLocalization [Algebra R S] [Algebra R Sᵣ] [Algebra Rᵣ Sᵣ] [IsSca
larTower R S Sᵣ] [IsScalarTower R Rᵣ Sᵣ…

--- 原说明 ---
If `P` is stable under base change and holds for `f`, then `P` holds for `f` loc
alized
at any submonoid `M` of `R`.
-/
lemma RingHom.IsStableUnderBaseChange.isLocalization_map (M : Submonoid R) [IsLocalization M Rᵣ]
    (f : R →+* S) [IsLocalization (M.map f) Sᵣ] (hf : P f) :
    P (IsLocalization.map Sᵣ f M.le_comap_map : Rᵣ →+* Sᵣ) := by
  algebraize [f, IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map,
    (IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map).comp (algebraMap R Rᵣ)]
  have : IsScalarTower R S Sᵣ := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map)
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ :=
    inferInstanceAs <| IsLocalization (M.map f) Sᵣ
  apply hP.of_isLocalization M hf
/-
**RingHom.IsStableUnderBaseChange.localizationPreserves** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：RingHom.IsStableUnderBaseChange.localizationPreserves : LocalizationPreser
ves P
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsStableUnderBaseChange.isLocalization_map`：RingHom.IsStableUnde
rBaseChange.isLocalization_map (M : Submonoid R) [IsLocalization M Rᵣ] (f : R ->
+* S) [IsLocalization (M.map f) Sᵣ] (hf …
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

/-
**Ideal.localized'_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   (p : Submonoid R) [inst_3 : IsLocalization p S]
 (I : Ideal R),   Submodule.localized' S p (Algebra.linearMap R S) I = Ideal.map
 (algebraMap R S) I
参数：S : Type u_2；p : Submonoid R；I : Ideal R；Algebra.linearMap R S；algebraMap R S
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Submodule.localized'_eq_span`：∀ {R : Type u_1} (S : Type u_2) {M : Type 
u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 
: AddCommMonoid M]…
· 使用定理 `Algebra.coe_linearMap`：coe_linearMap : ⇑(Algebra.linearMap R A) = algebr
aMap R A
-/
theorem Ideal.localized'_eq_map (I : Ideal R) :
    Submodule.localized' S p (Algebra.linearMap R S) I = I.map (algebraMap R S) := by
  rw [map, span, Submodule.localized'_eq_span, Algebra.coe_linearMap]
/-
**Ideal.localized** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ideal.localized₀_eq_restrictScalars_map (I : Ideal R) :
    Submodule.localized₀ p (Algebra.linearMap R S) I = (I.map (algebraMap R S)).restrictScalars R :=
  congr(Submodule.restrictScalars R $(localized'_eq_map S p I))
/-
**Algebra.idealMap_eq_ofEq_comp_toLocalized** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Algebra.idealMap_eq_ofEq_comp_toLocalized₀ (I : Ideal R) :
    Algebra.idealMap S I =
      (LinearEquiv.ofEq _ _ <| Ideal.localized₀_eq_restrictScalars_map S p I).toLinearMap ∘ₗ
      Submodule.toLocalized₀ p (Algebra.linearMap R S) I :=
  rfl
/-
**Ideal.mem_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mem_of_localization_maximal {r : R} {J : Ideal R} (h : forall (P : I
deal R) (_ : P.IsMaximal), algebraMap R _ r in Ideal.map (algebraMap R (Localiza
tion.AtPrime P)) J) : r in J
参数：h : forall (P : Ideal R) (_ : P.IsMaximal), algebraMap R _ r in Ideal.map (al
gebraMap R (Localization.AtPrime P)) J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.mem_of_localization_maximal`：Submodule.mem_of_localization_max
imal (m : M) (N : Submodule R M) (h : forall (P : Ideal R) [P.IsMaximal], f P m 
in N.localized₀ P.primeComp…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.localized'_eq_map`：∀ {R : Type u_1} (S : Type u_2) [inst : CommSem
iring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   (p : Submonoid R) [i
nst_3 : IsLoc…
-/
theorem Ideal.mem_of_localization_maximal {r : R} {J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      algebraMap R _ r ∈ Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    r ∈ J :=
  Submodule.mem_of_localization_maximal _ _ _ _ fun P hP ↦ by
    apply (localized'_eq_map (Localization.AtPrime P) P.primeCompl J).symm ▸ h P hP

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is included in
the localization of `J` at `P`, then `I ≤ J`. -/
/-
**Ideal.le_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.le_of_localization_maximal {I J : Ideal R} (h : forall (P : Ideal R)
 (_ : P.IsMaximal), Ideal.map (algebraMap R (Localization.AtPrime P)) I <= Ideal
.map (algebraMap R (Localization.AtPrime P)) J) : I <= J
参数：h : forall (P : Ideal R) (_ : P.IsMaximal), Ideal.map (algebraMap R (Localiza
tion.AtPrime P)) I <= Ideal.map (algebraMap R (Localization.AtPrime P)) J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.mem_of_localization_maximal`：Ideal.mem_of_localization_maximal {r 
: R} {J : Ideal R} (h : forall (P : Ideal R) (_ : P.IsMaximal), algebraMap R _ r
 in Ideal.map (algebraM…
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I

--- 原说明 ---
Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is inc
luded in
the localization of `J` at `P`, then `I ≤ J`.
-/
theorem Ideal.le_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I ≤
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I ≤ J :=
  fun _ hm ↦ mem_of_localization_maximal fun P hP ↦ h P hP (mem_map_of_mem _ hm)
/-
**Ideal.iInf_ker_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.iInf_ker_le (I : Ideal R) : ⨅ (p : Ideal R) (_ : p.IsPrime) (_ : I <
= p), RingHom.ker (algebraMap R (Localization.AtPrime p)) <= I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_of_localization_maximal`：Ideal.mem_of_localization_maximal {r 
: R} {J : Ideal R} (h : forall (P : Ideal R) (_ : P.IsMaximal), algebraMap R _ r
 in Ideal.map (algebraM…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IsLocalization.AtPrime.map_eq_top_of_not_le`：map_eq_top_of_not_le {I : I
deal R} {p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p] (hle : ¬ I <= p) 
: Ideal.map (algebraMap R S) I = …
-/
lemma Ideal.iInf_ker_le (I : Ideal R) :
    ⨅ (p : Ideal R) (_ : p.IsPrime) (_ : I ≤ p),
      RingHom.ker (algebraMap R (Localization.AtPrime p)) ≤ I := by
  intro x hx
  refine Ideal.mem_of_localization_maximal fun m hm ↦ ?_
  simp only [Submodule.mem_iInf, RingHom.mem_ker] at hx
  by_cases hle : I ≤ m
  · simp [hx _ _ hle]
  · simp [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is equal to
the localization of `J` at `P`, then `I = J`. -/
/-
**Ideal.eq_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.eq_of_localization_maximal {I J : Ideal R} (h : forall (P : Ideal R)
 (_ : P.IsMaximal), Ideal.map (algebraMap R (Localization.AtPrime P)) I = Ideal.
map (algebraMap R (Localization.AtPrime P)) J) : I = J
参数：h : forall (P : Ideal R) (_ : P.IsMaximal), Ideal.map (algebraMap R (Localiza
tion.AtPrime P)) I = Ideal.map (algebraMap R (Localization.AtPrime P)) J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.le_of_localization_maximal`：Ideal.le_of_localization_maximal {I J 
: Ideal R} (h : forall (P : Ideal R) (_ : P.IsMaximal), Ideal.map (algebraMap R 
(Localization.AtPrime …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is equ
al to
the localization of `J` at `P`, then `I = J`.
-/
theorem Ideal.eq_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I = J :=
  le_antisymm (le_of_localization_maximal fun P hP ↦ (h P hP).le)
    (le_of_localization_maximal fun P hP ↦ (h P hP).ge)

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
/-
**ideal_eq_bot_of_localization'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ideal_eq_bot_of_localization' (I : Ideal R) (h : forall (J : Ideal R) (_ :
 J.IsMaximal), Ideal.map (algebraMap R (Localization.AtPrime J)) I = ⊥) : I = ⊥
参数：I : Ideal R；h : forall (J : Ideal R) (_ : J.IsMaximal), Ideal.map (algebraMap
 R (Localization.AtPrime J)) I = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.eq_of_localization_maximal`：Ideal.eq_of_localization_maximal {I J 
: Ideal R} (h : forall (P : Ideal R) (_ : P.IsMaximal), Ideal.map (algebraMap R 
(Localization.AtPrime …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥

--- 原说明 ---
An ideal is trivial if its localization at every maximal ideal is trivial.
-/
theorem ideal_eq_bot_of_localization' (I : Ideal R)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime J)) I = ⊥) :
    I = ⊥ :=
  Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP
/-
**eq_zero_of_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_localization (r : R) (h : forall (J : Ideal R) (_ : J.IsMaximal
), algebraMap R (Localization.AtPrime J) r = 0) : r = 0
参数：r : R；h : forall (J : Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.
AtPrime J) r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.eq_zero_of_localization_maximal`：Module.eq_zero_of_localization_m
aximal (m : M) (h : forall (P : Ideal R) [P.IsMaximal], f P m = 0) : m = 0
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
-/
theorem eq_zero_of_localization (r : R)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) :
    r = 0 :=
  Module.eq_zero_of_localization_maximal _ (fun _ _ ↦ Algebra.linearMap R _) r h

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
/-
**ideal_eq_bot_of_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ideal_eq_bot_of_localization (I : Ideal R) (h : forall (J : Ideal R) (_ : 
J.IsMaximal), IsLocalization.coeSubmodule (Localization.AtPrime J) I = ⊥) : I = 
⊥
参数：I : Ideal R；h : forall (J : Ideal R) (_ : J.IsMaximal), IsLocalization.coeSub
module (Localization.AtPrime J) I = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `eq_zero_of_localization`：eq_zero_of_localization (r : R) (h : forall (J 
: Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) : r =
 0
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
An ideal is trivial if its localization at every maximal ideal is trivial.
-/
theorem ideal_eq_bot_of_localization (I : Ideal R)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
      IsLocalization.coeSubmodule (Localization.AtPrime J) I = ⊥) :
    I = ⊥ :=
  bot_unique fun r hr ↦ eq_zero_of_localization r fun J hJ ↦ (h J hJ).le ⟨r, hr, rfl⟩

end Ideal

