/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Basic

/-!

# Localization over left Ore sets.

This file defines the localization of a monoid over a left Ore set and proves its universal
mapping property.

## Notation

Introduces the notation `R[S⁻¹]` for the Ore localization of a monoid `R` at a right Ore
subset `S`. Also defines a new heterogeneous division notation `r /ₒ s` for a numerator `r : R` and
a denominator `s : S`.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

## Implementation detail

Some of the declarations are marked reducible to avoid diamonds with
`Mathlib/Algebra/Module/LocalizedModule/Basic.lean`. This causes a significant performance
regression, most notably in `Mathlib/AlgebraicGeometry/AffineSpace.lean`.
Also see https://github.com/leanprover-community/mathlib4/pull/31862.

We shall investigate if there are ways to improve performances. For example by introducing
typeclasses to unify the two constructions on this and `LocalizedModule`, or by marking some
downstream constructions (e.g. `Spec.structureSheaf`) as irreducible.

-/

@[expose] public section

assert_not_exists RelIso MonoidWithZero

universe u

open OreLocalization

namespace OreLocalization

variable {R : Type*} [Monoid R] (S : Submonoid R) [OreSet S] (X) [MulAction R X]

/-- The setoid on `R × S` used for the Ore localization. -/
@[to_additive (attr := instance_reducible) AddOreLocalization.oreEqv
  /-- The setoid on `R × S` used for the Ore localization. -/]
/--
Definition of `oreEqv` / `oreEqv` 的定义

English:
definition oreEqv
  signature: : Setoid (X × S) where
  body: exists (u : S) (v : R), u • rs'.1 = v • rs.1 ∧ u * rs'.2 = v * rs.2
  iseqv := by
    refine ⟨fun _ => ⟨1, 1, by simp⟩, ?_, ?_⟩
    · rintro ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩; dsimp only at *
      rcases oreCondition (s : R) s' with ⟨r₂, s₂, h₁⟩
      rcases oreCondition r₂ u with ⟨r₃, s₃, h₂⟩
      have : r₃ * v * s = s₃ * s₂ * s := by
        -- Porting note: the proof used `assoc_rw`
        rw [mul_assoc _ (s₂ : R)]; rw [h₁]; rw [← mul_assoc]; rw [h₂]; rw [mul_assoc]; rw [← hsu]; rw [← mul_assoc]
      rcases ore_right_cancel (r₃ * v) (s₃ * s₂) s this with ⟨w, hw⟩
      refine ⟨w * (s₃ * s₂), w * (r₃ * u), ?_, ?_⟩ <;>
        simp only [Submonoid.coe_mul, Submonoid.smul_def, ← hw]
      · simp only [mul_smul, hru, ← Submonoid.smul_def]
      · simp only [mul_assoc, hsu]
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩
      rcases oreCondition v' u with ⟨r', s', h⟩; dsimp only at *
      refine ⟨s' * u', r' * v, ?_, ?_⟩ <;>
        simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, mul_assoc] at *
      · rw [hur₂, smul_smul, h, mul_smul, hur₁]
      · rw [hs₂u, ← mul_assoc, h, mul_assoc, hs₁u]

中文:
定义 oreEqv
  签名: : 集合等价关系 (X × S) where
  定义体: exists (u : S) (v : R), u • rs'.1 = v • rs.1 ∧ u * rs'.2 = v * rs.2
  iseqv := by
    refine ⟨fun _ => ⟨1, 1, by simp⟩, ?_, ?_⟩
    · rintro ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩; dsimp only at *
      rcases oreCondition (s : R) s' with ⟨r₂, s₂, h₁⟩
      rcases oreCondition r₂ u with ⟨r₃, s₃, h₂⟩
      have : r₃ * v * s = s₃ * s₂ * s := by
        -- Porting note: the proof used `assoc_rw`
        rw [mul_assoc _ (s₂ : R)]; rw [h₁]; rw [← mul_assoc]; rw [h₂]; rw [mul_assoc]; rw [← hsu]; rw [← mul_assoc]
      rcases ore_right_cancel (r₃ * v) (s₃ * s₂) s this with ⟨w, hw⟩
      refine ⟨w * (s₃ * s₂), w * (r₃ * u), ?_, ?_⟩ <;>
        simp only [Submonoid.coe_mul, Submonoid.smul_def, ← hw]
      · simp only [mul_smul, hru, ← Submonoid.smul_def]
      · simp only [mul_assoc, hsu]
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩
      rcases oreCondition v' u with ⟨r', s', h⟩; dsimp only at *
      refine ⟨s' * u', r' * v, ?_, ?_⟩ <;>
        simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, mul_assoc] at *
      · rw [hur₂, smul_smul, h, mul_smul, hur₁]
      · rw [hs₂u, ← mul_assoc, h, mul_assoc, hs₁u]
-/
def oreEqv : Setoid (X × S) where
  r rs rs' := exists (u : S) (v : R), u • rs'.1 = v • rs.1 ∧ u * rs'.2 = v * rs.2
  iseqv := by
    refine ⟨fun _ => ⟨1, 1, by simp⟩, ?_, ?_⟩
    · rintro ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩; dsimp only at *
      rcases oreCondition (s : R) s' with ⟨r₂, s₂, h₁⟩
      rcases oreCondition r₂ u with ⟨r₃, s₃, h₂⟩
      have : r₃ * v * s = s₃ * s₂ * s := by
        -- Porting note: the proof used `assoc_rw`
        rw [mul_assoc _ (s₂ : R)]; rw [h₁]; rw [← mul_assoc]; rw [h₂]; rw [mul_assoc]; rw [← hsu]; rw [← mul_assoc]
      rcases ore_right_cancel (r₃ * v) (s₃ * s₂) s this with ⟨w, hw⟩
      refine ⟨w * (s₃ * s₂), w * (r₃ * u), ?_, ?_⟩ <;>
        simp only [Submonoid.coe_mul, Submonoid.smul_def, ← hw]
      · simp only [mul_smul, hru, ← Submonoid.smul_def]
      · simp only [mul_assoc, hsu]
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩
      rcases oreCondition v' u with ⟨r', s', h⟩; dsimp only at *
      refine ⟨s' * u', r' * v, ?_, ?_⟩ <;>
        simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, mul_assoc] at *
      · rw [hur₂, smul_smul, h, mul_smul, hur₁]
      · rw [hs₂u, ← mul_assoc, h, mul_assoc, hs₁u]

end OreLocalization

/-- The Ore localization of a monoid and a submonoid fulfilling the Ore condition. -/
@[to_additive AddOreLocalization /-- The Ore localization of an additive monoid and a submonoid
fulfilling the Ore condition. -/]
/--
Definition of `OreLocalization` / `OreLocalization` 的定义

English:
definition OreLocalization
  signature: {R : Type*} [Monoid R] (S : Submonoid R) [OreSet S]
  body: Quotient (OreLocalization.oreEqv S X)

中文:
定义 OreLocalization
  签名: {R : 类型} [幺半群 R] (S : 子幺半群 R) [OreSet S]
  定义体: Quotient (OreLocalization.oreEqv S X)

Depends on / 依赖: OreLocalization, OreLocalization.oreEqv, Quotient, oreEqv
-/
def OreLocalization {R : Type*} [Monoid R] (S : Submonoid R) [OreSet S]
    (X : Type*) [MulAction R X] :=
  Quotient (OreLocalization.oreEqv S X)

namespace OreLocalization

section Monoid

variable (R : Type*) [Monoid R] (S : Submonoid R) [OreSet S]

@[inherit_doc OreLocalization]
scoped syntax:1075 term noWs atomic("[" term "⁻¹" noWs "]") : term
macro_rules | `($R[$S⁻¹]) => ``(OreLocalization $S $R)

attribute [local instance] oreEqv

variable {R S}
variable {X} [MulAction R X]

/-- The division in the Ore localization `X[S⁻¹]`, as a fraction of an element of `X` and `S`. -/
@[to_additive /-- The subtraction in the Ore localization,
as a difference of an element of `X` and `S`. -/]
/--
Definition of `oreDiv` / `oreDiv` 的定义

English:
definition oreDiv
  signature: (r : X) (s : S)
  body: Quotient.mk' (r, s)

@[inherit_doc]
infixl:70 " /ₒ " => oreDiv

@[inherit_doc]
infixl:65 " -ₒ " => _root_.AddOreLocalization.oreSub

@[to_additive (attr := elab_as_elim, cases_eliminator, induction_eliminator)]

中文:
定义 oreDiv
  签名: (r : X) (s : S)
  定义体: Quotient.mk' (r, s)

@[inherit_doc]
infixl:70 " /ₒ " => oreDiv

@[inherit_doc]
infixl:65 " -ₒ " => _root_.AddOreLocalization.oreSub

@[to_additive (attr := elab_as_elim, cases_eliminator, induction_eliminator)]

Depends on / 依赖: Quotient, Quotient.mk
-/
def oreDiv (r : X) (s : S) : X[S⁻¹] :=
  Quotient.mk' (r, s)

@[inherit_doc]
infixl:70 " /ₒ " => oreDiv

@[inherit_doc]
infixl:65 " -ₒ " => _root_.AddOreLocalization.oreSub

@[to_additive (attr := elab_as_elim, cases_eliminator, induction_eliminator)]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {β : X[S⁻¹] -> Prop}
  proof: by
  apply Quotient.ind
  rintro ⟨r, s⟩
  exact c r s

@[to_additive]

中文:
定理 ind
  结论: {β : X[S⁻¹] -> 命题}
  证明: by
  apply Quotient.ind
  rintro ⟨r, s⟩
  exact c r s

@[to_additive]
-/
protected theorem ind {β : X[S⁻¹] -> Prop}
    (c : forall (r : X) (s : S), β (r /ₒ s)) : forall q, β q := by
  apply Quotient.ind
  rintro ⟨r, s⟩
  exact c r s

@[to_additive]
/--
theorem `oreDiv_eq_iff` / 定理 `oreDiv_eq_iff`

English:
theorem oreDiv_eq_iff
  given: {r₁ r₂ : X} {s₁ s₂ : S}
  proof: Quotient.eq''

中文:
定理 oreDiv_eq_iff
  条件: {r₁ r₂ : X} {s₁ s₂ : S}
  证明: Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} :
    r₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁ :=
  Quotient.eq''

/-- A fraction `r /ₒ s` is equal to its expansion by an arbitrary factor `t` if `t * s ∈ S`. -/
@[to_additive /-- A difference `r -ₒ s` is equal to its expansion by an
arbitrary translation `t` if `t + s ∈ S`. -/]
/--
theorem `expand` / 定理 `expand`

English:
theorem expand
  given: (r : X) (s : S) (t : R) (hst : t * (s : R) in S)
  proof: by
  apply Quotient.sound
  exact ⟨s, s * t, by rw [mul_smul, Submonoid.smul_def], by rw [← mul_assoc]⟩

中文:
定理 expand
  条件: (r : X) (s : S) (t : R) (hst : t * (s : R) in S)
  证明: by
  apply Quotient.sound
  exact ⟨s, s * t, by rw [mul_smul, Submonoid.smul_def], by rw [← mul_assoc]⟩
-/
protected theorem expand (r : X) (s : S) (t : R) (hst : t * (s : R) in S) :
    r /ₒ s = t • r /ₒ ⟨t * s, hst⟩ := by
  apply Quotient.sound
  exact ⟨s, s * t, by rw [mul_smul, Submonoid.smul_def], by rw [← mul_assoc]⟩

/-- A fraction is equal to its expansion by a factor from `S`. -/
@[to_additive /-- A difference is equal to its expansion by a summand from `S`. -/]
/--
theorem `expand'` / 定理 `expand'`

English:
theorem expand'
  given: (r : X) (s s' : S)
  statement: r /ₒ s = s' • r /ₒ (s' * s)
  proof: OreLocalization.expand r s s' (by norm_cast; apply SetLike.coe_mem)

中文:
定理 expand'
  条件: (r : X) (s s' : S)
  结论: r /ₒ s = s' • r /ₒ (s' * s)
  证明: OreLocalization.expand r s s' (by norm_cast; apply SetLike.coe_mem)
-/
protected theorem expand' (r : X) (s s' : S) : r /ₒ s = s' • r /ₒ (s' * s) :=
  OreLocalization.expand r s s' (by norm_cast; apply SetLike.coe_mem)

/-- Fractions which differ by a factor of the numerator can be proven equal if
those factors expand to equal elements of `R`. -/
@[to_additive /-- Differences whose minuends differ by a common summand can be proven equal if
those summands expand to equal elements of `R`. -/]
/--
theorem `eq_of_num_factor_eq` / 定理 `eq_of_num_factor_eq`

English:
theorem eq_of_num_factor_eq
  given: {r r' r₁ r₂ : R} {s t : S} (h : t * r = t * r')
  proof: by
  rcases oreCondition r₁ t with ⟨r₁', t', hr₁⟩
  rw [OreLocalization.expand' _ s t']; rw [OreLocalization.expand' _ s t']
  congr 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `assoc_rw`?
  calc (t' : R) * (r₁ * r * r₂)
      = t' * r₁ * r * r₂ := by simp [← mul_assoc]
    _ = r₁' * t * r * r₂ := by rw [hr₁]
    _ = r₁' * (t * r) * r₂ := by simp [← mul_assoc]
    _ = r₁' * (t * r') * r₂ := by rw [h]
    _ = r₁' * t * r' * r₂ := by simp [← mul_assoc]
    _ = t' * r₁ * r' * r₂ := by rw [hr₁]
    _ = t' * (r₁ * r' * r₂) := by simp [← mul_assoc]

中文:
定理 eq_of_num_factor_eq
  条件: {r r' r₁ r₂ : R} {s t : S} (h : t * r = t * r')
  证明: by
  rcases oreCondition r₁ t with ⟨r₁', t', hr₁⟩
  rw [OreLocalization.expand' _ s t']; rw [OreLocalization.expand' _ s t']
  congr 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `assoc_rw`?
  calc (t' : R) * (r₁ * r * r₂)
      = t' * r₁ * r * r₂ := by simp [← mul_assoc]
    _ = r₁' * t * r * r₂ := by rw [hr₁]
    _ = r₁' * (t * r) * r₂ := by simp [← mul_assoc]
    _ = r₁' * (t * r') * r₂ := by rw [h]
    _ = r₁' * t * r' * r₂ := by simp [← mul_assoc]
    _ = t' * r₁ * r' * r₂ := by rw [hr₁]
    _ = t' * (r₁ * r' * r₂) := by simp [← mul_assoc]
-/
protected theorem eq_of_num_factor_eq {r r' r₁ r₂ : R} {s t : S} (h : t * r = t * r') :
    r₁ * r * r₂ /ₒ s = r₁ * r' * r₂ /ₒ s := by
  rcases oreCondition r₁ t with ⟨r₁', t', hr₁⟩
  rw [OreLocalization.expand' _ s t']; rw [OreLocalization.expand' _ s t']
  congr 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `assoc_rw`?
  calc (t' : R) * (r₁ * r * r₂)
      = t' * r₁ * r * r₂ := by simp [← mul_assoc]
    _ = r₁' * t * r * r₂ := by rw [hr₁]
    _ = r₁' * (t * r) * r₂ := by simp [← mul_assoc]
    _ = r₁' * (t * r') * r₂ := by rw [h]
    _ = r₁' * t * r' * r₂ := by simp [← mul_assoc]
    _ = t' * r₁ * r' * r₂ := by rw [hr₁]
    _ = t' * (r₁ * r' * r₂) := by simp [← mul_assoc]

/-- A function or predicate over `X` and `S` can be lifted to `X[S⁻¹]` if it is invariant
under expansion on the left. -/
@[to_additive /-- A function or predicate over `X` and `S` can be lifted to the localization if it
is invariant under expansion on the left. -/]
/--
Definition of `liftExpand` / `liftExpand` 的定义

English:
definition liftExpand
  signature: {C : Sort*} (P : X -> S -> C)
  body: Quotient.lift (fun p : X × S => P p.1 p.2) fun (r₁, s₁) (r₂, s₂) ⟨u, v, hr₂, hs₂⟩ => by
    dsimp at *
    have s₁vS : v * s₁ in S := by
      rw [← hs₂]; rw [← S.coe_mul]
      exact SetLike.coe_mem (u * s₂)
    replace hs₂ : u * s₂ = ⟨_, s₁vS⟩ := by ext; simp [hs₂]
    rw [hP r₁ v s₁ s₁vS]; rw [hP r₂ u s₂ (by norm_cast; rwa [hs₂]), ← hr₂]
    simp only [← hs₂]; rfl

@[to_additive (attr := simp)]

中文:
定义 liftExpand
  签名: {C : 类型层*} (P : X -> S -> C)
  定义体: Quotient.lift (fun p : X × S => P p.1 p.2) fun (r₁, s₁) (r₂, s₂) ⟨u, v, hr₂, hs₂⟩ => by
    dsimp at *
    have s₁vS : v * s₁ in S := by
      rw [← hs₂]; rw [← S.coe_mul]
      exact SetLike.coe_mem (u * s₂)
    replace hs₂ : u * s₂ = ⟨_, s₁vS⟩ := by ext; simp [hs₂]
    rw [hP r₁ v s₁ s₁vS]; rw [hP r₂ u s₂ (by norm_cast; rwa [hs₂]), ← hr₂]
    simp only [← hs₂]; rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.lift, S.coe_mul, SetLike, SetLike.coe_mem, coe_mem, coe_mul, replace
-/
def liftExpand {C : Sort*} (P : X -> S -> C)
    (hP : forall (r : X) (t : R) (s : S) (ht : t * s in S), P r s = P (t • r) ⟨t * s, ht⟩) :
    X[S⁻¹] -> C :=
  Quotient.lift (fun p : X × S => P p.1 p.2) fun (r₁, s₁) (r₂, s₂) ⟨u, v, hr₂, hs₂⟩ => by
    dsimp at *
    have s₁vS : v * s₁ in S := by
      rw [← hs₂]; rw [← S.coe_mul]
      exact SetLike.coe_mem (u * s₂)
    replace hs₂ : u * s₂ = ⟨_, s₁vS⟩ := by ext; simp [hs₂]
    rw [hP r₁ v s₁ s₁vS]; rw [hP r₂ u s₂ (by norm_cast; rwa [hs₂]), ← hr₂]
    simp only [← hs₂]; rfl

@[to_additive (attr := simp)]
/--
theorem `liftExpand_of` / 定理 `liftExpand_of`

English:
theorem liftExpand_of
  statement: {C : Sort*} {P : X -> S -> C}
  proof: rfl

中文:
定理 liftExpand_of
  结论: {C : 类型层*} {P : X -> S -> C}
  证明: rfl
-/
theorem liftExpand_of {C : Sort*} {P : X -> S -> C}
    {hP : forall (r : X) (t : R) (s : S) (ht : t * s in S), P r s = P (t • r) ⟨t * s, ht⟩} (r : X)
    (s : S) : liftExpand P hP (r /ₒ s) = P r s :=
  rfl

/-- A version of `liftExpand` used to simultaneously lift functions with two arguments
in `X[S⁻¹]`. -/
@[to_additive
/-- A version of `liftExpand` used to simultaneously lift functions with two arguments. -/]
/--
Definition of `lift₂Expand` / `lift₂Expand` 的定义

English:
definition lift₂Expand
  signature: {C : Sort*} (P : X -> S -> X -> S -> C)
  body: liftExpand
    (fun r₁ s₁ => liftExpand (P r₁ s₁) fun r₂ t₂ s₂ ht₂ => by
      have := hP r₁ 1 s₁ (by simp) r₂ t₂ s₂ ht₂
      simp [this])
    fun r₁ t₁ s₁ ht₁ => by
    ext x; cases x with | _ r₂ s₂
    rw [liftExpand_of]; rw [liftExpand_of]; rw [hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)]; simp

@[to_additive (attr := simp)]

中文:
定义 lift₂Expand
  签名: {C : 类型层*} (P : X -> S -> X -> S -> C)
  定义体: liftExpand
    (fun r₁ s₁ => liftExpand (P r₁ s₁) fun r₂ t₂ s₂ ht₂ => by
      have := hP r₁ 1 s₁ (by simp) r₂ t₂ s₂ ht₂
      simp [this])
    fun r₁ t₁ s₁ ht₁ => by
    ext x; cases x with | _ r₂ s₂
    rw [liftExpand_of]; rw [liftExpand_of]; rw [hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)]; simp

@[to_additive (attr := simp)]

Depends on / 依赖: liftExpand, liftExpand_of
-/
def lift₂Expand {C : Sort*} (P : X -> S -> X -> S -> C)
    (hP :
      forall (r₁ : X) (t₁ : R) (s₁ : S) (ht₁ : t₁ * s₁ in S) (r₂ : X) (t₂ : R) (s₂ : S)
        (ht₂ : t₂ * s₂ in S),
        P r₁ s₁ r₂ s₂ = P (t₁ • r₁) ⟨t₁ * s₁, ht₁⟩ (t₂ • r₂) ⟨t₂ * s₂, ht₂⟩) :
    X[S⁻¹] -> X[S⁻¹] -> C :=
  liftExpand
    (fun r₁ s₁ => liftExpand (P r₁ s₁) fun r₂ t₂ s₂ ht₂ => by
      have := hP r₁ 1 s₁ (by simp) r₂ t₂ s₂ ht₂
      simp [this])
    fun r₁ t₁ s₁ ht₁ => by
    ext x; cases x with | _ r₂ s₂
    rw [liftExpand_of]; rw [liftExpand_of]; rw [hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)]; simp

@[to_additive (attr := simp)]
/--
theorem `lift₂Expand_of` / 定理 `lift₂Expand_of`

English:
theorem lift₂Expand_of
  statement: {C : Sort*} {P : X -> S -> X -> S -> C}
  proof: rfl

中文:
定理 lift₂Expand_of
  结论: {C : 类型层*} {P : X -> S -> X -> S -> C}
  证明: rfl
-/
theorem lift₂Expand_of {C : Sort*} {P : X -> S -> X -> S -> C}
    {hP :
      forall (r₁ : X) (t₁ : R) (s₁ : S) (ht₁ : t₁ * s₁ in S) (r₂ : X) (t₂ : R) (s₂ : S)
        (ht₂ : t₂ * s₂ in S),
        P r₁ s₁ r₂ s₂ = P (t₁ • r₁) ⟨t₁ * s₁, ht₁⟩ (t₂ • r₂) ⟨t₂ * s₂, ht₂⟩}
    (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) : lift₂Expand P hP (r₁ /ₒ s₁) (r₂ /ₒ s₂) = P r₁ s₁ r₂ s₂ :=
  rfl

set_option backward.privateInPublic true in
@[to_additive]
/--
Definition of `smul'` / `smul'` 的定义

English:
abbreviation smul'
  signature: (r₁ : R) (s₁ : S) (r₂ : X) (s₂ : S)
  body: oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * s₁)

@[to_additive]

中文:
缩写 smul'
  签名: (r₁ : R) (s₁ : S) (r₂ : X) (s₂ : S)
  定义体: oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * s₁)

@[to_additive]
-/
private abbrev smul' (r₁ : R) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
  oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * s₁)

@[to_additive]
/--
theorem `smul'_char` / 定理 `smul'_char`

English:
theorem smul'_char
  given: (r₁ : R) (r₂ : X) (s₁ s₂ : S) (u : S) (v : R) (huv : u * r₁ = v * s₂)
  proof: by
  -- Porting note: `assoc_rw` was not ported yet
  simp only [smul']
  have h₀ := ore_eq r₁ s₂; set v₀ := oreNum r₁ s₂; set u₀ := oreDenom r₁ s₂
  rcases oreCondition (u₀ : R) u with ⟨r₃, s₃, h₃⟩
  have :=
    calc
      r₃ * v * s₂ = r₃ * (u * r₁) := by rw [mul_assoc, ← huv]
      _ = s₃ * (u₀ * r₁) := by rw [← mul_assoc, ← mul_assoc, h₃]
      _ = s₃ * v₀ * s₂ := by rw [mul_assoc, h₀]
  rcases ore_right_cancel _ _ _ this with ⟨s₄, hs₄⟩
  symm; rw [oreDiv_eq_iff]
  use s₄ * s₃
  use s₄ * r₃
  simp only [Submonoid.coe_mul, Submonoid.smul_def]
  constructor
  · rw [smul_smul, mul_assoc (c := v₀), ← hs₄]
    simp only [smul_smul, mul_assoc]
  · rw [← mul_assoc (b := (u₀ : R)), mul_assoc (c := (u₀ : R)), h₃]
    simp only [mul_assoc]

中文:
定理 smul'_char
  条件: (r₁ : R) (r₂ : X) (s₁ s₂ : S) (u : S) (v : R) (huv : u * r₁ = v * s₂)
  证明: by
  -- Porting note: `assoc_rw` was not ported yet
  simp only [smul']
  have h₀ := ore_eq r₁ s₂; set v₀ := oreNum r₁ s₂; set u₀ := oreDenom r₁ s₂
  rcases oreCondition (u₀ : R) u with ⟨r₃, s₃, h₃⟩
  have :=
    calc
      r₃ * v * s₂ = r₃ * (u * r₁) := by rw [mul_assoc, ← huv]
      _ = s₃ * (u₀ * r₁) := by rw [← mul_assoc, ← mul_assoc, h₃]
      _ = s₃ * v₀ * s₂ := by rw [mul_assoc, h₀]
  rcases ore_right_cancel _ _ _ this with ⟨s₄, hs₄⟩
  symm; rw [oreDiv_eq_iff]
  use s₄ * s₃
  use s₄ * r₃
  simp only [Submonoid.coe_mul, Submonoid.smul_def]
  constructor
  · rw [smul_smul, mul_assoc (c := v₀), ← hs₄]
    simp only [smul_smul, mul_assoc]
  · rw [← mul_assoc (b := (u₀ : R)), mul_assoc (c := (u₀ : R)), h₃]
    simp only [mul_assoc]
-/
private theorem smul'_char (r₁ : R) (r₂ : X) (s₁ s₂ : S) (u : S) (v : R) (huv : u * r₁ = v * s₂) :
    OreLocalization.smul' r₁ s₁ r₂ s₂ = v • r₂ /ₒ (u * s₁) := by
  -- Porting note: `assoc_rw` was not ported yet
  simp only [smul']
  have h₀ := ore_eq r₁ s₂; set v₀ := oreNum r₁ s₂; set u₀ := oreDenom r₁ s₂
  rcases oreCondition (u₀ : R) u with ⟨r₃, s₃, h₃⟩
  have :=
    calc
      r₃ * v * s₂ = r₃ * (u * r₁) := by rw [mul_assoc, ← huv]
      _ = s₃ * (u₀ * r₁) := by rw [← mul_assoc, ← mul_assoc, h₃]
      _ = s₃ * v₀ * s₂ := by rw [mul_assoc, h₀]
  rcases ore_right_cancel _ _ _ this with ⟨s₄, hs₄⟩
  symm; rw [oreDiv_eq_iff]
  use s₄ * s₃
  use s₄ * r₃
  simp only [Submonoid.coe_mul, Submonoid.smul_def]
  constructor
  · rw [smul_smul, mul_assoc (c := v₀), ← hs₄]
    simp only [smul_smul, mul_assoc]
  · rw [← mul_assoc (b := (u₀ : R)), mul_assoc (c := (u₀ : R)), h₃]
    simp only [mul_assoc]

set_option backward.privateInPublic true in
/-- The multiplication on the Ore localization of monoids. -/
@[to_additive]
/--
Definition of `smul''` / `smul''` 的定义

English:
abbreviation smul''
  signature: (r : R) (s : S)
  body: liftExpand (smul' r s) fun r₁ r₂ s' hs => by
    rcases oreCondition r s' with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition r ⟨_, hs⟩ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₁' : R) (s₂') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₁' * s' = (r₃' * r₂' * r₂) * s' := by
      rw [mul_assoc]; rw [← h₁]; rw [← mul_assoc]; rw [h₃]; rw [mul_assoc]; rw [h₂]
      simp [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₂' * s) in S := by
      rw [mul_assoc]; rw [← mul_assoc r₃']; rw [← h₃]
      exact (s₄' * (s₃' * s₁' * s)).2
    rw [OreLocalization.expand' _ _ (s₄' * s₃')]; rw [OreLocalization.expand _ (s₂' * s) _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc (s₄' : R)]; rw [h₃]; rw [← mul_assoc]

中文:
缩写 smul''
  签名: (r : R) (s : S)
  定义体: liftExpand (smul' r s) fun r₁ r₂ s' hs => by
    rcases oreCondition r s' with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition r ⟨_, hs⟩ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₁' : R) (s₂') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₁' * s' = (r₃' * r₂' * r₂) * s' := by
      rw [mul_assoc]; rw [← h₁]; rw [← mul_assoc]; rw [h₃]; rw [mul_assoc]; rw [h₂]
      simp [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₂' * s) in S := by
      rw [mul_assoc]; rw [← mul_assoc r₃']; rw [← h₃]
      exact (s₄' * (s₃' * s₁' * s)).2
    rw [OreLocalization.expand' _ _ (s₄' * s₃')]; rw [OreLocalization.expand _ (s₂' * s) _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc (s₄' : R)]; rw [h₃]; rw [← mul_assoc]
-/
private abbrev smul'' (r : R) (s : S) : X[S⁻¹] -> X[S⁻¹] :=
  liftExpand (smul' r s) fun r₁ r₂ s' hs => by
    rcases oreCondition r s' with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition r ⟨_, hs⟩ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₁' : R) (s₂') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₁' * s' = (r₃' * r₂' * r₂) * s' := by
      rw [mul_assoc]; rw [← h₁]; rw [← mul_assoc]; rw [h₃]; rw [mul_assoc]; rw [h₂]
      simp [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₂' * s) in S := by
      rw [mul_assoc]; rw [← mul_assoc r₃']; rw [← h₃]
      exact (s₄' * (s₃' * s₁' * s)).2
    rw [OreLocalization.expand' _ _ (s₄' * s₃')]; rw [OreLocalization.expand _ (s₂' * s) _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc (s₄' : R)]; rw [h₃]; rw [← mul_assoc]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The scalar multiplication on the Ore localization of monoids. -/
@[to_additive
  /-- the vector addition on the Ore localization of additive monoids. -/]
/--
Definition of `smul` / `smul` 的定义

English:
abbreviation smul
  signature: (y : R[S⁻¹]) (x : X[S⁻¹])
  body: liftExpand (smul'' · · x) (fun r₁ r₂ s hs => by
    cases x with | _ x s₂
    change OreLocalization.smul' r₁ s x s₂ = OreLocalization.smul' (r₂ * r₁) ⟨_, hs⟩ x s₂
    rcases oreCondition r₁ s₂ with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition (r₂ * r₁) s₂ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₂' * r₂) (s₁') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₂' * s₂ = r₃' * r₁' * s₂ := by
      rw [mul_assoc]; rw [← h₂]; rw [← mul_assoc _ r₂]; rw [← mul_assoc]; rw [h₃]; rw [mul_assoc]; rw [h₁]; rw [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₁' * s) in S := by
      rw [← mul_assoc]; rw [mul_assoc _ r₃']; rw [← h₃]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_assoc]
      exact mul_mem (s₄' * s₃' * s₂').2 hs
    rw [OreLocalization.expand' (r₂' • x) _ (s₄' * s₃')]; rw [OreLocalization.expand _ _ _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc _ r₃']; rw [← h₃]; rw [← mul_assoc]; rw [← mul_assoc]) y

@[to_additive]

中文:
缩写 smul
  签名: (y : R[S⁻¹]) (x : X[S⁻¹])
  定义体: liftExpand (smul'' · · x) (fun r₁ r₂ s hs => by
    cases x with | _ x s₂
    change OreLocalization.smul' r₁ s x s₂ = OreLocalization.smul' (r₂ * r₁) ⟨_, hs⟩ x s₂
    rcases oreCondition r₁ s₂ with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition (r₂ * r₁) s₂ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₂' * r₂) (s₁') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₂' * s₂ = r₃' * r₁' * s₂ := by
      rw [mul_assoc]; rw [← h₂]; rw [← mul_assoc _ r₂]; rw [← mul_assoc]; rw [h₃]; rw [mul_assoc]; rw [h₁]; rw [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₁' * s) in S := by
      rw [← mul_assoc]; rw [mul_assoc _ r₃']; rw [← h₃]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_assoc]
      exact mul_mem (s₄' * s₃' * s₂').2 hs
    rw [OreLocalization.expand' (r₂' • x) _ (s₄' * s₃')]; rw [OreLocalization.expand _ _ _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc _ r₃']; rw [← h₃]; rw [← mul_assoc]; rw [← mul_assoc]) y

@[to_additive]
-/
protected abbrev smul (y : R[S⁻¹]) (x : X[S⁻¹]) : X[S⁻¹] :=
  liftExpand (smul'' · · x) (fun r₁ r₂ s hs => by
    cases x with | _ x s₂
    change OreLocalization.smul' r₁ s x s₂ = OreLocalization.smul' (r₂ * r₁) ⟨_, hs⟩ x s₂
    rcases oreCondition r₁ s₂ with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition (r₂ * r₁) s₂ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₂' * r₂) (s₁') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₂' * s₂ = r₃' * r₁' * s₂ := by
      rw [mul_assoc]; rw [← h₂]; rw [← mul_assoc _ r₂]; rw [← mul_assoc]; rw [h₃]; rw [mul_assoc]; rw [h₁]; rw [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₁' * s) in S := by
      rw [← mul_assoc]; rw [mul_assoc _ r₃']; rw [← h₃]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_assoc]
      exact mul_mem (s₄' * s₃' * s₂').2 hs
    rw [OreLocalization.expand' (r₂' • x) _ (s₄' * s₃')]; rw [OreLocalization.expand _ _ _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc _ r₃']; rw [← h₃]; rw [← mul_assoc]; rw [← mul_assoc]) y

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R[S⁻¹] X[S⁻¹]
  body: ⟨OreLocalization.smul⟩

@[to_additive]

中文:
实例 :
  签名: 标量乘法 R[S⁻¹] X[S⁻¹]
  定义体: ⟨OreLocalization.smul⟩

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.smul
-/
instance : SMul R[S⁻¹] X[S⁻¹] :=
  ⟨OreLocalization.smul⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul R[S⁻¹]
  body: ⟨OreLocalization.smul⟩

@[to_additive]

中文:
实例 :
  签名: 乘法 R[S⁻¹]
  定义体: ⟨OreLocalization.smul⟩

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.smul
-/
instance : Mul R[S⁻¹] :=
  ⟨OreLocalization.smul⟩

@[to_additive]
/--
theorem `oreDiv_smul_oreDiv` / 定理 `oreDiv_smul_oreDiv`

English:
theorem oreDiv_smul_oreDiv
  given: {r₁ : R} {r₂ : X} {s₁ s₂ : S}
  proof: by
  with_unfolding_all rfl

@[to_additive]

中文:
定理 oreDiv_smul_oreDiv
  条件: {r₁ : R} {r₂ : X} {s₁ s₂ : S}
  证明: by
  with_unfolding_all rfl

@[to_additive]

Depends on / 依赖: with_unfolding_all
-/
theorem oreDiv_smul_oreDiv {r₁ : R} {r₂ : X} {s₁ s₂ : S} :
    (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * s₁) := by
  with_unfolding_all rfl

@[to_additive]
/--
theorem `oreDiv_mul_oreDiv` / 定理 `oreDiv_mul_oreDiv`

English:
theorem oreDiv_mul_oreDiv
  given: {r₁ : R} {r₂ : R} {s₁ s₂ : S}
  proof: by
  with_unfolding_all rfl

中文:
定理 oreDiv_mul_oreDiv
  条件: {r₁ : R} {r₂ : R} {s₁ s₂ : S}
  证明: by
  with_unfolding_all rfl

Depends on / 依赖: with_unfolding_all
-/
theorem oreDiv_mul_oreDiv {r₁ : R} {r₂ : R} {s₁ s₂ : S} :
    (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = oreNum r₁ s₂ * r₂ /ₒ (oreDenom r₁ s₂ * s₁) := by
  with_unfolding_all rfl

/-- A characterization lemma for the scalar multiplication on the Ore localization,
allowing for a choice of Ore numerator and Ore denominator. -/
@[to_additive /-- A characterization lemma for the vector addition on the Ore localization,
allowing for a choice of Ore minuend and Ore subtrahend. -/]
/--
theorem `oreDiv_smul_char` / 定理 `oreDiv_smul_char`

English:
theorem oreDiv_smul_char
  given: (r₁ : R) (r₂ : X) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂)
  proof: by
  with_unfolding_all exact smul'_char r₁ r₂ s₁ s₂ s' r' huv

中文:
定理 oreDiv_smul_char
  条件: (r₁ : R) (r₂ : X) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂)
  证明: by
  with_unfolding_all exact smul'_char r₁ r₂ s₁ s₂ s' r' huv

Depends on / 依赖: _char, with_unfolding_all
-/
theorem oreDiv_smul_char (r₁ : R) (r₂ : X) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂) :
    (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = r' • r₂ /ₒ (s' * s₁) := by
  with_unfolding_all exact smul'_char r₁ r₂ s₁ s₂ s' r' huv

/-- A characterization lemma for the multiplication on the Ore localization, allowing for a choice
of Ore numerator and Ore denominator. -/
@[to_additive /-- A characterization lemma for the addition on the Ore localization,
allowing for a choice of Ore minuend and Ore subtrahend. -/]
/--
theorem `oreDiv_mul_char` / 定理 `oreDiv_mul_char`

English:
theorem oreDiv_mul_char
  given: (r₁ r₂ : R) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂)
  proof: by
  with_unfolding_all exact smul'_char r₁ r₂ s₁ s₂ s' r' huv

中文:
定理 oreDiv_mul_char
  条件: (r₁ r₂ : R) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂)
  证明: by
  with_unfolding_all exact smul'_char r₁ r₂ s₁ s₂ s' r' huv

Depends on / 依赖: _char, with_unfolding_all
-/
theorem oreDiv_mul_char (r₁ r₂ : R) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂) :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r' * r₂ /ₒ (s' * s₁) := by
  with_unfolding_all exact smul'_char r₁ r₂ s₁ s₂ s' r' huv

/-- Another characterization lemma for the scalar multiplication on the Ore localization delivering
Ore witnesses and conditions bundled in a sigma type. -/
@[to_additive /-- Another characterization lemma for the vector addition on the
  Ore localization delivering Ore witnesses and conditions bundled in a sigma type. -/]
/--
Definition of `oreDivSMulChar'` / `oreDivSMulChar'` 的定义

English:
definition oreDivSMulChar'
  signature: (r₁ : R) (r₂ : X) (s₁ s₂ : S)
  body: ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_smul_oreDiv⟩

中文:
定义 oreDivSMulChar'
  签名: (r₁ : R) (r₂ : X) (s₁ s₂ : S)
  定义体: ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_smul_oreDiv⟩

Depends on / 依赖: oreDenom, oreDiv_smul_oreDiv, oreNum, ore_eq
-/
def oreDivSMulChar' (r₁ : R) (r₂ : X) (s₁ s₂ : S) :
    Σ' r' : R, Σ' s' : S, s' * r₁ = r' * s₂ ∧ (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = r' • r₂ /ₒ (s' * s₁) :=
  ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_smul_oreDiv⟩

/-- Another characterization lemma for the multiplication on the Ore localization delivering
Ore witnesses and conditions bundled in a sigma type. -/
@[to_additive /-- Another characterization lemma for the addition on the Ore localization delivering
  Ore witnesses and conditions bundled in a sigma type. -/]
/--
Definition of `oreDivMulChar'` / `oreDivMulChar'` 的定义

English:
definition oreDivMulChar'
  signature: (r₁ r₂ : R) (s₁ s₂ : S)
  body: ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_mul_oreDiv⟩

中文:
定义 oreDivMulChar'
  签名: (r₁ r₂ : R) (s₁ s₂ : S)
  定义体: ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_mul_oreDiv⟩

Depends on / 依赖: oreDenom, oreDiv_mul_oreDiv, oreNum, ore_eq
-/
def oreDivMulChar' (r₁ r₂ : R) (s₁ s₂ : S) :
    Σ' r' : R, Σ' s' : S, s' * r₁ = r' * s₂ ∧ r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r' * r₂ /ₒ (s' * s₁) :=
  ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_mul_oreDiv⟩

/-- `1` in the localization, defined as `1 /ₒ 1`. -/
@[to_additive (attr := irreducible) /-- `0` in the additive localization, defined as `0 -ₒ 0`. -/]
/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: [One X]
  body: 1 /ₒ 1

@[to_additive]

中文:
定义 one
  签名: [幺 X]
  定义体: 1 /ₒ 1

@[to_additive]
-/
protected def one [One X] : X[S⁻¹] := 1 /ₒ 1

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: X] : One X[S⁻¹]
  body: ⟨OreLocalization.one⟩

@[to_additive]

中文:
实例 [幺
  签名: X] : 幺 X[S⁻¹]
  定义体: ⟨OreLocalization.one⟩

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.one
-/
instance [One X] : One X[S⁻¹] :=
  ⟨OreLocalization.one⟩

@[to_additive]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  given: [One X]
  statement: (1 : X[S⁻¹]) = 1 /ₒ 1
  proof: by
  with_unfolding_all rfl

@[to_additive]

中文:
定理 one_def
  条件: [幺 X]
  结论: (1 : X[S⁻¹]) = 1 /ₒ 1
  证明: by
  with_unfolding_all rfl

@[to_additive]
-/
protected theorem one_def [One X] : (1 : X[S⁻¹]) = 1 /ₒ 1 := by
  with_unfolding_all rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited R[S⁻¹]
  body: ⟨1⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 可居 R[S⁻¹]
  定义体: ⟨1⟩

@[to_additive (attr := simp)]
-/
instance : Inhabited R[S⁻¹] :=
  ⟨1⟩

@[to_additive (attr := simp)]
/--
theorem `div_eq_one'` / 定理 `div_eq_one'`

English:
theorem div_eq_one'
  given: {r : R} (hr : r in S)
  statement: r /ₒ ⟨r, hr⟩ = 1
  proof: by
  rw [OreLocalization.one_def]; rw [oreDiv_eq_iff]
  exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩

@[to_additive (attr := simp)]

中文:
定理 div_eq_one'
  条件: {r : R} (hr : r in S)
  结论: r /ₒ ⟨r, hr⟩ = 1
  证明: by
  rw [OreLocalization.one_def]; rw [oreDiv_eq_iff]
  exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩

@[to_additive (attr := simp)]
-/
protected theorem div_eq_one' {r : R} (hr : r in S) : r /ₒ ⟨r, hr⟩ = 1 := by
  rw [OreLocalization.one_def]; rw [oreDiv_eq_iff]
  exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩

@[to_additive (attr := simp)]
/--
theorem `div_eq_one` / 定理 `div_eq_one`

English:
theorem div_eq_one
  given: {s : S}
  statement: (s : R) /ₒ s = 1
  proof: OreLocalization.div_eq_one' _

@[to_additive]

中文:
定理 div_eq_one
  条件: {s : S}
  结论: (s : R) /ₒ s = 1
  证明: OreLocalization.div_eq_one' _

@[to_additive]
-/
protected theorem div_eq_one {s : S} : (s : R) /ₒ s = 1 :=
  OreLocalization.div_eq_one' _

@[to_additive]
/--
theorem `one_smul` / 定理 `one_smul`

English:
theorem one_smul
  given: (x : X[S⁻¹])
  statement: (1 : R[S⁻¹]) • x = x
  proof: by
  cases x with | _ r s
  simp [OreLocalization.one_def, oreDiv_smul_char 1 r 1 s 1 s (by simp)]

@[to_additive]

中文:
定理 one_smul
  条件: (x : X[S⁻¹])
  结论: (1 : R[S⁻¹]) • x = x
  证明: by
  cases x with | _ r s
  simp [OreLocalization.one_def, oreDiv_smul_char 1 r 1 s 1 s (by simp)]

@[to_additive]
-/
protected theorem one_smul (x : X[S⁻¹]) : (1 : R[S⁻¹]) • x = x := by
  cases x with | _ r s
  simp [OreLocalization.one_def, oreDiv_smul_char 1 r 1 s 1 s (by simp)]

@[to_additive]
/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: (x : R[S⁻¹])
  statement: 1 * x = x
  proof: OreLocalization.one_smul x

@[to_additive]

中文:
定理 one_mul
  条件: (x : R[S⁻¹])
  结论: 1 * x = x
  证明: OreLocalization.one_smul x

@[to_additive]
-/
protected theorem one_mul (x : R[S⁻¹]) : 1 * x = x :=
  OreLocalization.one_smul x

@[to_additive]
/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  given: (x : R[S⁻¹])
  statement: x * 1 = x
  proof: by
  cases x with | _ r s
  simp [OreLocalization.one_def, oreDiv_mul_char r (1 : R) s (1 : S) r 1 (by simp)]

@[to_additive]

中文:
定理 mul_one
  条件: (x : R[S⁻¹])
  结论: x * 1 = x
  证明: by
  cases x with | _ r s
  simp [OreLocalization.one_def, oreDiv_mul_char r (1 : R) s (1 : S) r 1 (by simp)]

@[to_additive]
-/
protected theorem mul_one (x : R[S⁻¹]) : x * 1 = x := by
  cases x with | _ r s
  simp [OreLocalization.one_def, oreDiv_mul_char r (1 : R) s (1 : S) r 1 (by simp)]

@[to_additive]
/--
theorem `mul_smul` / 定理 `mul_smul`

English:
theorem mul_smul
  given: (x y : R[S⁻¹]) (z : X[S⁻¹])
  statement: (x * y) • z = x • y • z
  proof: by
  -- Porting note: `assoc_rw` was not ported yet
  cases x with | _ r₁ s₁
  cases y with | _ r₂ s₂
  cases z with | _ r₃ s₃
  rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivSMulChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  rcases oreCondition ra sb with ⟨rc, sc, hc⟩
  rw [oreDiv_smul_char (ra * r₂) r₃ (sa * s₁) s₃ (rc * rb) sc]; swap
  · rw [← mul_assoc _ ra, hc, mul_assoc, hb, ← mul_assoc]
  rw [← mul_assoc]; rw [mul_smul]
  symm; apply oreDiv_smul_char
  rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [← mul_assoc]; rw [← hc]; rw [mul_assoc _ ra]; rw [← ha]; rw [mul_assoc]

@[to_additive]

中文:
定理 mul_smul
  条件: (x y : R[S⁻¹]) (z : X[S⁻¹])
  结论: (x * y) • z = x • y • z
  证明: by
  -- Porting note: `assoc_rw` was not ported yet
  cases x with | _ r₁ s₁
  cases y with | _ r₂ s₂
  cases z with | _ r₃ s₃
  rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivSMulChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  rcases oreCondition ra sb with ⟨rc, sc, hc⟩
  rw [oreDiv_smul_char (ra * r₂) r₃ (sa * s₁) s₃ (rc * rb) sc]; swap
  · rw [← mul_assoc _ ra, hc, mul_assoc, hb, ← mul_assoc]
  rw [← mul_assoc]; rw [mul_smul]
  symm; apply oreDiv_smul_char
  rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [← mul_assoc]; rw [← hc]; rw [mul_assoc _ ra]; rw [← ha]; rw [mul_assoc]

@[to_additive]
-/
protected theorem mul_smul (x y : R[S⁻¹]) (z : X[S⁻¹]) : (x * y) • z = x • y • z := by
  -- Porting note: `assoc_rw` was not ported yet
  cases x with | _ r₁ s₁
  cases y with | _ r₂ s₂
  cases z with | _ r₃ s₃
  rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivSMulChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  rcases oreCondition ra sb with ⟨rc, sc, hc⟩
  rw [oreDiv_smul_char (ra * r₂) r₃ (sa * s₁) s₃ (rc * rb) sc]; swap
  · rw [← mul_assoc _ ra, hc, mul_assoc, hb, ← mul_assoc]
  rw [← mul_assoc]; rw [mul_smul]
  symm; apply oreDiv_smul_char
  rw [Submonoid.coe_mul]; rw [Submonoid.coe_mul]; rw [← mul_assoc]; rw [← hc]; rw [mul_assoc _ ra]; rw [← ha]; rw [mul_assoc]

@[to_additive]
/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: (x y z : R[S⁻¹])
  statement: x * y * z = x * (y * z)
  proof: OreLocalization.mul_smul x y z

中文:
定理 mul_assoc
  条件: (x y z : R[S⁻¹])
  结论: x * y * z = x * (y * z)
  证明: OreLocalization.mul_smul x y z
-/
protected theorem mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) :=
  OreLocalization.mul_smul x y z

/-- `npow` of `OreLocalization` -/
@[to_additive /-- `nsmul` of `AddOreLocalization` -/]
/--
Definition of `npow` / `npow` 的定义

English:
abbreviation npow
  signature: : Nat -> R[S⁻¹] -> R[S⁻¹]
  body: npowRec

@[to_additive]

中文:
缩写 npow
  签名: : 自然数 -> R[S⁻¹] -> R[S⁻¹]
  定义体: npowRec

@[to_additive]
-/
protected abbrev npow : Nat -> R[S⁻¹] -> R[S⁻¹] := npowRec

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid R[S⁻¹]
  body: OreLocalization.one_mul
  mul_one := OreLocalization.mul_one
  mul_assoc := OreLocalization.mul_assoc
  npow := OreLocalization.npow

@[to_additive]

中文:
实例 :
  签名: 幺半群 R[S⁻¹]
  定义体: OreLocalization.one_mul
  mul_one := OreLocalization.mul_one
  mul_assoc := OreLocalization.mul_assoc
  npow := OreLocalization.npow

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.one_mul, one_mul
-/
instance : Monoid R[S⁻¹] where
  one_mul := OreLocalization.one_mul
  mul_one := OreLocalization.mul_one
  mul_assoc := OreLocalization.mul_assoc
  npow := OreLocalization.npow

@[to_additive]
/--
theorem `oreDiv_pow` / 定理 `oreDiv_pow`

English:
theorem oreDiv_pow
  given: (r : R) (s : S) (n : Nat) (h : Commute r (s : R))
  proof: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [pow_zero]; rw [OreLocalization.one_def]
  | succ n ih =>
    rw [pow_succ']; rw [pow_succ']; rw [pow_succ]; rw [ih]; rw [oreDiv_mul_char (r' := r) (s' := s ^ n)]
.symm exact h.pow_right _

@[to_additive]

中文:
定理 oreDiv_pow
  条件: (r : R) (s : S) (n : 自然数) (h : Commute r (s : R))
  证明: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [pow_zero]; rw [OreLocalization.one_def]
  | succ n ih =>
    rw [pow_succ']; rw [pow_succ']; rw [pow_succ]; rw [ih]; rw [oreDiv_mul_char (r' := r) (s' := s ^ n)]
.symm exact h.pow_right _

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.one_def, h.pow_right, one_def, oreDiv_mul_char, pow_right, pow_succ, pow_zero
-/
theorem oreDiv_pow (r : R) (s : S) (n : Nat) (h : Commute r (s : R)) :
    (r /ₒ s) ^ n = (r ^ n) /ₒ (s ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [pow_zero]; rw [OreLocalization.one_def]
  | succ n ih =>
    rw [pow_succ']; rw [pow_succ']; rw [pow_succ]; rw [ih]; rw [oreDiv_mul_char (r' := r) (s' := s ^ n)]
.symm exact h.pow_right _

@[to_additive]
/--
Instance `instMulActionOreLocalization` / 实例 `instMulActionOreLocalization`

English:
instance instMulActionOreLocalization
  signature: : MulAction R[S⁻¹] X[S⁻¹] where
  body: OreLocalization.one_smul
  mul_smul := OreLocalization.mul_smul

@[to_additive]

中文:
实例 instMulActionOreLocalization
  签名: : 乘法作用 R[S⁻¹] X[S⁻¹] where
  定义体: OreLocalization.one_smul
  mul_smul := OreLocalization.mul_smul

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.one_smul, one_smul
-/
instance instMulActionOreLocalization : MulAction R[S⁻¹] X[S⁻¹] where
  one_smul := OreLocalization.one_smul
  mul_smul := OreLocalization.mul_smul

@[to_additive]
/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  given: (s s' : S)
  statement: ((s : R) /ₒ s') * ((s' : R) /ₒ s) = 1
  proof: by
  simp [oreDiv_mul_char (s : R) s' s' s 1 1 (by simp)]

@[to_additive (attr := simp)]

中文:
定理 mul_inv
  条件: (s s' : S)
  结论: ((s : R) /ₒ s') * ((s' : R) /ₒ s) = 1
  证明: by
  simp [oreDiv_mul_char (s : R) s' s' s 1 1 (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem mul_inv (s s' : S) : ((s : R) /ₒ s') * ((s' : R) /ₒ s) = 1 := by
  simp [oreDiv_mul_char (s : R) s' s' s 1 1 (by simp)]

@[to_additive (attr := simp)]
/--
theorem `one_div_smul` / 定理 `one_div_smul`

English:
theorem one_div_smul
  given: {r : X} {s t : S}
  statement: ((1 : R) /ₒ t) • (r /ₒ s) = r /ₒ (s * t)
  proof: by
  simp [oreDiv_smul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]

中文:
定理 one_div_smul
  条件: {r : X} {s t : S}
  结论: ((1 : R) /ₒ t) • (r /ₒ s) = r /ₒ (s * t)
  证明: by
  simp [oreDiv_smul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem one_div_smul {r : X} {s t : S} : ((1 : R) /ₒ t) • (r /ₒ s) = r /ₒ (s * t) := by
  simp [oreDiv_smul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]
/--
theorem `one_div_mul` / 定理 `one_div_mul`

English:
theorem one_div_mul
  given: {r : R} {s t : S}
  statement: (1 /ₒ t) * (r /ₒ s) = r /ₒ (s * t)
  proof: by
  simp [oreDiv_mul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]

中文:
定理 one_div_mul
  条件: {r : R} {s t : S}
  结论: (1 /ₒ t) * (r /ₒ s) = r /ₒ (s * t)
  证明: by
  simp [oreDiv_mul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem one_div_mul {r : R} {s t : S} : (1 /ₒ t) * (r /ₒ s) = r /ₒ (s * t) := by
  simp [oreDiv_mul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]
/--
theorem `smul_cancel` / 定理 `smul_cancel`

English:
theorem smul_cancel
  given: {r : X} {s t : S}
  statement: ((s : R) /ₒ t) • (r /ₒ s) = r /ₒ t
  proof: by
  simp [oreDiv_smul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]

中文:
定理 smul_cancel
  条件: {r : X} {s t : S}
  结论: ((s : R) /ₒ t) • (r /ₒ s) = r /ₒ t
  证明: by
  simp [oreDiv_smul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem smul_cancel {r : X} {s t : S} : ((s : R) /ₒ t) • (r /ₒ s) = r /ₒ t := by
  simp [oreDiv_smul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]
/--
theorem `mul_cancel` / 定理 `mul_cancel`

English:
theorem mul_cancel
  given: {r : R} {s t : S}
  statement: ((s : R) /ₒ t) * (r /ₒ s) = r /ₒ t
  proof: by
  simp [oreDiv_mul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]

中文:
定理 mul_cancel
  条件: {r : R} {s t : S}
  结论: ((s : R) /ₒ t) * (r /ₒ s) = r /ₒ t
  证明: by
  simp [oreDiv_mul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem mul_cancel {r : R} {s t : S} : ((s : R) /ₒ t) * (r /ₒ s) = r /ₒ t := by
  simp [oreDiv_mul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]
/--
theorem `smul_cancel'` / 定理 `smul_cancel'`

English:
theorem smul_cancel'
  given: {r₁ : R} {r₂ : X} {s t : S}
  proof: by
  simp [oreDiv_smul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]

中文:
定理 smul_cancel'
  条件: {r₁ : R} {r₂ : X} {s t : S}
  证明: by
  simp [oreDiv_smul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem smul_cancel' {r₁ : R} {r₂ : X} {s t : S} :
    ((r₁ * s) /ₒ t) • (r₂ /ₒ s) = (r₁ • r₂) /ₒ t := by
  simp [oreDiv_smul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]
/--
theorem `mul_cancel'` / 定理 `mul_cancel'`

English:
theorem mul_cancel'
  given: {r₁ r₂ : R} {s t : S}
  proof: by
  simp [oreDiv_mul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]

中文:
定理 mul_cancel'
  条件: {r₁ r₂ : R} {s t : S}
  证明: by
  simp [oreDiv_mul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]
-/
protected theorem mul_cancel' {r₁ r₂ : R} {s t : S} :
    ((r₁ * s) /ₒ t) * (r₂ /ₒ s) = (r₁ * r₂) /ₒ t := by
  simp [oreDiv_mul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]
/--
theorem `smul_div_one` / 定理 `smul_div_one`

English:
theorem smul_div_one
  given: {p : R} {r : X} {s : S}
  statement: (p /ₒ s) • (r /ₒ 1) = (p • r) /ₒ s
  proof: by
  simp [oreDiv_smul_char p r s 1 p 1 (by simp)]

@[to_additive (attr := simp)]

中文:
定理 smul_div_one
  条件: {p : R} {r : X} {s : S}
  结论: (p /ₒ s) • (r /ₒ 1) = (p • r) /ₒ s
  证明: by
  simp [oreDiv_smul_char p r s 1 p 1 (by simp)]

@[to_additive (attr := simp)]

Depends on / 依赖: oreDiv_smul_char
-/
theorem smul_div_one {p : R} {r : X} {s : S} : (p /ₒ s) • (r /ₒ 1) = (p • r) /ₒ s := by
  simp [oreDiv_smul_char p r s 1 p 1 (by simp)]

@[to_additive (attr := simp)]
/--
theorem `mul_div_one` / 定理 `mul_div_one`

English:
theorem mul_div_one
  given: {p r : R} {s : S}
  statement: (p /ₒ s) * (r /ₒ 1) = (p * r) /ₒ s
  proof: by
  --TODO use coercion r ↦ r /ₒ 1
  simp [oreDiv_mul_char p r s 1 p 1 (by simp)]

中文:
定理 mul_div_one
  条件: {p r : R} {s : S}
  结论: (p /ₒ s) * (r /ₒ 1) = (p * r) /ₒ s
  证明: by
  --TODO use coercion r ↦ r /ₒ 1
  simp [oreDiv_mul_char p r s 1 p 1 (by simp)]
-/
theorem mul_div_one {p r : R} {s : S} : (p /ₒ s) * (r /ₒ 1) = (p * r) /ₒ s := by
  --TODO use coercion r ↦ r /ₒ 1
  simp [oreDiv_mul_char p r s 1 p 1 (by simp)]

/-- The fraction `s /ₒ 1` as a unit in `R[S⁻¹]`, where `s : S`. -/
@[to_additive /-- The difference `s -ₒ 0` as an additive unit. -/]
/--
Definition of `numeratorUnit` / `numeratorUnit` 的定义

English:
definition numeratorUnit
  signature: (s : S)
  body: (s : R) /ₒ 1
  inv := (1 : R) /ₒ s
  val_inv := OreLocalization.mul_inv s 1
  inv_val := OreLocalization.mul_inv 1 s

中文:
定义 numeratorUnit
  签名: (s : S)
  定义体: (s : R) /ₒ 1
  inv := (1 : R) /ₒ s
  val_inv := OreLocalization.mul_inv s 1
  inv_val := OreLocalization.mul_inv 1 s
-/
def numeratorUnit (s : S) : Units R[S⁻¹] where
  val := (s : R) /ₒ 1
  inv := (1 : R) /ₒ s
  val_inv := OreLocalization.mul_inv s 1
  inv_val := OreLocalization.mul_inv 1 s

/-- The multiplicative homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the
fraction `r /ₒ 1`. -/
@[to_additive /-- The additive homomorphism from `R` to `AddOreLocalization R S`,
  mapping `r : R` to the difference `r -ₒ 0`. -/]
/--
Definition of `numeratorHom` / `numeratorHom` 的定义

English:
abbreviation numeratorHom
  signature: : R ->* R[S⁻¹] where
  body: r /ₒ 1
  map_one' := by with_unfolding_all rfl
  map_mul' _ _ := mul_div_one.symm

@[to_additive]

中文:
缩写 numeratorHom
  签名: : R ->* R[S⁻¹] where
  定义体: r /ₒ 1
  map_one' := by with_unfolding_all rfl
  map_mul' _ _ := mul_div_one.symm

@[to_additive]
-/
abbrev numeratorHom : R ->* R[S⁻¹] where
  toFun r := r /ₒ 1
  map_one' := by with_unfolding_all rfl
  map_mul' _ _ := mul_div_one.symm

@[to_additive]
/--
theorem `numeratorHom_apply` / 定理 `numeratorHom_apply`

English:
theorem numeratorHom_apply
  given: {r : R}
  statement: numeratorHom r = r /ₒ (1 : S)
  proof: rfl

@[to_additive]

中文:
定理 numeratorHom_apply
  条件: {r : R}
  结论: numeratorHom r = r /ₒ (1 : S)
  证明: rfl

@[to_additive]
-/
theorem numeratorHom_apply {r : R} : numeratorHom r = r /ₒ (1 : S) :=
  rfl

@[to_additive]
/--
theorem `numerator_isUnit` / 定理 `numerator_isUnit`

English:
theorem numerator_isUnit
  given: (s : S)
  statement: IsUnit (numeratorHom (s : R) : R[S⁻¹])
  proof: ⟨numeratorUnit s, rfl⟩

中文:
定理 numerator_isUnit
  条件: (s : S)
  结论: 是单位 (numeratorHom (s : R) : R[S⁻¹])
  证明: ⟨numeratorUnit s, rfl⟩

Depends on / 依赖: numeratorUnit
-/
theorem numerator_isUnit (s : S) : IsUnit (numeratorHom (s : R) : R[S⁻¹]) :=
  ⟨numeratorUnit s, rfl⟩

section UMP

variable {T : Type*} [Monoid T]
variable (f : R ->* T) (fS : S ->* Units T)

/-- The universal lift from a morphism `R →* T`, which maps elements of `S` to units of `T`,
to a morphism `R[S⁻¹] →* T`. -/
@[to_additive /-- The universal lift from a morphism `R →+ T`, which maps elements of `S` to
  additive-units of `T`, to a morphism `AddOreLocalization R S →+ T`. -/]
/--
Definition of `universalMulHom` / `universalMulHom` 的定义

English:
definition universalMulHom
  signature: (hf : forall s : S, f s = fS s)
  body: x.liftExpand (fun r s => ((fS s)⁻¹ : Units T) * f r) fun r t s ht => by
      simp only [smul_eq_mul]
      have : (fS ⟨t * s, ht⟩ : T) = f t * fS s := by
        simp only [← hf, map_mul]
      conv_rhs =>
        rw [map_mul]; rw [← one_mul (f r)]; rw [← Units.val_one]; rw [← mul_inv_cancel (fS s)]
        rw [Units.val_mul]; rw [mul_assoc]; rw [← mul_assoc _ (fS s : T)]; rw [← this]; rw [← mul_assoc]
      simp only [one_mul, Units.inv_mul]
  map_one' := by rw [OreLocalization.one_def, liftExpand_of]; simp
  map_mul' x y := by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
    rw [liftExpand_of]; rw [liftExpand_of]; rw [liftExpand_of]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [map_mul]; rw [map_mul]; rw [Units.val_mul]; rw [mul_assoc]; rw [← mul_assoc (fS s₁ : T)]; rw [← mul_assoc (fS s₁ : T)]; rw [Units.mul_inv]; rw [one_mul]; rw [← hf]; rw [← mul_assoc]; rw [← map_mul _ _ r₁]; rw [ha]; rw [map_mul]; rw [hf s₂]; rw [mul_assoc]; rw [← mul_assoc (fS s₂ : T)]; rw [(fS s₂).mul_inv]; rw [one_mul]

中文:
定义 universalMulHom
  签名: (hf : 对任意 s : S, f s = fS s)
  定义体: x.liftExpand (fun r s => ((fS s)⁻¹ : Units T) * f r) fun r t s ht => by
      simp only [smul_eq_mul]
      have : (fS ⟨t * s, ht⟩ : T) = f t * fS s := by
        simp only [← hf, map_mul]
      conv_rhs =>
        rw [map_mul]; rw [← one_mul (f r)]; rw [← Units.val_one]; rw [← mul_inv_cancel (fS s)]
        rw [Units.val_mul]; rw [mul_assoc]; rw [← mul_assoc _ (fS s : T)]; rw [← this]; rw [← mul_assoc]
      simp only [one_mul, Units.inv_mul]
  map_one' := by rw [OreLocalization.one_def, liftExpand_of]; simp
  map_mul' x y := by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
    rw [liftExpand_of]; rw [liftExpand_of]; rw [liftExpand_of]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [map_mul]; rw [map_mul]; rw [Units.val_mul]; rw [mul_assoc]; rw [← mul_assoc (fS s₁ : T)]; rw [← mul_assoc (fS s₁ : T)]; rw [Units.mul_inv]; rw [one_mul]; rw [← hf]; rw [← mul_assoc]; rw [← map_mul _ _ r₁]; rw [ha]; rw [map_mul]; rw [hf s₂]; rw [mul_assoc]; rw [← mul_assoc (fS s₂ : T)]; rw [(fS s₂).mul_inv]; rw [one_mul]

Depends on / 依赖: OreLocalization, OreLocalization.one_def, Units.inv_mul, Units.val_mul, Units.val_one, conv_rhs, inv_mul, liftExpand, liftExpand_of, map_mul, map_one, mul_assoc, mul_inv_cancel, one_def, one_mul, smul_eq_mul, val_mul, val_one, x.liftExpand
-/
def universalMulHom (hf : forall s : S, f s = fS s) : R[S⁻¹] ->* T where
  toFun x :=
    x.liftExpand (fun r s => ((fS s)⁻¹ : Units T) * f r) fun r t s ht => by
      simp only [smul_eq_mul]
      have : (fS ⟨t * s, ht⟩ : T) = f t * fS s := by
        simp only [← hf, map_mul]
      conv_rhs =>
        rw [map_mul]; rw [← one_mul (f r)]; rw [← Units.val_one]; rw [← mul_inv_cancel (fS s)]
        rw [Units.val_mul]; rw [mul_assoc]; rw [← mul_assoc _ (fS s : T)]; rw [← this]; rw [← mul_assoc]
      simp only [one_mul, Units.inv_mul]
  map_one' := by rw [OreLocalization.one_def, liftExpand_of]; simp
  map_mul' x y := by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
    rw [liftExpand_of]; rw [liftExpand_of]; rw [liftExpand_of]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [map_mul]; rw [map_mul]; rw [Units.val_mul]; rw [mul_assoc]; rw [← mul_assoc (fS s₁ : T)]; rw [← mul_assoc (fS s₁ : T)]; rw [Units.mul_inv]; rw [one_mul]; rw [← hf]; rw [← mul_assoc]; rw [← map_mul _ _ r₁]; rw [ha]; rw [map_mul]; rw [hf s₂]; rw [mul_assoc]; rw [← mul_assoc (fS s₂ : T)]; rw [(fS s₂).mul_inv]; rw [one_mul]

variable (hf : forall s : S, f s = fS s)

@[to_additive]
/--
theorem `universalMulHom_apply` / 定理 `universalMulHom_apply`

English:
theorem universalMulHom_apply
  given: {r : R} {s : S}
  proof: rfl

@[to_additive]

中文:
定理 universalMulHom_apply
  条件: {r : R} {s : S}
  证明: rfl

@[to_additive]
-/
theorem universalMulHom_apply {r : R} {s : S} :
    universalMulHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Units T) * f r :=
  rfl

@[to_additive]
/--
theorem `universalMulHom_commutes` / 定理 `universalMulHom_commutes`

English:
theorem universalMulHom_commutes
  given: {r : R}
  statement: universalMulHom f fS hf (numeratorHom r) = f r
  proof: by
  simp [numeratorHom_apply, universalMulHom_apply]

中文:
定理 universalMulHom_commutes
  条件: {r : R}
  结论: universalMulHom f fS hf (numeratorHom r) = f r
  证明: by
  simp [numeratorHom_apply, universalMulHom_apply]

Depends on / 依赖: numeratorHom_apply, universalMulHom_apply
-/
theorem universalMulHom_commutes {r : R} : universalMulHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalMulHom_apply]

/-- The universal morphism `universalMulHom` is unique. -/
@[to_additive /-- The universal morphism `universalAddHom` is unique. -/]
/--
theorem `universalMulHom_unique` / 定理 `universalMulHom_unique`

English:
theorem universalMulHom_unique
  given: (φ : R[S⁻¹] ->* T) (huniv : forall r : R, φ (numeratorHom r) = f r)
  proof: by
  ext x; cases x with | _ r s
  rw [universalMulHom_apply]; rw [← huniv r]; rw [numeratorHom_apply]; rw [← one_mul (φ (r /ₒ s))]; rw [←
    Units.val_one]; rw [← inv_mul_cancel (fS s)]; rw [Units.val_mul]; rw [mul_assoc]; rw [← hf]; rw [← huniv]; rw [← φ.map_mul]; rw [numeratorHom_apply]; rw [OreLocalization.mul_cancel]

中文:
定理 universalMulHom_unique
  条件: (φ : R[S⁻¹] ->* T) (huniv : 对任意 r : R, φ (numeratorHom r) = f r)
  证明: by
  ext x; cases x with | _ r s
  rw [universalMulHom_apply]; rw [← huniv r]; rw [numeratorHom_apply]; rw [← one_mul (φ (r /ₒ s))]; rw [←
    Units.val_one]; rw [← inv_mul_cancel (fS s)]; rw [Units.val_mul]; rw [mul_assoc]; rw [← hf]; rw [← huniv]; rw [← φ.map_mul]; rw [numeratorHom_apply]; rw [OreLocalization.mul_cancel]

Depends on / 依赖: OreLocalization, OreLocalization.mul_cancel, Units.val_mul, Units.val_one, inv_mul_cancel, map_mul, mul_assoc, mul_cancel, numeratorHom_apply, one_mul, universalMulHom_apply, val_mul, val_one
-/
theorem universalMulHom_unique (φ : R[S⁻¹] ->* T) (huniv : forall r : R, φ (numeratorHom r) = f r) :
    φ = universalMulHom f fS hf := by
  ext x; cases x with | _ r s
  rw [universalMulHom_apply]; rw [← huniv r]; rw [numeratorHom_apply]; rw [← one_mul (φ (r /ₒ s))]; rw [←
    Units.val_one]; rw [← inv_mul_cancel (fS s)]; rw [Units.val_mul]; rw [mul_assoc]; rw [← hf]; rw [← huniv]; rw [← φ.map_mul]; rw [numeratorHom_apply]; rw [OreLocalization.mul_cancel]

end UMP

end Monoid

section SMul

variable {R R' M X : Type*} [Monoid M] {S : Submonoid M} [OreSet S] [MulAction M X]
variable [SMul R X] [SMul R M] [IsScalarTower R M M] [IsScalarTower R M X]
variable [SMul R' X] [SMul R' M] [IsScalarTower R' M M] [IsScalarTower R' M X]
variable [SMul R R'] [IsScalarTower R R' M]

/-- Scalar multiplication in a monoid localization. -/
@[to_additive (attr := irreducible) /-- Vector addition in an additive monoid localization. -/]
/--
Definition of `hsmul` / `hsmul` 的定义

English:
definition hsmul
  signature: (c : R)
  body: liftExpand (fun m s => oreNum (c • 1) s • m /ₒ oreDenom (c • 1) s) (fun r t s ht => by
    rw [← mul_one (oreDenom (c • 1) s)]; rw [← oreDiv_smul_oreDiv]; rw [← mul_one (oreDenom (c • 1) _)]; rw [← oreDiv_smul_oreDiv]; rw [← OreLocalization.expand])

中文:
定义 hsmul
  签名: (c : R)
  定义体: liftExpand (fun m s => oreNum (c • 1) s • m /ₒ oreDenom (c • 1) s) (fun r t s ht => by
    rw [← mul_one (oreDenom (c • 1) s)]; rw [← oreDiv_smul_oreDiv]; rw [← mul_one (oreDenom (c • 1) _)]; rw [← oreDiv_smul_oreDiv]; rw [← OreLocalization.expand])
-/
protected def hsmul (c : R) :
    X[S⁻¹] -> X[S⁻¹] :=
  liftExpand (fun m s => oreNum (c • 1) s • m /ₒ oreDenom (c • 1) s) (fun r t s ht => by
    rw [← mul_one (oreDenom (c • 1) s)]; rw [← oreDiv_smul_oreDiv]; rw [← mul_one (oreDenom (c • 1) _)]; rw [← oreDiv_smul_oreDiv]; rw [← OreLocalization.expand])

set_option linter.overlappingInstances false in
/-- Warning: This gives a diamond on `SMul R[S⁻¹] M[S⁻¹][S⁻¹]`, but we will almost never localize
at the same monoid twice. -/
/- Although the definition does not require `IsScalarTower R M X`,
it does not make sense without it. -/
@[to_additive (attr := nolint unusedArguments)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsScalarTower
  signature: R M X] [IsScalarTower R M M] : SMul R (X[S⁻¹]) where
  body: OreLocalization.hsmul

@[to_additive]

中文:
实例 [标量塔
  签名: R M X] [标量塔 R M M] : 标量乘法 R (X[S⁻¹]) where
  定义体: OreLocalization.hsmul

@[to_additive]

Depends on / 依赖: OreLocalization, OreLocalization.hsmul
-/
instance [IsScalarTower R M X] [IsScalarTower R M M] : SMul R (X[S⁻¹]) where
  smul := OreLocalization.hsmul

@[to_additive]
/--
theorem `smul_oreDiv` / 定理 `smul_oreDiv`

English:
theorem smul_oreDiv
  given: (r : R) (x : X) (s : S)
  proof: by with_unfolding_all rfl

@[to_additive (attr := simp)]

中文:
定理 smul_oreDiv
  条件: (r : R) (x : X) (s : S)
  证明: by with_unfolding_all rfl

@[to_additive (attr := simp)]

Depends on / 依赖: with_unfolding_all
-/
theorem smul_oreDiv (r : R) (x : X) (s : S) :
    r • (x /ₒ s) = oreNum (r • 1) s • x /ₒ oreDenom (r • 1) s := by with_unfolding_all rfl

@[to_additive (attr := simp)]
/--
theorem `oreDiv_one_smul` / 定理 `oreDiv_one_smul`

English:
theorem oreDiv_one_smul
  given: (r : M) (x : X[S⁻¹])
  statement: (r /ₒ (1 : S)) • x = r • x
  proof: by
  cases x
  rw [smul_oreDiv]; rw [oreDiv_smul_oreDiv]; rw [mul_one]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive]

中文:
定理 oreDiv_one_smul
  条件: (r : M) (x : X[S⁻¹])
  结论: (r /ₒ (1 : S)) • x = r • x
  证明: by
  cases x
  rw [smul_oreDiv]; rw [oreDiv_smul_oreDiv]; rw [mul_one]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive]

Depends on / 依赖: mul_one, oreDiv_smul_oreDiv, smul_eq_mul, smul_oreDiv
-/
theorem oreDiv_one_smul (r : M) (x : X[S⁻¹]) : (r /ₒ (1 : S)) • x = r • x := by
  cases x
  rw [smul_oreDiv]; rw [oreDiv_smul_oreDiv]; rw [mul_one]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive]
/--
theorem `smul_one_smul` / 定理 `smul_one_smul`

English:
theorem smul_one_smul
  given: (r : R) (x : X[S⁻¹])
  statement: (r • 1 : M) • x = r • x
  proof: by
  cases x
  simp only [smul_oreDiv, smul_eq_mul, mul_one]

@[to_additive]

中文:
定理 smul_one_smul
  条件: (r : R) (x : X[S⁻¹])
  结论: (r • 1 : M) • x = r • x
  证明: by
  cases x
  simp only [smul_oreDiv, smul_eq_mul, mul_one]

@[to_additive]

Depends on / 依赖: mul_one, smul_eq_mul, smul_oreDiv
-/
theorem smul_one_smul (r : R) (x : X[S⁻¹]) : (r • 1 : M) • x = r • x := by
  cases x
  simp only [smul_oreDiv, smul_eq_mul, mul_one]

@[to_additive]
/--
theorem `smul_one_oreDiv_one_smul` / 定理 `smul_one_oreDiv_one_smul`

English:
theorem smul_one_oreDiv_one_smul
  given: (r : R) (x : X[S⁻¹])
  proof: by
  rw [oreDiv_one_smul]; rw [smul_one_smul]

@[to_additive]

中文:
定理 smul_one_oreDiv_one_smul
  条件: (r : R) (x : X[S⁻¹])
  证明: by
  rw [oreDiv_one_smul]; rw [smul_one_smul]

@[to_additive]

Depends on / 依赖: oreDiv_one_smul, smul_one_smul
-/
theorem smul_one_oreDiv_one_smul (r : R) (x : X[S⁻¹]) :
    ((r • 1 : M) /ₒ (1 : S)) • x = r • x := by
  rw [oreDiv_one_smul]; rw [smul_one_smul]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R R' X[S⁻¹]
  body: by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← mul_smul]; rw [mul_div_one]
    simp only [smul_mul_assoc, smul_assoc, one_mul]

@[to_additive]

中文:
实例 :
  签名: 标量塔 R R' X[S⁻¹]
  定义体: by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← mul_smul]; rw [mul_div_one]
    simp only [smul_mul_assoc, smul_assoc, one_mul]

@[to_additive]

Depends on / 依赖: mul_div_one, mul_smul, one_mul, smul_assoc, smul_mul_assoc, smul_one_oreDiv_one_smul
-/
instance : IsScalarTower R R' X[S⁻¹] where
  smul_assoc r m x := by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← mul_smul]; rw [mul_div_one]
    simp only [smul_mul_assoc, smul_assoc, one_mul]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R R' M] : SMulCommClass R R' X[S⁻¹] where
  body: by
    rw [← smul_one_smul m]; rw [← smul_assoc]; rw [smul_comm]; rw [smul_assoc]; rw [smul_one_smul]

@[to_additive]

中文:
实例 [标量交换类
  签名: R R' M] : 标量交换类 R R' X[S⁻¹] where
  定义体: by
    rw [← smul_one_smul m]; rw [← smul_assoc]; rw [smul_comm]; rw [smul_assoc]; rw [smul_one_smul]

@[to_additive]

Depends on / 依赖: smul_assoc, smul_comm, smul_one_smul
-/
instance [SMulCommClass R R' M] : SMulCommClass R R' X[S⁻¹] where
  smul_comm r m x := by
    rw [← smul_one_smul m]; rw [← smul_assoc]; rw [smul_comm]; rw [smul_assoc]; rw [smul_one_smul]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R M[S⁻¹] X[S⁻¹]
  body: by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← mul_smul]; rw [smul_eq_mul]

@[to_additive]

中文:
实例 :
  签名: 标量塔 R M[S⁻¹] X[S⁻¹]
  定义体: by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← mul_smul]; rw [smul_eq_mul]

@[to_additive]

Depends on / 依赖: mul_smul, smul_eq_mul, smul_one_oreDiv_one_smul
-/
instance : IsScalarTower R M[S⁻¹] X[S⁻¹] where
  smul_assoc r m x := by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [← mul_smul]; rw [smul_eq_mul]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: R M M] : SMulCommClass R M[S⁻¹] X[S⁻¹] where
  body: by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [smul_smul]; rw [smul_smul]; rw [mul_div_one]; rw [oreDiv_mul_char _ _ _ _ (r • 1) s₁ (by simp)]; rw [mul_one]
    simp

@[to_additive]

中文:
实例 [标量交换类
  签名: R M M] : 标量交换类 R M[S⁻¹] X[S⁻¹] where
  定义体: by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [smul_smul]; rw [smul_smul]; rw [mul_div_one]; rw [oreDiv_mul_char _ _ _ _ (r • 1) s₁ (by simp)]; rw [mul_one]
    simp

@[to_additive]

Depends on / 依赖: mul_div_one, mul_one, oreDiv_mul_char, smul_one_oreDiv_one_smul, smul_smul
-/
instance [SMulCommClass R M M] : SMulCommClass R M[S⁻¹] X[S⁻¹] where
  smul_comm r x y := by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [smul_smul]; rw [smul_smul]; rw [mul_div_one]; rw [oreDiv_mul_char _ _ _ _ (r • 1) s₁ (by simp)]; rw [mul_one]
    simp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: Rᵐᵒᵖ M] [SMul Rᵐᵒᵖ X] [IsScalarTower Rᵐᵒᵖ M M] [IsScalarTower Rᵐᵒᵖ M X]
  body: by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [op_smul_eq_smul]

@[to_additive]

中文:
实例 [标量乘法
  签名: Rᵐᵒᵖ M] [标量乘法 Rᵐᵒᵖ X] [标量塔 Rᵐᵒᵖ M M] [标量塔 Rᵐᵒᵖ M X]
  定义体: by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [op_smul_eq_smul]

@[to_additive]

Depends on / 依赖: op_smul_eq_smul, smul_one_oreDiv_one_smul
-/
instance [SMul Rᵐᵒᵖ M] [SMul Rᵐᵒᵖ X] [IsScalarTower Rᵐᵒᵖ M M] [IsScalarTower Rᵐᵒᵖ M X]
    [IsCentralScalar R M] : IsCentralScalar R X[S⁻¹] where
  op_smul_eq_smul r x := by
    rw [← smul_one_oreDiv_one_smul]; rw [← smul_one_oreDiv_one_smul]; rw [op_smul_eq_smul]

@[to_additive]
instance {R} [Monoid R] [MulAction R M] [IsScalarTower R M M]
    [MulAction R X] [IsScalarTower R M X] : MulAction R X[S⁻¹] where
  one_smul := OreLocalization.ind fun x s => by
    rw [← smul_one_oreDiv_one_smul]; rw [one_smul]; rw [← OreLocalization.one_def]; rw [one_smul]
  mul_smul s₁ s₂ x := by rw [← smul_eq_mul, smul_assoc]

@[to_additive]
/--
theorem `smul_oreDiv_one` / 定理 `smul_oreDiv_one`

English:
theorem smul_oreDiv_one
  given: (r : R) (x : X)
  statement: r • (x /ₒ (1 : S)) = (r • x) /ₒ (1 : S)
  proof: by
  rw [← smul_one_oreDiv_one_smul]; rw [smul_div_one]; rw [smul_assoc]; rw [one_smul]

中文:
定理 smul_oreDiv_one
  条件: (r : R) (x : X)
  结论: r • (x /ₒ (1 : S)) = (r • x) /ₒ (1 : S)
  证明: by
  rw [← smul_one_oreDiv_one_smul]; rw [smul_div_one]; rw [smul_assoc]; rw [one_smul]

Depends on / 依赖: one_smul, smul_assoc, smul_div_one, smul_one_oreDiv_one_smul
-/
theorem smul_oreDiv_one (r : R) (x : X) : r • (x /ₒ (1 : S)) = (r • x) /ₒ (1 : S) := by
  rw [← smul_one_oreDiv_one_smul]; rw [smul_div_one]; rw [smul_assoc]; rw [one_smul]

end SMul

section CommMonoid

variable {R : Type*} [CommMonoid R] {S : Submonoid R} [OreSet S]

@[to_additive]
/--
theorem `oreDiv_mul_oreDiv_comm` / 定理 `oreDiv_mul_oreDiv_comm`

English:
theorem oreDiv_mul_oreDiv_comm
  given: {r₁ r₂ : R} {s₁ s₂ : S}
  proof: by
  rw [oreDiv_mul_char r₁ r₂ s₁ s₂ r₁ s₂ (by simp [mul_comm]), mul_comm s₂]

@[to_additive]

中文:
定理 oreDiv_mul_oreDiv_comm
  条件: {r₁ r₂ : R} {s₁ s₂ : S}
  证明: by
  rw [oreDiv_mul_char r₁ r₂ s₁ s₂ r₁ s₂ (by simp [mul_comm]), mul_comm s₂]

@[to_additive]

Depends on / 依赖: mul_comm, oreDiv_mul_char
-/
theorem oreDiv_mul_oreDiv_comm {r₁ r₂ : R} {s₁ s₂ : S} :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₁ * r₂ /ₒ (s₁ * s₂) := by
  rw [oreDiv_mul_char r₁ r₂ s₁ s₂ r₁ s₂ (by simp [mul_comm]), mul_comm s₂]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid R[S⁻¹]
  body: fun x y => by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rw [oreDiv_mul_oreDiv_comm]; rw [oreDiv_mul_oreDiv_comm]; rw [mul_comm r₁]; rw [mul_comm s₁]

中文:
实例 :
  签名: 交换幺半群 R[S⁻¹]
  定义体: fun x y => by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rw [oreDiv_mul_oreDiv_comm]; rw [oreDiv_mul_oreDiv_comm]; rw [mul_comm r₁]; rw [mul_comm s₁]

Depends on / 依赖: mul_comm, oreDiv_mul_oreDiv_comm
-/
instance : CommMonoid R[S⁻¹] where
  mul_comm := fun x y => by
    cases x with | _ r₁ s₁
    cases y with | _ r₂ s₂
    rw [oreDiv_mul_oreDiv_comm]; rw [oreDiv_mul_oreDiv_comm]; rw [mul_comm r₁]; rw [mul_comm s₁]

end CommMonoid

section Zero

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S] {X : Type*} [Zero X]
variable [MulAction R X]


/-- `0` in the localization, defined as `0 /ₒ 1`. -/
@[irreducible]
/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : X[S⁻¹]
  body: 0 /ₒ 1

中文:
定义 zero
  签名: : X[S⁻¹]
  定义体: 0 /ₒ 1
-/
protected def zero : X[S⁻¹] := 0 /ₒ 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero X[S⁻¹]
  body: ⟨OreLocalization.zero⟩

中文:
实例 :
  签名: 零 X[S⁻¹]
  定义体: ⟨OreLocalization.zero⟩

Depends on / 依赖: OreLocalization, OreLocalization.zero
-/
instance : Zero X[S⁻¹] :=
  ⟨OreLocalization.zero⟩

/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: (0 : X[S⁻¹]) = 0 /ₒ 1
  proof: by
  with_unfolding_all rfl

中文:
定理 zero_def
  结论: (0 : X[S⁻¹]) = 0 /ₒ 1
  证明: by
  with_unfolding_all rfl
-/
protected theorem zero_def : (0 : X[S⁻¹]) = 0 /ₒ 1 := by
  with_unfolding_all rfl

end Zero

end OreLocalization
