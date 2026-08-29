/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Submonoid.DistribMulAction
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.Algebra.GroupWithZero.Defs

/-!

# Localization over left Ore sets.

This file proves results on the localization of rings (monoids with zeros) over a left Ore set.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

-/

@[expose] public section

assert_not_exists RelIso

universe u

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

@[simp]
/--
theorem `zero_oreDiv'` / 定理 `zero_oreDiv'`

English:
theorem zero_oreDiv'
  given: (s : S)
  statement: (0 : R) /ₒ s = 0
  proof: by
  rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  exact ⟨s, 1, by simp [Submonoid.smul_def]⟩

中文:
定理 zero_oreDiv'
  条件: (s : S)
  结论: (0 : R) /ₒ s = 0
  证明: by
  rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  exact ⟨s, 1, by simp [Submonoid.smul_def]⟩

Depends on / 依赖: OreLocalization, OreLocalization.zero_def, Submonoid, Submonoid.smul_def, oreDiv_eq_iff, smul_def, zero_def
-/
theorem zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0 := by
  rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  exact ⟨s, 1, by simp [Submonoid.smul_def]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZero R[S⁻¹]
  body: by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def]; rw [oreDiv_mul_char 0 r 1 s 0 1 (by simp)]; rw [zero_mul]; rw [one_mul]
  mul_zero x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def]; rw [mul_div_one]; rw [mul_

中文:
实例 :
  签名: MonoidWithZero R[S⁻¹]
  定义体: by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def]; rw [oreDiv_mul_char 0 r 1 s 0 1 (by simp)]; rw [zero_mul]; rw [one_mul]
  mul_zero x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def]; rw [mul_div_one]; rw [mul_

Depends on / 依赖: OreLocalization, OreLocalization.ind, OreLocalization.zero_def, mul_div_one, mul_zero, one_mul, oreDiv_mul_char, zero_def, zero_mul, zero_oreDiv
-/
instance : MonoidWithZero R[S⁻¹] where
  zero_mul x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def]; rw [oreDiv_mul_char 0 r 1 s 0 1 (by simp)]; rw [zero_mul]; rw [one_mul]
  mul_zero x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def]; rw [mul_div_one]; rw [mul_zero]; rw [zero_oreDiv']; rw [zero_oreDiv']

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  proof: by
  rw [← subsingleton_iff_zero_eq_one]; rw [OreLocalization.one_def]; rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  simp

中文:
定理 subsingleton_iff
  证明: by
  rw [← subsingleton_iff_zero_eq_one]; rw [OreLocalization.one_def]; rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  simp

Depends on / 依赖: OreLocalization, OreLocalization.one_def, OreLocalization.zero_def, one_def, oreDiv_eq_iff, subsingleton_iff_zero_eq_one, zero_def
-/
theorem subsingleton_iff :
    Subsingleton R[S⁻¹] ↔ 0 in S := by
  rw [← subsingleton_iff_zero_eq_one]; rw [OreLocalization.one_def]; rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  simp

/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  proof: by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]

中文:
定理 nontrivial_iff
  证明: by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]

Depends on / 依赖: not_subsingleton_iff_nontrivial, subsingleton_iff
-/
theorem nontrivial_iff :
    Nontrivial R[S⁻¹] ↔ 0 ∉ S := by
  rw [← not_subsingleton_iff_nontrivial]; rw [subsingleton_iff]

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] {S : Submonoid R} [OreSet S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoidWithZero R[S⁻¹]
  body: (inferInstance : MonoidWithZero R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

中文:
实例 :
  签名: CommMonoidWithZero R[S⁻¹]
  定义体: (inferInstance : MonoidWithZero R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

Depends on / 依赖: MonoidWithZero
-/
instance : CommMonoidWithZero R[S⁻¹] where
  __ := (inferInstance : MonoidWithZero R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommMonoidWithZero

section DistribMulAction

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S] {X : Type*} [AddMonoid X]
variable [DistribMulAction R X]

/--
Definition of `add''` / `add''` 的定义

English:
definition add''
  signature: (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S)
  body: (oreDenom (s₁ : R) s₂ • r₁ + oreNum (s₁ : R) s₂ • r₂) /ₒ (oreDenom (s₁ : R) s₂ * s₁)

中文:
定义 add''
  签名: (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S)
  定义体: (oreDenom (s₁ : R) s₂ • r₁ + oreNum (s₁ : R) s₂ • r₂) /ₒ (oreDenom (s₁ : R) s₂ * s₁)
-/
private def add'' (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
  (oreDenom (s₁ : R) s₂ • r₁ + oreNum (s₁ : R) s₂ • r₂) /ₒ (oreDenom (s₁ : R) s₂ * s₁)

/--
theorem `add''_char` / 定理 `add''_char`

English:
theorem add''_char
  statement: (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) (rb : R) (sb : R)
  proof: by
  simp only [add'']
  have ha := ore_eq (s₁ : R) s₂
  generalize oreNum (s₁ : R) s₂ = ra at *
  generalize oreDenom (s₁ : R) s₂ = sa at *
  rw [oreDiv_eq_iff]
  rcases oreCondition sb sa with ⟨rc, sc, hc⟩
  have : sc * rb * s₂ = rc * ra * s₂ := by
    rw [mul_assoc rc]; rw [← ha]; rw [← mul_assoc

中文:
定理 add''_char
  结论: (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) (rb : R) (sb : R)
  证明: by
  simp only [add'']
  have ha := ore_eq (s₁ : R) s₂
  generalize oreNum (s₁ : R) s₂ = ra at *
  generalize oreDenom (s₁ : R) s₂ = sa at *
  rw [oreDiv_eq_iff]
  rcases oreCondition sb sa with ⟨rc, sc, hc⟩
  have : sc * rb * s₂ = rc * ra * s₂ := by
    rw [mul_assoc rc]; rw [← ha]; rw [← mul_assoc
-/
private theorem add''_char (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) (rb : R) (sb : R)
    (hb : sb * s₁ = rb * s₂) (h : sb * s₁ in S) :
    add'' r₁ s₁ r₂ s₂ = (sb • r₁ + rb • r₂) /ₒ ⟨sb * s₁, h⟩ := by
  simp only [add'']
  have ha := ore_eq (s₁ : R) s₂
  generalize oreNum (s₁ : R) s₂ = ra at *
  generalize oreDenom (s₁ : R) s₂ = sa at *
  rw [oreDiv_eq_iff]
  rcases oreCondition sb sa with ⟨rc, sc, hc⟩
  have : sc * rb * s₂ = rc * ra * s₂ := by
    rw [mul_assoc rc]; rw [← ha]; rw [← mul_assoc]; rw [← hc]; rw [mul_assoc]; rw [mul_assoc]; rw [hb]
  rcases ore_right_cancel _ _ s₂ this with ⟨sd, hd⟩
  use sd * sc
  use sd * rc
  simp only [smul_add, smul_smul, Submonoid.smul_def, Submonoid.coe_mul]
  constructor
  · rw [mul_assoc _ _ rb, hd, mul_assoc, hc, mul_assoc, mul_assoc]
  · rw [mul_assoc, ← mul_assoc (sc : R), hc, mul_assoc, mul_assoc]

attribute [local instance] OreLocalization.oreEqv

/--
Definition of `add'` / `add'` 的定义

English:
definition add'
  signature: (r₂ : X) (s₂ : S)
  body: (--plus tilde
      Quotient.lift
      fun r₁s₁ : X × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    --s~~, r~~
    r

中文:
定义 add'
  签名: (r₂ : X) (s₂ : S)
  定义体: (--plus tilde
      Quotient.lift
      fun r₁s₁ : X × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    --s~~, r~~
    r
-/
private def add' (r₂ : X) (s₂ : S) : X[S⁻¹] -> X[S⁻¹] :=
  (--plus tilde
      Quotient.lift
      fun r₁s₁ : X × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    --s~~, r~~
    rcases oreCondition rb sc with ⟨rd, sd, hd⟩
    -- s#, r#
    dsimp at *
    rw [add''_char _ _ _ _ rc sc hc (sc * s₁').2]
    have : sd * sb * s₁ = rd * rc * s₂ := by
      rw [mul_assoc]; rw [hb']; rw [← mul_assoc]; rw [hd]; rw [mul_assoc]; rw [hc]; rw [← mul_assoc]
    rw [add''_char _ _ _ _ (rd * rc : R) (sd * sb) this (sd * sb * s₁).2]
    rw [mul_smul]; rw [← Submonoid.smul_def sb]; rw [hb]; rw [smul_smul]; rw [hd]; rw [oreDiv_eq_iff]
    use 1
    use rd
    simp only [mul_smul, smul_add, one_smul, OneMemClass.coe_one, one_mul, true_and]
    rw [this]; rw [hc]; rw [mul_assoc]

/-- The addition on the Ore localization. -/
@[irreducible]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : X[S⁻¹] -> X[S⁻¹] -> X[S⁻¹]
  body: fun x =>
  Quotient.lift (fun rs : X × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨sb, rb, hb, hb'⟩
      induction x with | _ r₃ s₃
      change add'' _ _ _ _ = add'' _ _ _ _
      dsimp only at *
      rcases oreCondition (s₃ : R) s₂ with ⟨rc, sc, hc⟩
      rcases oreCondition r

中文:
定义 add
  签名: : X[S⁻¹] -> X[S⁻¹] -> X[S⁻¹]
  定义体: fun x =>
  Quotient.lift (fun rs : X × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨sb, rb, hb, hb'⟩
      induction x with | _ r₃ s₃
      change add'' _ _ _ _ = add'' _ _ _ _
      dsimp only at *
      rcases oreCondition (s₃ : R) s₂ with ⟨rc, sc, hc⟩
      rcases oreCondition r
-/
private def add : X[S⁻¹] -> X[S⁻¹] -> X[S⁻¹] := fun x =>
  Quotient.lift (fun rs : X × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨sb, rb, hb, hb'⟩
      induction x with | _ r₃ s₃
      change add'' _ _ _ _ = add'' _ _ _ _
      dsimp only at *
      rcases oreCondition (s₃ : R) s₂ with ⟨rc, sc, hc⟩
      rcases oreCondition rc sb with ⟨rd, sd, hd⟩
      have : rd * rb * s₁ = sd * sc * s₃ := by
        rw [mul_assoc]; rw [← hb']; rw [← mul_assoc]; rw [← hd]; rw [mul_assoc]; rw [← hc]; rw [mul_assoc]
      rw [add''_char _ _ _ _ rc sc hc (sc * s₃).2]
      rw [add''_char _ _ _ _ _ _ this.symm (sd * sc * s₃).2]
      refine oreDiv_eq_iff.mpr ?_
      simp only [smul_add]
      use sd, 1
      simp only [one_smul, one_mul, mul_smul, ← hb, Submonoid.smul_def, ← mul_assoc, and_true]
      simp only [smul_smul, hd])

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add X[S⁻¹]
  body: ⟨add⟩

中文:
实例 :
  签名: Add X[S⁻¹]
  定义体: ⟨add⟩
-/
instance : Add X[S⁻¹] :=
  ⟨add⟩

/--
theorem `oreDiv_add_oreDiv` / 定理 `oreDiv_add_oreDiv`

English:
theorem oreDiv_add_oreDiv
  given: {r r' : X} {s s' : S}
  proof: by
  with_unfolding_all rfl

中文:
定理 oreDiv_add_oreDiv
  条件: {r r' : X} {s s' : S}
  证明: by
  with_unfolding_all rfl

Depends on / 依赖: with_unfolding_all
-/
theorem oreDiv_add_oreDiv {r r' : X} {s s' : S} :
    r /ₒ s + r' /ₒ s' =
      (oreDenom (s : R) s' • r + oreNum (s : R) s' • r') /ₒ (oreDenom (s : R) s' * s) := by
  with_unfolding_all rfl

/--
theorem `oreDiv_add_char'` / 定理 `oreDiv_add_char'`

English:
theorem oreDiv_add_char'
  statement: {r r' : X} (s s' : S) (rb : R) (sb : R)
  proof: by
  with_unfolding_all exact add''_char r s r' s' rb sb h h'

中文:
定理 oreDiv_add_char'
  结论: {r r' : X} (s s' : S) (rb : R) (sb : R)
  证明: by
  with_unfolding_all exact add''_char r s r' s' rb sb h h'

Depends on / 依赖: _char, with_unfolding_all
-/
theorem oreDiv_add_char' {r r' : X} (s s' : S) (rb : R) (sb : R)
    (h : sb * s = rb * s') (h' : sb * s in S) :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ ⟨sb * s, h'⟩ := by
  with_unfolding_all exact add''_char r s r' s' rb sb h h'

/--
theorem `oreDiv_add_char` / 定理 `oreDiv_add_char`

English:
theorem oreDiv_add_char
  given: {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb * s')
  proof: oreDiv_add_char' s s' rb sb h (sb * s).2

中文:
定理 oreDiv_add_char
  条件: {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb * s')
  证明: oreDiv_add_char' s s' rb sb h (sb * s).2

Depends on / 依赖: oreDiv_add_char
-/
theorem oreDiv_add_char {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb * s') :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ (sb * s) :=
  oreDiv_add_char' s s' rb sb h (sb * s).2

/--
Definition of `oreDivAddChar'` / `oreDivAddChar'` 的定义

English:
definition oreDivAddChar'
  signature: (r r' : X) (s s' : S)
  body: ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩

@[simp]

中文:
定义 oreDivAddChar'
  签名: (r r' : X) (s s' : S)
  定义体: ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩

@[simp]

Depends on / 依赖: oreDenom, oreDiv_add_oreDiv, oreNum, ore_eq
-/
def oreDivAddChar' (r r' : X) (s s' : S) :
    Σ' r'' : R,
      Σ' s'' : S, s'' * s = r'' * s' ∧ r /ₒ s + r' /ₒ s' = (s'' • r + r'' • r') /ₒ (s'' * s) :=
  ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩

@[simp]
/--
theorem `add_oreDiv` / 定理 `add_oreDiv`

English:
theorem add_oreDiv
  given: {r r' : X} {s : S}
  statement: r /ₒ s + r' /ₒ s = (r + r') /ₒ s
  proof: by
  simp [oreDiv_add_char s s 1 1 (by simp)]

中文:
定理 add_oreDiv
  条件: {r r' : X} {s : S}
  结论: r /ₒ s + r' /ₒ s = (r + r') /ₒ s
  证明: by
  simp [oreDiv_add_char s s 1 1 (by simp)]

Depends on / 依赖: oreDiv_add_char
-/
theorem add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' /ₒ s = (r + r') /ₒ s := by
  simp [oreDiv_add_char s s 1 1 (by simp)]

/--
theorem `add_assoc` / 定理 `add_assoc`

English:
theorem add_assoc
  given: (x y z : X[S⁻¹])
  statement: x + y + z = x + (y + z)
  proof: by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' (sa • r₁ + ra • r₂) r₃ (sa * s₁) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  simp only [smul_add, add_assoc

中文:
定理 add_assoc
  条件: (x y z : X[S⁻¹])
  结论: x + y + z = x + (y + z)
  证明: by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' (sa • r₁ + ra • r₂) r₃ (sa * s₁) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  simp only [smul_add, add_assoc
-/
protected theorem add_assoc (x y z : X[S⁻¹]) : x + y + z = x + (y + z) := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' (sa • r₁ + ra • r₂) r₃ (sa * s₁) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  simp only [smul_add, add_assoc]
  simp_rw [← add_oreDiv, ← OreLocalization.expand']
  congr 2
  · rw [OreLocalization.expand r₂ s₂ ra (ha.symm ▸ (sa * s₁).2)]; congr; ext; exact ha
  · rw [OreLocalization.expand r₃ s₃ rc (hc.symm ▸ (sc * (sa * s₁)).2)]; congr; ext; exact hc

@[simp]
/--
theorem `zero_oreDiv` / 定理 `zero_oreDiv`

English:
theorem zero_oreDiv
  given: (s : S)
  statement: (0 : X) /ₒ s = 0
  proof: by
  rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩

中文:
定理 zero_oreDiv
  条件: (s : S)
  结论: (0 : X) /ₒ s = 0
  证明: by
  rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩

Depends on / 依赖: OreLocalization, OreLocalization.zero_def, oreDiv_eq_iff, zero_def
-/
theorem zero_oreDiv (s : S) : (0 : X) /ₒ s = 0 := by
  rw [OreLocalization.zero_def]; rw [oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩

/--
theorem `zero_add` / 定理 `zero_add`

English:
theorem zero_add
  given: (x : X[S⁻¹])
  statement: 0 + x = x
  proof: by
  induction x
  rw [← zero_oreDiv]; rw [add_oreDiv]; simp

中文:
定理 zero_add
  条件: (x : X[S⁻¹])
  结论: 0 + x = x
  证明: by
  induction x
  rw [← zero_oreDiv]; rw [add_oreDiv]; simp
-/
protected theorem zero_add (x : X[S⁻¹]) : 0 + x = x := by
  induction x
  rw [← zero_oreDiv]; rw [add_oreDiv]; simp

/--
theorem `add_zero` / 定理 `add_zero`

English:
theorem add_zero
  given: (x : X[S⁻¹])
  statement: x + 0 = x
  proof: by
  induction x
  rw [← zero_oreDiv]; rw [add_oreDiv]; simp

中文:
定理 add_zero
  条件: (x : X[S⁻¹])
  结论: x + 0 = x
  证明: by
  induction x
  rw [← zero_oreDiv]; rw [add_oreDiv]; simp
-/
protected theorem add_zero (x : X[S⁻¹]) : x + 0 = x := by
  induction x
  rw [← zero_oreDiv]; rw [add_oreDiv]; simp

/-- Scalar multiplication by natural numbers on the Ore localization. -/
@[irreducible]
/--
Definition of `nsmul` / `nsmul` 的定义

English:
definition nsmul
  signature: : Nat -> X[S⁻¹] -> X[S⁻¹]
  body: nsmulRec

中文:
定义 nsmul
  签名: : 自然数 -> X[S⁻¹] -> X[S⁻¹]
  定义体: nsmulRec

Depends on / 依赖: nsmulRec
-/
def nsmul : Nat -> X[S⁻¹] -> X[S⁻¹] := nsmulRec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid X[S⁻¹]
  body: OreLocalization.add_assoc
    zero_add := OreLocalization.zero_add
    add_zero := OreLocalization.add_zero
    nsmul := nsmul
    nsmul_zero _ := by with_unfolding_all rfl
    nsmul_succ _ _ := by with_unfolding_all rfl

中文:
实例 :
  签名: AddMonoid X[S⁻¹]
  定义体: OreLocalization.add_assoc
    zero_add := OreLocalization.zero_add
    add_zero := OreLocalization.add_zero
    nsmul := nsmul
    nsmul_zero _ := by with_unfolding_all rfl
    nsmul_succ _ _ := by with_unfolding_all rfl

Depends on / 依赖: OreLocalization, OreLocalization.add_assoc, add_assoc
-/
instance : AddMonoid X[S⁻¹] where
    add_assoc := OreLocalization.add_assoc
    zero_add := OreLocalization.zero_add
    add_zero := OreLocalization.add_zero
    nsmul := nsmul
    nsmul_zero _ := by with_unfolding_all rfl
    nsmul_succ _ _ := by with_unfolding_all rfl

/--
theorem `smul_zero` / 定理 `smul_zero`

English:
theorem smul_zero
  given: (x : R[S⁻¹])
  statement: x • (0 : X[S⁻¹]) = 0
  proof: by
  induction x with | _ r s
  rw [OreLocalization.zero_def]; rw [smul_div_one]; rw [smul_zero]; rw [zero_oreDiv]; rw [zero_oreDiv]

中文:
定理 smul_zero
  条件: (x : R[S⁻¹])
  结论: x • (0 : X[S⁻¹]) = 0
  证明: by
  induction x with | _ r s
  rw [OreLocalization.zero_def]; rw [smul_div_one]; rw [smul_zero]; rw [zero_oreDiv]; rw [zero_oreDiv]
-/
protected theorem smul_zero (x : R[S⁻¹]) : x • (0 : X[S⁻¹]) = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def]; rw [smul_div_one]; rw [smul_zero]; rw [zero_oreDiv]; rw [zero_oreDiv]

/--
theorem `smul_add` / 定理 `smul_add`

English:
theorem smul_add
  given: (z : R[S⁻¹]) (x y : X[S⁻¹])
  proof: by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_me

中文:
定理 smul_add
  条件: (z : R[S⁻¹]) (x y : X[S⁻¹])
  证明: by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_me
-/
protected theorem smul_add (z : R[S⁻¹]) (x y : X[S⁻¹]) :
    z • (x + y) = z • x + z • y := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_mem)]
  rw [← Subtype.coe_eq_of_eq_mk ha]
  repeat rw [oreDiv_smul_oreDiv]
  simp only [smul_add, add_oreDiv]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction R[S⁻¹] X[S⁻¹]
  body: OreLocalization.smul_zero
  smul_add := OreLocalization.smul_add

中文:
实例 :
  签名: DistribMulAction R[S⁻¹] X[S⁻¹]
  定义体: OreLocalization.smul_zero
  smul_add := OreLocalization.smul_add

Depends on / 依赖: OreLocalization, OreLocalization.smul_zero, smul_zero
-/
instance : DistribMulAction R[S⁻¹] X[S⁻¹] where
  smul_zero := OreLocalization.smul_zero
  smul_add := OreLocalization.smul_add

instance {R₀} [Monoid R₀] [MulAction R₀ X] [MulAction R₀ R]
    [IsScalarTower R₀ R X] [IsScalarTower R₀ R R] :
    DistribMulAction R₀ X[S⁻¹] where
  smul_zero _ := by rw [← smul_one_oreDiv_one_smul, smul_zero]
  smul_add _ _ _ := by simp only [← smul_one_oreDiv_one_smul, smul_add]

end DistribMulAction

section AddCommMonoid

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [DistribMulAction R X]

/--
theorem `add_comm` / 定理 `add_comm`

English:
theorem add_comm
  given: (x y : X[S⁻¹])
  statement: x + y = y + x
  proof: by
  induction x with | _ r s
  induction y with | _ r' s'
  rcases oreDivAddChar' r r' s s' with ⟨ra, sa, ha, ha'⟩
  rw [ha']; rw [oreDiv_add_char' s' s _ _ ha.symm (ha ▸ (sa * s).2)]; rw [add_comm]
  congr; ext; exact ha

中文:
定理 add_comm
  条件: (x y : X[S⁻¹])
  结论: x + y = y + x
  证明: by
  induction x with | _ r s
  induction y with | _ r' s'
  rcases oreDivAddChar' r r' s s' with ⟨ra, sa, ha, ha'⟩
  rw [ha']; rw [oreDiv_add_char' s' s _ _ ha.symm (ha ▸ (sa * s).2)]; rw [add_comm]
  congr; ext; exact ha
-/
protected theorem add_comm (x y : X[S⁻¹]) : x + y = y + x := by
  induction x with | _ r s
  induction y with | _ r' s'
  rcases oreDivAddChar' r r' s s' with ⟨ra, sa, ha, ha'⟩
  rw [ha']; rw [oreDiv_add_char' s' s _ _ ha.symm (ha ▸ (sa * s).2)]; rw [add_comm]
  congr; ext; exact ha

/--
Instance `instAddCommMonoidOreLocalization` / 实例 `instAddCommMonoidOreLocalization`

English:
instance instAddCommMonoidOreLocalization
  signature: : AddCommMonoid X[S⁻¹] where
  body: OreLocalization.add_comm

中文:
实例 instAddCommMonoidOreLocalization
  签名: : AddCommMonoid X[S⁻¹] where
  定义体: OreLocalization.add_comm

Depends on / 依赖: OreLocalization, OreLocalization.add_comm, add_comm
-/
instance instAddCommMonoidOreLocalization : AddCommMonoid X[S⁻¹] where
  add_comm := OreLocalization.add_comm

end AddCommMonoid

section AddGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddGroup X] [DistribMulAction R X]

/-- Negation on the Ore localization is defined via negation on the numerator. -/
@[irreducible]
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : X[S⁻¹] -> X[S⁻¹]
  body: liftExpand (fun (r : X) (s : S) => -r /ₒ s) fun r t s ht => by
    rw [← smul_neg]; rw [← OreLocalization.expand]

中文:
定义 neg
  签名: : X[S⁻¹] -> X[S⁻¹]
  定义体: liftExpand (fun (r : X) (s : S) => -r /ₒ s) fun r t s ht => by
    rw [← smul_neg]; rw [← OreLocalization.expand]
-/
protected def neg : X[S⁻¹] -> X[S⁻¹] :=
  liftExpand (fun (r : X) (s : S) => -r /ₒ s) fun r t s ht => by
    rw [← smul_neg]; rw [← OreLocalization.expand]

/--
Instance `instNegOreLocalization` / 实例 `instNegOreLocalization`

English:
instance instNegOreLocalization
  signature: : Neg X[S⁻¹]
  body: ⟨OreLocalization.neg⟩

@[simp]

中文:
实例 instNegOreLocalization
  签名: : Neg X[S⁻¹]
  定义体: ⟨OreLocalization.neg⟩

@[simp]

Depends on / 依赖: OreLocalization, OreLocalization.neg
-/
instance instNegOreLocalization : Neg X[S⁻¹] :=
  ⟨OreLocalization.neg⟩

@[simp]
/--
theorem `neg_def` / 定理 `neg_def`

English:
theorem neg_def
  given: (r : X) (s : S)
  statement: -(r /ₒ s) = -r /ₒ s
  proof: by
  with_unfolding_all rfl

中文:
定理 neg_def
  条件: (r : X) (s : S)
  结论: -(r /ₒ s) = -r /ₒ s
  证明: by
  with_unfolding_all rfl
-/
protected theorem neg_def (r : X) (s : S) : -(r /ₒ s) = -r /ₒ s := by
  with_unfolding_all rfl

/--
theorem `neg_add_cancel` / 定理 `neg_add_cancel`

English:
theorem neg_add_cancel
  given: (x : X[S⁻¹])
  statement: -x + x = 0
  proof: by
  induction x with | _ r s; simp

中文:
定理 neg_add_cancel
  条件: (x : X[S⁻¹])
  结论: -x + x = 0
  证明: by
  induction x with | _ r s; simp
-/
protected theorem neg_add_cancel (x : X[S⁻¹]) : -x + x = 0 := by
  induction x with | _ r s; simp

/-- `zsmul` of `OreLocalization` -/
@[irreducible]
/--
Definition of `zsmul` / `zsmul` 的定义

English:
definition zsmul
  signature: : Int -> X[S⁻¹] -> X[S⁻¹]
  body: zsmulRec

unseal OreLocalization.zsmul in

中文:
定义 zsmul
  签名: : 整数 -> X[S⁻¹] -> X[S⁻¹]
  定义体: zsmulRec

unseal OreLocalization.zsmul in
-/
protected def zsmul : Int -> X[S⁻¹] -> X[S⁻¹] := zsmulRec

unseal OreLocalization.zsmul in
/--
Instance `instAddGroupOreLocalization` / 实例 `instAddGroupOreLocalization`

English:
instance instAddGroupOreLocalization
  signature: : AddGroup X[S⁻¹] where
  body: OreLocalization.neg_add_cancel
  zsmul := OreLocalization.zsmul

中文:
实例 instAddGroupOreLocalization
  签名: : AddGroup X[S⁻¹] where
  定义体: OreLocalization.neg_add_cancel
  zsmul := OreLocalization.zsmul

Depends on / 依赖: OreLocalization, OreLocalization.neg_add_cancel, neg_add_cancel
-/
instance instAddGroupOreLocalization : AddGroup X[S⁻¹] where
  neg_add_cancel := OreLocalization.neg_add_cancel
  zsmul := OreLocalization.zsmul

end AddGroup

section AddCommGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [DistribMulAction R X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup X[S⁻¹]
  body: (inferInstance : AddGroup X[S⁻¹])
  __ := (inferInstance : AddCommMonoid X[S⁻¹])

中文:
实例 :
  签名: AddCommGroup X[S⁻¹]
  定义体: (inferInstance : AddGroup X[S⁻¹])
  __ := (inferInstance : AddCommMonoid X[S⁻¹])

Depends on / 依赖: AddGroup
-/
instance : AddCommGroup X[S⁻¹] where
  __ := (inferInstance : AddGroup X[S⁻¹])
  __ := (inferInstance : AddCommMonoid X[S⁻¹])

end AddCommGroup

end OreLocalization
