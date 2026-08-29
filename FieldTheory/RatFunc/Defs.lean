/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The field of rational functions

Files in this folder define the field `K⟮X⟯` of rational functions over a field `K`, show it
is the field of fractions of `K[X]` and provide the main results concerning it. This file contains
the basic definition.

For connections with Laurent Series, see `Mathlib/RingTheory/LaurentSeries.lean`.

## Main definitions
We provide a set of recursion and induction principles:
- `RatFunc.liftOn`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
- `RatFunc.liftOn'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
- `RatFunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
  rational functions

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`RatFunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `Field` and `IsFractionRing` structure,
namely `RatFunc.ofFractionRing`, `RatFunc.toFractionRing`, `RatFunc.mk` and
`RatFunc.toFractionRingRingEquiv`.
All these maps get `simp`ed to bundled morphisms like `algebraMap K[X] K⟮X⟯`
and `IsLocalization.algEquiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

/--
Definition of `RatFunc` / `RatFunc` 的定义

English:
structure RatFunc
  parameters: [CommRing K]
  (no additional axioms)

中文:
结构 RatFunc
  参数: [CommRing K]
  (无附加公理)
-/
structure RatFunc [CommRing K] : Type u where ofFractionRing ::
/-- the coercion to the fraction ring of the polynomial ring -/
  toFractionRing : FractionRing K[X]

@[inherit_doc] scoped[RatFunc] notation:9000 R "⟮X⟯" => RatFunc R

namespace RatFunc

section CommRing

variable {K}
variable [CommRing K]

section Rec


/--
theorem `ofFractionRing_injective` / 定理 `ofFractionRing_injective`

English:
theorem ofFractionRing_injective
  statement: Function.Injective (ofFractionRing : _ -> K⟮X⟯)
  proof: fun _ _ => ofFractionRing.inj

中文:
定理 ofFractionRing_injective
  结论: Function.Injective (ofFractionRing : _ -> K⟮X⟯)
  证明: fun _ _ => ofFractionRing.inj

Depends on / 依赖: ofFractionRing, ofFractionRing.inj
-/
theorem ofFractionRing_injective : Function.Injective (ofFractionRing : _ -> K⟮X⟯) :=
  fun _ _ => ofFractionRing.inj

/--
theorem `toFractionRing_injective` / 定理 `toFractionRing_injective`

English:
theorem toFractionRing_injective
  statement: Function.Injective (toFractionRing : _ -> FractionRing K[X])

中文:
定理 toFractionRing_injective
  结论: Function.Injective (toFractionRing : _ -> FractionRing K[X])
-/
theorem toFractionRing_injective : Function.Injective (toFractionRing : _ -> FractionRing K[X])
  | ⟨x⟩, ⟨y⟩, xy => by subst xy; rfl

/--
lemma `toFractionRing_inj` / 引理 `toFractionRing_inj`

English:
lemma toFractionRing_inj
  given: {x y : K⟮X⟯}
  proof: toFractionRing_injective.eq_iff

中文:
引理 toFractionRing_inj
  条件: {x y : K⟮X⟯}
  证明: toFractionRing_injective.eq_iff
-/
@[simp] lemma toFractionRing_inj {x y : K⟮X⟯} :
    toFractionRing x = toFractionRing y ↔ x = y :=
  toFractionRing_injective.eq_iff

/-- Non-dependent recursion principle for `K⟮X⟯`:
To construct a term of `P : Sort*` out of `x : K⟮X⟯`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `q' * p = q * p'` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `K⟮X⟯` by setting
`liftOn (p / q) f _ = f p q`.

When `[IsDomain K]`, one can use `RatFunc.liftOn'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
protected irreducible_def liftOn {P : Sort v} (x : K⟮X⟯) (f : K[X] -> K[X] -> P)
    (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq' : q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q') :
    P :=
  Localization.liftOn (toFractionRing x) (fun p q => f p q) fun {_ _ q q'} h =>
    H q.2 q'.2 (let ⟨⟨_, _⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)

/--
theorem `liftOn_ofFractionRing_mk` / 定理 `liftOn_ofFractionRing_mk`

English:
theorem liftOn_ofFractionRing_mk
  statement: {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] -> K[X] -> P)
  proof: by
  rw [RatFunc.liftOn]
  exact Localization.liftOn_mk _ _ _ _

中文:
定理 liftOn_ofFractionRing_mk
  结论: {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] -> K[X] -> P)
  证明: by
  rw [RatFunc.liftOn]
  exact Localization.liftOn_mk _ _ _ _

Depends on / 依赖: Localization, Localization.liftOn_mk, RatFunc, RatFunc.liftOn, liftOn, liftOn_mk
-/
theorem liftOn_ofFractionRing_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] -> K[X] -> P)
    (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq' : q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q') :
    RatFunc.liftOn (ofFractionRing (Localization.mk n d)) f @H = f n d := by
  rw [RatFunc.liftOn]
  exact Localization.liftOn_mk _ _ _ _

/--
theorem `liftOn_condition_of_liftOn'_condition` / 定理 `liftOn_condition_of_liftOn'_condition`

English:
theorem liftOn_condition_of_liftOn'_condition
  statement: {P : Sort v} {f : K[X] -> K[X] -> P}
  proof: calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq

中文:
定理 liftOn_condition_of_liftOn'_condition
  结论: {P : Sort v} {f : K[X] -> K[X] -> P}
  证明: calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq

Depends on / 依赖: mul_comm
-/
theorem liftOn_condition_of_liftOn'_condition {P : Sort v} {f : K[X] -> K[X] -> P}
    (H : forall {p q a} (_ : q != 0) (_ha : a != 0), f (a * p) (a * q) = f p q) ⦃p q p' q' : K[X]⦄
    (hq : q != 0) (hq' : q' != 0) (h : q' * p = q * p') : f p q = f p' q' :=
  calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq

section IsDomain

variable [IsDomain K]

/-- `RatFunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `Algebra` structure on `RatFunc`;
the `simp` normal form of `mk p q` is `algebraMap _ _ p / algebraMap _ _ q`.
-/
protected irreducible_def mk (p q : K[X]) : K⟮X⟯ :=
  ofFractionRing (algebraMap _ _ p / algebraMap _ _ q)

/--
theorem `mk_eq_div'` / 定理 `mk_eq_div'`

English:
theorem mk_eq_div'
  given: (p q : K[X])
  proof: by rw [RatFunc.mk]

中文:
定理 mk_eq_div'
  条件: (p q : K[X])
  证明: by rw [RatFunc.mk]

Depends on / 依赖: RatFunc, RatFunc.mk
-/
theorem mk_eq_div' (p q : K[X]) :
    RatFunc.mk p q = ofFractionRing (algebraMap _ _ p / algebraMap _ _ q) := by rw [RatFunc.mk]

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: (p : K[X])
  statement: RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X])
  proof: by
  rw [mk_eq_div']; rw [map_zero]; rw [div_zero]

中文:
定理 mk_zero
  条件: (p : K[X])
  结论: RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X])
  证明: by
  rw [mk_eq_div']; rw [map_zero]; rw [div_zero]

Depends on / 依赖: div_zero, map_zero, mk_eq_div
-/
theorem mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X]) := by
  rw [mk_eq_div']; rw [map_zero]; rw [div_zero]

/--
theorem `mk_coe_def` / 定理 `mk_coe_def`

English:
theorem mk_coe_def
  given: (p : K[X]) (q : K[X]⁰)
  proof: by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]

中文:
定理 mk_coe_def
  条件: (p : K[X]) (q : K[X]⁰)
  证明: by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]

Depends on / 依赖: FractionRing, FractionRing.mk_eq_div, Localization, Localization.mk_eq_mk, mk_eq_div, mk_eq_mk
-/
theorem mk_coe_def (p : K[X]) (q : K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' _ p q) := by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]

/--
theorem `mk_def_of_mem` / 定理 `mk_def_of_mem`

English:
theorem mk_def_of_mem
  given: (p : K[X]) {q} (hq : q in K[X]⁰)
  proof: by
  simp only [← mk_coe_def]

中文:
定理 mk_def_of_mem
  条件: (p : K[X]) {q} (hq : q in K[X]⁰)
  证明: by
  simp only [← mk_coe_def]

Depends on / 依赖: mk_coe_def
-/
theorem mk_def_of_mem (p : K[X]) {q} (hq : q in K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq⟩) := by
  simp only [← mk_coe_def]

/--
theorem `mk_def_of_ne` / 定理 `mk_def_of_ne`

English:
theorem mk_def_of_ne
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: mk_def_of_mem p _

中文:
定理 mk_def_of_ne
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: mk_def_of_mem p _

Depends on / 依赖: mk_def_of_mem
-/
theorem mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q != 0) :
    RatFunc.mk p q =
      ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p
        ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  mk_def_of_mem p _

/--
theorem `mk_eq_localization_mk` / 定理 `mk_eq_localization_mk`

English:
theorem mk_eq_localization_mk
  given: (p : K[X]) {q : K[X]} (hq : q != 0)
  proof: by
  rw [mk_def_of_ne _ hq]; rw [Localization.mk_eq_mk']

中文:
定理 mk_eq_localization_mk
  条件: (p : K[X]) {q : K[X]} (hq : q != 0)
  证明: by
  rw [mk_def_of_ne _ hq]; rw [Localization.mk_eq_mk']

Depends on / 依赖: Localization, Localization.mk_eq_mk, mk_def_of_ne, mk_eq_mk
-/
theorem mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q != 0) :
    RatFunc.mk p q =
      ofFractionRing (Localization.mk p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) := by
  rw [mk_def_of_ne _ hq]; rw [Localization.mk_eq_mk']

/--
theorem `mk_one'` / 定理 `mk_one'`

English:
theorem mk_one'
  given: (p : K[X])
  proof: by
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]

中文:
定理 mk_one'
  条件: (p : K[X])
  证明: by
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]

Depends on / 依赖: FractionRing, IsLocalization, IsLocalization.mk, Submonoid, Submonoid.coe_one, _one, coe_one, mk_coe_def
-/
theorem mk_one' (p : K[X]) :
    RatFunc.mk p 1 = ofFractionRing (algebraMap _ _ p) := by
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]

/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {p q p' q' : K[X]} (hq : q != 0) (hq' : q' != 0)
  proof: by
  rw [mk_def_of_ne _ hq]; rw [mk_def_of_ne _ hq']; rw [ofFractionRing_injective.eq_iff]; rw [IsLocalization.mk'_eq_iff_eq']; rw [(IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]

中文:
定理 mk_eq_mk
  条件: {p q p' q' : K[X]} (hq : q != 0) (hq' : q' != 0)
  证明: by
  rw [mk_def_of_ne _ hq]; rw [mk_def_of_ne _ hq']; rw [ofFractionRing_injective.eq_iff]; rw [IsLocalization.mk'_eq_iff_eq']; rw [(IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, IsLocalization, IsLocalization.mk, _eq_iff_eq, eq_iff, injective, mk_def_of_ne, ofFractionRing_injective, ofFractionRing_injective.eq_iff
-/
theorem mk_eq_mk {p q p' q' : K[X]} (hq : q != 0) (hq' : q' != 0) :
    RatFunc.mk p q = RatFunc.mk p' q' ↔ p * q' = p' * q := by
  rw [mk_def_of_ne _ hq]; rw [mk_def_of_ne _ hq']; rw [ofFractionRing_injective.eq_iff]; rw [IsLocalization.mk'_eq_iff_eq']; rw [(IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]

/--
theorem `liftOn_mk` / 定理 `liftOn_mk`

English:
theorem liftOn_mk
  statement: {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
  proof: by
  by_cases hq : q = 0
  · subst hq
    simp only [mk_zero, f0, ← Localization.mk_zero 1,
      liftOn_ofFractionRing_mk, Submonoid.coe_one]
  · simp only [mk_eq_localization_mk _ hq, liftOn_ofFractionRing_mk]

中文:
定理 liftOn_mk
  结论: {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : 对任意 p, f p 0 = f 0 1)
  证明: by
  by_cases hq : q = 0
  · subst hq
    simp only [mk_zero, f0, ← Localization.mk_zero 1,
      liftOn_ofFractionRing_mk, Submonoid.coe_one]
  · simp only [mk_eq_localization_mk _ hq, liftOn_ofFractionRing_mk]

Depends on / 依赖: Localization, Localization.mk_zero, RatFunc, RatFunc.mk, Submonoid, Submonoid.coe_one, coe_one, liftOn, liftOn_ofFractionRing_mk, mk_eq_localization_mk, mk_zero, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem liftOn_mk {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
    (H' : forall {p q p' q'} (_hq : q != 0) (_hq' : q' != 0), q' * p = q * p' -> f p q = f p' q')
    (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq' : q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.mk p q).liftOn f @H = f p q := by
  by_cases hq : q = 0
  · subst hq
    simp only [mk_zero, f0, ← Localization.mk_zero 1,
      liftOn_ofFractionRing_mk, Submonoid.coe_one]
  · simp only [mk_eq_localization_mk _ hq, liftOn_ofFractionRing_mk]

/-- Non-dependent recursion principle for `K⟮X⟯`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `K⟮X⟯` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
protected irreducible_def liftOn' {P : Sort v} (x : K⟮X⟯) (f : K[X] -> K[X] -> P)
  (H : forall {p q a} (_hq : q != 0) (_ha : a != 0), f (a * p) (a * q) = f p q) : P :=
  x.liftOn f fun {_p _q _p' _q'} hq hq' =>
    liftOn_condition_of_liftOn'_condition (@H) (nonZeroDivisors.ne_zero hq)
      (nonZeroDivisors.ne_zero hq')

/--
theorem `liftOn'_mk` / 定理 `liftOn'_mk`

English:
theorem liftOn'_mk
  statement: {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
  proof: by
  rw [RatFunc.liftOn']; rw [RatFunc.liftOn_mk _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

中文:
定理 liftOn'_mk
  结论: {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : 对任意 p, f p 0 = f 0 1)
  证明: by
  rw [RatFunc.liftOn']; rw [RatFunc.liftOn_mk _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H
-/
theorem liftOn'_mk {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p, f p 0 = f 0 1)
    (H : forall {p q a} (_hq : q != 0) (_ha : a != 0), f (a * p) (a * q) = f p q) :
    (RatFunc.mk p q).liftOn' f @H = f p q := by
  rw [RatFunc.liftOn']; rw [RatFunc.liftOn_mk _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

/-- Induction principle for `K⟮X⟯`: if `f p q : P (RatFunc.mk p q)` for all `p q`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on`, which is a recursion principle defined in terms of `algebraMap`.
-/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  given: {P : K⟮X⟯ -> Prop}

中文:
定理 induction_on'
  条件: {P : K⟮X⟯ -> 命题}
-/
protected theorem induction_on' {P : K⟮X⟯ -> Prop} :
    forall (x : K⟮X⟯) (_pq : forall (p q : K[X]) (_ : q != 0), P (RatFunc.mk p q)), P x
  | ⟨x⟩, f =>
    Localization.induction_on x fun ⟨p, q⟩ => by
      simpa only [mk_coe_def, Localization.mk_eq_mk'] using
        f p q (mem_nonZeroDivisors_iff_ne_zero.mp q.2)

end IsDomain

end Rec

end CommRing

end RatFunc
