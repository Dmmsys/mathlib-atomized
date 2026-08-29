/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Peel
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# p-adic numbers

This file defines the `p`-adic numbers (rationals) `ℚ_[p]` as
the completion of `ℚ` with respect to the `p`-adic norm.
We show that the `p`-adic norm on `ℚ` extends to `ℚ_[p]`, that `ℚ` is embedded in `ℚ_[p]`,
and that `ℚ_[p]` is Cauchy complete.

## Important definitions

* `Padic` : the type of `p`-adic numbers
* `padicNormE` : the rational-valued `p`-adic norm on `ℚ_[p]`
* `Padic.addValuation` : the additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`

## Notation

We introduce the notation `ℚ_[p]` for the `p`-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct `ℝ`.
`ℚ_[p]` inherits a field structure from this construction.
The extension of the norm on `ℚ` to `ℚ_[p]` is *not* analogous to extending the absolute value to
`ℝ` and hence the proof that `ℚ_[p]` is complete is different from the proof that ℝ is complete.

`padicNormE` is the rational-valued `p`-adic norm on `ℚ_[p]`.
To instantiate `ℚ_[p]` as a normed field, we must cast this into an `ℝ`-valued norm.
The `ℝ`-valued norm, using notation `‖ ‖` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padicNorm` to `padicNormE` when possible.
Since `padicNormE` and `‖ ‖` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

@[expose] public section

open WithZero

-- TODO: fix non-terminal simp; acts on 8 goals, leaving one
set_option linter.flexible false in
/--
Definition of `Rat.padicValuation` / `Rat.padicValuation` 的定义

English:
definition Rat.padicValuation
  signature: (p : Nat) [Fact p.Prime]
  body: if x = 0 then 0 else exp (-padicValRat p x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intros
    split_ifs <;>
    simp_all [padicValRat.mul, exp_add, mul_comm]
  map_add_le_max' := by
    intros
    split_ifs
    any_goals simp_all [-exp_neg]
    rw [← min_le_iff]
    exact 

中文:
定义 有理数.padicValuation
  签名: (p : 自然数) [Fact p.素]
  定义体: if x = 0 then 0 else exp (-padicValRat p x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intros
    split_ifs <;>
    simp_all [padicValRat.mul, exp_add, mul_comm]
  map_add_le_max' := by
    intros
    split_ifs
    any_goals simp_all [-exp_neg]
    rw [← min_le_iff]
    exact 

Depends on / 依赖: padicValRat
-/
def Rat.padicValuation (p : Nat) [Fact p.Prime] : Valuation Rat Intᵐ⁰ where
  toFun x := if x = 0 then 0 else exp (-padicValRat p x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intros
    split_ifs <;>
    simp_all [padicValRat.mul, exp_add, mul_comm]
  map_add_le_max' := by
    intros
    split_ifs
    any_goals simp_all [-exp_neg]
    rw [← min_le_iff]
    exact padicValRat.min_le_padicValRat_add ‹_›

/--
Definition of `Int.padicValuation` / `Int.padicValuation` 的定义

English:
definition Int.padicValuation
  signature: (p : Nat) [Fact p.Prime]
  body: (Rat.padicValuation p).comap (Int.castRingHom Rat)

中文:
定义 整数.padicValuation
  签名: (p : 自然数) [Fact p.素]
  定义体: (Rat.padicValuation p).comap (Int.castRingHom Rat)

Depends on / 依赖: Int.castRingHom, Rat.padicValuation, castRingHom, padicValuation
-/
def Int.padicValuation (p : Nat) [Fact p.Prime] : Valuation Int Intᵐ⁰ :=
  (Rat.padicValuation p).comap (Int.castRingHom Rat)

/--
lemma `Rat.padicValuation_cast` / 引理 `Rat.padicValuation_cast`

English:
lemma Rat.padicValuation_cast
  given: (p : Nat) [Fact p.Prime] (x : Int)
  proof: rfl

中文:
引理 有理数.padicValuation_cast
  条件: (p : 自然数) [Fact p.素] (x : 整数)
  证明: rfl
-/
lemma Rat.padicValuation_cast (p : Nat) [Fact p.Prime] (x : Int) :
    Rat.padicValuation p (Int.cast x) = Int.padicValuation p x :=
  rfl

/--
lemma `Rat.padicValuation_eq_zero_iff` / 引理 `Rat.padicValuation_eq_zero_iff`

English:
lemma Rat.padicValuation_eq_zero_iff
  given: {p : Nat} [Fact p.Prime] {x : Rat}
  proof: by
  simp

@[simp]

中文:
引理 有理数.padicValuation_eq_zero_iff
  条件: {p : 自然数} [Fact p.素] {x : 有理数}
  证明: by
  simp

@[simp]
-/
lemma Rat.padicValuation_eq_zero_iff {p : Nat} [Fact p.Prime] {x : Rat} :
    Rat.padicValuation p x = 0 ↔ x = 0 := by
  simp

@[simp]
/--
lemma `Int.padicValuation_eq_zero_iff` / 引理 `Int.padicValuation_eq_zero_iff`

English:
lemma Int.padicValuation_eq_zero_iff
  given: {p : Nat} [Fact p.Prime] {x : Int}
  proof: by
  simp [← Rat.padicValuation_cast]

@[simp]

中文:
引理 整数.padicValuation_eq_zero_iff
  条件: {p : 自然数} [Fact p.素] {x : 整数}
  证明: by
  simp [← Rat.padicValuation_cast]

@[simp]

Depends on / 依赖: Rat.padicValuation_cast, padicValuation_cast
-/
lemma Int.padicValuation_eq_zero_iff {p : Nat} [Fact p.Prime] {x : Int} :
    Int.padicValuation p x = 0 ↔ x = 0 := by
  simp [← Rat.padicValuation_cast]

@[simp]
/--
lemma `Rat.padicValuation_self` / 引理 `Rat.padicValuation_self`

English:
lemma Rat.padicValuation_self
  given: (p : Nat) [Fact p.Prime]
  proof: by
  simp [Rat.padicValuation, Nat.Prime.ne_zero Fact.out]

@[simp]

中文:
引理 有理数.padicValuation_self
  条件: (p : 自然数) [Fact p.素]
  证明: by
  simp [Rat.padicValuation, Nat.Prime.ne_zero Fact.out]

@[simp]

Depends on / 依赖: Fact.out, Nat.Prime.ne_zero, Rat.padicValuation, ne_zero, padicValuation
-/
lemma Rat.padicValuation_self (p : Nat) [Fact p.Prime] :
    Rat.padicValuation p p = exp (-1) := by
  simp [Rat.padicValuation, Nat.Prime.ne_zero Fact.out]

@[simp]
/--
lemma `Int.padicValuation_self` / 引理 `Int.padicValuation_self`

English:
lemma Int.padicValuation_self
  given: (p : Nat) [Fact p.Prime]
  proof: by
  simp [← Rat.padicValuation_cast]

中文:
引理 整数.padicValuation_self
  条件: (p : 自然数) [Fact p.素]
  证明: by
  simp [← Rat.padicValuation_cast]

Depends on / 依赖: Rat.padicValuation_cast, padicValuation_cast
-/
lemma Int.padicValuation_self (p : Nat) [Fact p.Prime] :
    Int.padicValuation p p = exp (-1) := by
  simp [← Rat.padicValuation_cast]

/--
lemma `Int.padicValuation_le_one` / 引理 `Int.padicValuation_le_one`

English:
lemma Int.padicValuation_le_one
  given: (p : Nat) [Fact p.Prime] (x : Int)
  proof: by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp
  · rw [← le_log_iff_exp_le] <;>
    simp_all

中文:
引理 整数.padicValuation_le_one
  条件: (p : 自然数) [Fact p.素] (x : 整数)
  证明: by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp
  · rw [← le_log_iff_exp_le] <;>
    simp_all

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, Rat.intCast_eq_zero_iff, Rat.padicValuation, Rat.padicValuation_cast, Valuation, Valuation.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, intCast_eq_zero_iff, le_log_iff_exp_le, of_int, padicValRat, padicValRat.of_int, padicValuation, padicValuation_cast, split_ifs
-/
lemma Int.padicValuation_le_one (p : Nat) [Fact p.Prime] (x : Int) :
    Int.padicValuation p x <= 1 := by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp
  · rw [← le_log_iff_exp_le] <;>
    simp_all

/--
lemma `Int.padicValuation_eq_one_iff` / 引理 `Int.padicValuation_eq_one_iff`

English:
lemma Int.padicValuation_eq_one_iff
  given: {p : Nat} [Fact p.Prime] {x : Int}
  proof: by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp_all
  · rw [← exp_zero, exp_injective.eq_iff]
    simp_all [Nat.Prime.ne_one Fact.out]

中文:
引理 整数.padicValuation_eq_one_iff
  条件: {p : 自然数} [Fact p.素] {x : 整数}
  证明: by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp_all
  · rw [← exp_zero, exp_injective.eq_iff]
    simp_all [Nat.Prime.ne_one Fact.out]

Depends on / 依赖: Fact.out, MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, Nat.Prime.ne_one, Rat.intCast_eq_zero_iff, Rat.padicValuation, Rat.padicValuation_cast, Valuation, Valuation.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, eq_iff, exp_injective, exp_injective.eq_iff, exp_zero, intCast_eq_zero_iff, ne_one, of_int, padicValRat
-/
lemma Int.padicValuation_eq_one_iff {p : Nat} [Fact p.Prime] {x : Int} :
    Int.padicValuation p x = 1 ↔ ¬ (p : Int) ∣ x := by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp_all
  · rw [← exp_zero, exp_injective.eq_iff]
    simp_all [Nat.Prime.ne_one Fact.out]

/--
lemma `Int.padicValuation_lt_one_iff` / 引理 `Int.padicValuation_lt_one_iff`

English:
lemma Int.padicValuation_lt_one_iff
  given: {p : Nat} [Fact p.Prime] {x : Int}
  proof: by
  simp [lt_iff_le_and_ne, padicValuation_eq_one_iff, Int.padicValuation_le_one]

中文:
引理 整数.padicValuation_lt_one_iff
  条件: {p : 自然数} [Fact p.素] {x : 整数}
  证明: by
  simp [lt_iff_le_and_ne, padicValuation_eq_one_iff, Int.padicValuation_le_one]

Depends on / 依赖: Int.padicValuation_le_one, lt_iff_le_and_ne, padicValuation_eq_one_iff, padicValuation_le_one
-/
lemma Int.padicValuation_lt_one_iff {p : Nat} [Fact p.Prime] {x : Int} :
    Int.padicValuation p x < 1 ↔ (p : Int) ∣ x := by
  simp [lt_iff_le_and_ne, padicValuation_eq_one_iff, Int.padicValuation_le_one]

/--
lemma `Rat.padicValuation_le_one_iff` / 引理 `Rat.padicValuation_le_one_iff`

English:
lemma Rat.padicValuation_le_one_iff
  given: {p : Nat} [Fact p.Prime] {x : Rat}
  proof: by
  nth_rw 1 [← x.num_div_den, map_div₀, ← Int.natCast_dvd_natCast, ← Int.padicValuation_eq_one_iff,
    Rat.padicValuation_cast, ← Int.cast_natCast, Rat.padicValuation_cast, div_le_one₀]
  · rcases (Int.padicValuation_le_one p x.den).eq_or_lt with h | h
    · simp [h, Int.padicValuation_le_one]
  

中文:
引理 有理数.padicValuation_le_one_iff
  条件: {p : 自然数} [Fact p.素] {x : 有理数}
  证明: by
  nth_rw 1 [← x.num_div_den, map_div₀, ← Int.natCast_dvd_natCast, ← Int.padicValuation_eq_one_iff,
    Rat.padicValuation_cast, ← Int.cast_natCast, Rat.padicValuation_cast, div_le_one₀]
  · rcases (Int.padicValuation_le_one p x.den).eq_or_lt with h | h
    · simp [h, Int.padicValuation_le_one]
  

Depends on / 依赖: Int.cast_natCast, Int.n, Int.natCast_dvd_natCast, Int.padicValuation_eq_one_iff, Int.padicValuation_le_one, Int.padicValuation_lt_one_iff, Rat.padicValuation_cast, cast_natCast, eq_or_lt, h.ne, iff_false, natCast_dvd_natCast, not_le, nth_rw, num_div_den, padicValuation_cast, padicValuation_eq_one_iff, padicValuation_le_one, padicValuation_lt_one_iff, x.den
-/
lemma Rat.padicValuation_le_one_iff {p : Nat} [Fact p.Prime] {x : Rat} :
    Rat.padicValuation p x <= 1 ↔ ¬ p ∣ x.den := by
  nth_rw 1 [← x.num_div_den, map_div₀, ← Int.natCast_dvd_natCast, ← Int.padicValuation_eq_one_iff,
    Rat.padicValuation_cast, ← Int.cast_natCast, Rat.padicValuation_cast, div_le_one₀]
  · rcases (Int.padicValuation_le_one p x.den).eq_or_lt with h | h
    · simp [h, Int.padicValuation_le_one]
    · simp only [h.ne, iff_false, not_le]
      rcases (Int.padicValuation_le_one p x.num).eq_or_lt with h' | h'
      · simp [h, h']
      · rw [Int.padicValuation_lt_one_iff] at h h'
        exfalso
        rw [Int.natCast_dvd_natCast] at h
        rw [Int.natCast_dvd] at h'
        exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) h h' x.reduced.symm
  · simp [zero_lt_iff]

/--
theorem `Rat.surjective_padicValuation` / 定理 `Rat.surjective_padicValuation`

English:
theorem Rat.surjective_padicValuation
  given: (p : Nat) [hp : Fact (p.Prime)]
  proof: by
  intro x
  induction x with
  | zero => simp
  | coe x =>
    induction x with | ofAdd x
    simp_rw [Rat.padicValuation, WithZero.exp, Valuation.coe_mk, MonoidWithZeroHom.coe_mk]
    rcases le_or_gt 0 x with (hx | hx)
    · exact ⟨(p ^ x.natAbs)⁻¹, by simp [hp.out.ne_zero, hx]⟩
    · exact ⟨p ^

中文:
定理 有理数.surjective_padicValuation
  条件: (p : 自然数) [hp : Fact (p.素)]
  证明: by
  intro x
  induction x with
  | zero => simp
  | coe x =>
    induction x with | ofAdd x
    simp_rw [Rat.padicValuation, WithZero.exp, Valuation.coe_mk, MonoidWithZeroHom.coe_mk]
    rcases le_or_gt 0 x with (hx | hx)
    · exact ⟨(p ^ x.natAbs)⁻¹, by simp [hp.out.ne_zero, hx]⟩
    · exact ⟨p ^

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, Rat.padicValuation, Valuation, Valuation.coe_mk, WithZero, WithZero.exp, abs_eq_neg_self, coe_mk, hp.out.ne_zero, hx.le, le_or_gt, natAbs, ne_zero, padicValRat, padicValRat.pow, padicValuation, simp_rw, x.natAbs
-/
theorem Rat.surjective_padicValuation (p : Nat) [hp : Fact (p.Prime)] :
    Function.Surjective (Rat.padicValuation p) := by
  intro x
  induction x with
  | zero => simp
  | coe x =>
    induction x with | ofAdd x
    simp_rw [Rat.padicValuation, WithZero.exp, Valuation.coe_mk, MonoidWithZeroHom.coe_mk]
    rcases le_or_gt 0 x with (hx | hx)
    · exact ⟨(p ^ x.natAbs)⁻¹, by simp [hp.out.ne_zero, hx]⟩
    · exact ⟨p ^ x.natAbs, by simp [hp.out.ne_zero, padicValRat.pow, abs_eq_neg_self.2 hx.le]⟩

noncomputable section

open Nat padicNorm CauSeq CauSeq.Completion Metric

/--
Definition of `PadicSeq` / `PadicSeq` 的定义

English:
abbreviation PadicSeq
  signature: (p : Nat)
  body: CauSeq _ (padicNorm p)

中文:
缩写 PadicSeq
  签名: (p : 自然数)
  定义体: CauSeq _ (padicNorm p)

Depends on / 依赖: CauSeq, padicNorm
-/
abbrev PadicSeq (p : Nat) :=
  CauSeq _ (padicNorm p)

namespace PadicSeq

section

variable {p : Nat} [Fact p.Prime]

/--
theorem `stationary` / 定理 `stationary`

English:
theorem stationary
  given: {f : CauSeq Rat (padicNorm p)} (hf : ¬f ≈ 0)
  proof: have : exists ε > 0, exists N1, forall j >= N1, ε <= padicNorm p (f j) :=
CauSeq.abv_pos_of_not_limZero not_limZero_of_not_congr_zero hf
  let ⟨ε, hε, N1, hN1⟩ := this
  let ⟨N2, hN2⟩ := CauSeq.cauchy₂ f hε
  ⟨max N1 N2, fun n m hn hm => by
    have : padicNorm p (f n - f m) < ε := hN2 _ (max_le_iff

中文:
定理 stationary
  条件: {f : CauSeq 有理数 (padicNorm p)} (hf : ¬f ≈ 0)
  证明: have : exists ε > 0, exists N1, forall j >= N1, ε <= padicNorm p (f j) :=
CauSeq.abv_pos_of_not_limZero not_limZero_of_not_congr_zero hf
  let ⟨ε, hε, N1, hN1⟩ := this
  let ⟨N2, hN2⟩ := CauSeq.cauchy₂ f hε
  ⟨max N1 N2, fun n m hn hm => by
    have : padicNorm p (f n - f m) < ε := hN2 _ (max_le_iff

Depends on / 依赖: CauSeq, CauSeq.abv_pos_of_not_limZero, CauSeq.cauchy, abv_pos_of_not_limZero, lt_of_lt_of_le, max_le_iff, not_limZero_of_not_congr_zero, padicNorm
-/
theorem stationary {f : CauSeq Rat (padicNorm p)} (hf : ¬f ≈ 0) :
    exists N, forall m n, N <= m -> N <= n -> padicNorm p (f n) = padicNorm p (f m) :=
  have : exists ε > 0, exists N1, forall j >= N1, ε <= padicNorm p (f j) :=
CauSeq.abv_pos_of_not_limZero not_limZero_of_not_congr_zero hf
  let ⟨ε, hε, N1, hN1⟩ := this
  let ⟨N2, hN2⟩ := CauSeq.cauchy₂ f hε
  ⟨max N1 N2, fun n m hn hm => by
    have : padicNorm p (f n - f m) < ε := hN2 _ (max_le_iff.1 hn).2 _ (max_le_iff.1 hm).2
    have : padicNorm p (f n - f m) < padicNorm p (f n) :=
lt_of_lt_of_le this hN1 _ (max_le_iff.1 hn).1
    have : padicNorm p (f n - f m) < max (padicNorm p (f n)) (padicNorm p (f m)) :=
      lt_max_iff.2 (Or.inl this)
    by_contra hne
    rw [← padicNorm.neg (f m)] at hne
    have hnam := add_eq_max_of_ne hne
    rw [padicNorm.neg]; rw [max_comm] at hnam
    rw [← hnam]; rw [sub_eq_add_neg]; rw [add_comm] at this
    apply _root_.lt_irrefl _ this⟩

/--
Definition of `stationaryPoint` / `stationaryPoint` 的定义

English:
definition stationaryPoint
  signature: {f : PadicSeq p} (hf : ¬f ≈ 0)
  body: Classical.choose stationary hf

中文:
定义 stationaryPoint
  签名: {f : PadicSeq p} (hf : ¬f ≈ 0)
  定义体: Classical.choose stationary hf

Depends on / 依赖: Classical, Classical.choose, stationary
-/
def stationaryPoint {f : PadicSeq p} (hf : ¬f ≈ 0) : Nat :=
Classical.choose stationary hf

/--
theorem `stationaryPoint_spec` / 定理 `stationaryPoint_spec`

English:
theorem stationaryPoint_spec
  given: {f : PadicSeq p} (hf : ¬f ≈ 0)
  proof: @(Classical.choose_spec <| stationary hf)

中文:
定理 stationaryPoint_spec
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0)
  证明: @(Classical.choose_spec <| stationary hf)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, stationary
-/
theorem stationaryPoint_spec {f : PadicSeq p} (hf : ¬f ≈ 0) :
    forall {m n},
      stationaryPoint hf <= m -> stationaryPoint hf <= n -> padicNorm p (f n) = padicNorm p (f m) :=
  @(Classical.choose_spec <| stationary hf)

open scoped Classical in
/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: (f : PadicSeq p)
  body: if hf : f ≈ 0 then 0 else padicNorm p (f (stationaryPoint hf))

中文:
定义 norm
  签名: (f : PadicSeq p)
  定义体: if hf : f ≈ 0 then 0 else padicNorm p (f (stationaryPoint hf))

Depends on / 依赖: padicNorm, stationaryPoint
-/
def norm (f : PadicSeq p) : Rat :=
  if hf : f ≈ 0 then 0 else padicNorm p (f (stationaryPoint hf))

/--
theorem `norm_zero_iff` / 定理 `norm_zero_iff`

English:
theorem norm_zero_iff
  given: (f : PadicSeq p)
  statement: f.norm = 0 ↔ f ≈ 0
  proof: by
  constructor
  · intro h
    by_contra hf
    unfold norm at h
    split_ifs at h
    apply hf
    intro ε hε
    exists stationaryPoint hf
    intro j hj
    have heq := stationaryPoint_spec hf le_rfl hj
    simpa [h, heq]
  · intro h
    simp [norm, h]

中文:
定理 norm_zero_iff
  条件: (f : PadicSeq p)
  结论: f.norm = 0 ↔ f ≈ 0
  证明: by
  constructor
  · intro h
    by_contra hf
    unfold norm at h
    split_ifs at h
    apply hf
    intro ε hε
    exists stationaryPoint hf
    intro j hj
    have heq := stationaryPoint_spec hf le_rfl hj
    simpa [h, heq]
  · intro h
    simp [norm, h]

Depends on / 依赖: le_rfl, split_ifs, stationaryPoint, stationaryPoint_spec
-/
theorem norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f ≈ 0 := by
  constructor
  · intro h
    by_contra hf
    unfold norm at h
    split_ifs at h
    apply hf
    intro ε hε
    exists stationaryPoint hf
    intro j hj
    have heq := stationaryPoint_spec hf le_rfl hj
    simpa [h, heq]
  · intro h
    simp [norm, h]

end

section Embedding

open CauSeq

variable {p : Nat} [Fact p.Prime]

/--
theorem `equiv_zero_of_val_eq_of_equiv_zero` / 定理 `equiv_zero_of_val_eq_of_equiv_zero`

English:
theorem equiv_zero_of_val_eq_of_equiv_zero
  statement: {f g : PadicSeq p}
  proof: fun ε hε =>
  let ⟨i, hi⟩ := hf _ hε
  ⟨i, fun j hj => by simpa [h] using hi _ hj⟩

中文:
定理 equiv_zero_of_val_eq_of_equiv_zero
  结论: {f g : PadicSeq p}
  证明: fun ε hε =>
  let ⟨i, hi⟩ := hf _ hε
  ⟨i, fun j hj => by simpa [h] using hi _ hj⟩
-/
theorem equiv_zero_of_val_eq_of_equiv_zero {f g : PadicSeq p}
    (h : forall k, padicNorm p (f k) = padicNorm p (g k)) (hf : f ≈ 0) : g ≈ 0 := fun ε hε =>
  let ⟨i, hi⟩ := hf _ hε
  ⟨i, fun j hj => by simpa [h] using hi _ hj⟩

/--
theorem `norm_nonzero_of_not_equiv_zero` / 定理 `norm_nonzero_of_not_equiv_zero`

English:
theorem norm_nonzero_of_not_equiv_zero
  given: {f : PadicSeq p} (hf : ¬f ≈ 0)
  statement: f.norm != 0
  proof: hf ∘ f.norm_zero_iff.1

中文:
定理 norm_nonzero_of_not_equiv_zero
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0)
  结论: f.norm != 0
  证明: hf ∘ f.norm_zero_iff.1

Depends on / 依赖: f.norm_zero_iff, norm_zero_iff
-/
theorem norm_nonzero_of_not_equiv_zero {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm != 0 :=
  hf ∘ f.norm_zero_iff.1

/--
theorem `norm_eq_norm_app_of_nonzero` / 定理 `norm_eq_norm_app_of_nonzero`

English:
theorem norm_eq_norm_app_of_nonzero
  given: {f : PadicSeq p} (hf : ¬f ≈ 0)
  proof: have heq : f.norm = padicNorm p (f <| stationaryPoint hf) := by simp [norm, hf]
⟨f stationaryPoint hf, heq, fun h =>
    norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩

中文:
定理 norm_eq_norm_app_of_nonzero
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0)
  证明: have heq : f.norm = padicNorm p (f <| stationaryPoint hf) := by simp [norm, hf]
⟨f stationaryPoint hf, heq, fun h =>
    norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩

Depends on / 依赖: f.norm, norm_nonzero_of_not_equiv_zero, padicNorm, stationaryPoint
-/
theorem norm_eq_norm_app_of_nonzero {f : PadicSeq p} (hf : ¬f ≈ 0) :
    exists k, f.norm = padicNorm p k ∧ k != 0 :=
  have heq : f.norm = padicNorm p (f <| stationaryPoint hf) := by simp [norm, hf]
⟨f stationaryPoint hf, heq, fun h =>
    norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩

/--
theorem `not_limZero_const_of_nonzero` / 定理 `not_limZero_const_of_nonzero`

English:
theorem not_limZero_const_of_nonzero
  given: {q : Rat} (hq : q != 0)
  statement: ¬LimZero (const (padicNorm p) q)
  proof: fun h' => hq const_limZero.1 h'

中文:
定理 not_limZero_const_of_nonzero
  条件: {q : 有理数} (hq : q != 0)
  结论: ¬LimZero (const (padicNorm p) q)
  证明: fun h' => hq const_limZero.1 h'

Depends on / 依赖: const_limZero
-/
theorem not_limZero_const_of_nonzero {q : Rat} (hq : q != 0) : ¬LimZero (const (padicNorm p) q) :=
fun h' => hq const_limZero.1 h'

/--
theorem `not_equiv_zero_const_of_nonzero` / 定理 `not_equiv_zero_const_of_nonzero`

English:
theorem not_equiv_zero_const_of_nonzero
  given: {q : Rat} (hq : q != 0)
  statement: ¬const (padicNorm p) q ≈ 0
  proof: fun h : LimZero (const (padicNorm p) q - 0) =>
not_limZero_const_of_nonzero (p := p) hq by simpa using h

中文:
定理 not_equiv_zero_const_of_nonzero
  条件: {q : 有理数} (hq : q != 0)
  结论: ¬const (padicNorm p) q ≈ 0
  证明: fun h : LimZero (const (padicNorm p) q - 0) =>
not_limZero_const_of_nonzero (p := p) hq by simpa using h

Depends on / 依赖: LimZero, not_limZero_const_of_nonzero, padicNorm
-/
theorem not_equiv_zero_const_of_nonzero {q : Rat} (hq : q != 0) : ¬const (padicNorm p) q ≈ 0 :=
  fun h : LimZero (const (padicNorm p) q - 0) =>
not_limZero_const_of_nonzero (p := p) hq by simpa using h

/--
theorem `norm_nonneg` / 定理 `norm_nonneg`

English:
theorem norm_nonneg
  given: (f : PadicSeq p)
  statement: 0 <= f.norm
  proof: by
  classical exact if hf : f ≈ 0 then by simp [hf, norm] else by simp [norm, hf, padicNorm.nonneg]

中文:
定理 norm_nonneg
  条件: (f : PadicSeq p)
  结论: 0 <= f.norm
  证明: by
  classical exact if hf : f ≈ 0 then by simp [hf, norm] else by simp [norm, hf, padicNorm.nonneg]

Depends on / 依赖: classical, nonneg, padicNorm, padicNorm.nonneg
-/
theorem norm_nonneg (f : PadicSeq p) : 0 <= f.norm := by
  classical exact if hf : f ≈ 0 then by simp [hf, norm] else by simp [norm, hf, padicNorm.nonneg]

/--
theorem `lift_index_left_left` / 定理 `lift_index_left_left`

English:
theorem lift_index_left_left
  given: {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : Nat)
  proof: by
  apply stationaryPoint_spec hf
  · apply le_max_left
  · exact le_rfl

中文:
定理 lift_index_left_left
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : 自然数)
  证明: by
  apply stationaryPoint_spec hf
  · apply le_max_left
  · exact le_rfl

Depends on / 依赖: le_max_left, le_rfl, stationaryPoint_spec
-/
theorem lift_index_left_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : Nat) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max (stationaryPoint hf) (max v2 v3))) := by
  apply stationaryPoint_spec hf
  · apply le_max_left
  · exact le_rfl

/--
theorem `lift_index_left` / 定理 `lift_index_left`

English:
theorem lift_index_left
  given: {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : Nat)
  proof: by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_left _ v3
    · apply le_max_right
  · exact le_rfl

中文:
定理 lift_index_left
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : 自然数)
  证明: by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_left _ v3
    · apply le_max_right
  · exact le_rfl

Depends on / 依赖: le_max_left, le_max_right, le_rfl, le_trans, stationaryPoint_spec
-/
theorem lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : Nat) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max v1 (max (stationaryPoint hf) v3))) := by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_left _ v3
    · apply le_max_right
  · exact le_rfl

/--
theorem `lift_index_right` / 定理 `lift_index_right`

English:
theorem lift_index_right
  given: {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : Nat)
  proof: by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_right v2
    · apply le_max_right
  · exact le_rfl

中文:
定理 lift_index_right
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : 自然数)
  证明: by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_right v2
    · apply le_max_right
  · exact le_rfl

Depends on / 依赖: le_max_right, le_rfl, le_trans, stationaryPoint_spec
-/
theorem lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : Nat) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max v1 (max v2 (stationaryPoint hf)))) := by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_right v2
    · apply le_max_right
  · exact le_rfl

end Embedding

section Valuation

open CauSeq

variable {p : Nat} [Fact p.Prime]

/-! ### Valuation on `PadicSeq` -/

open scoped Classical in
/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: (f : PadicSeq p)
  body: if hf : f ≈ 0 then 0 else padicValRat p (f (stationaryPoint hf))

中文:
定义 valuation
  签名: (f : PadicSeq p)
  定义体: if hf : f ≈ 0 then 0 else padicValRat p (f (stationaryPoint hf))

Depends on / 依赖: padicValRat, stationaryPoint
-/
def valuation (f : PadicSeq p) : Int :=
  if hf : f ≈ 0 then 0 else padicValRat p (f (stationaryPoint hf))

/--
theorem `norm_eq_zpow_neg_valuation` / 定理 `norm_eq_zpow_neg_valuation`

English:
theorem norm_eq_zpow_neg_valuation
  given: {f : PadicSeq p} (hf : ¬f ≈ 0)
  proof: by
  rw [norm]; rw [valuation]; rw [dif_neg hf]; rw [dif_neg hf]; rw [padicNorm]; rw [if_neg]
  intro H
  apply CauSeq.not_limZero_of_not_congr_zero hf
  intro ε hε
  use stationaryPoint hf
  intro n hn
  rw [stationaryPoint_spec hf le_rfl hn]
  simpa [H] using hε

中文:
定理 norm_eq_zpow_neg_valuation
  条件: {f : PadicSeq p} (hf : ¬f ≈ 0)
  证明: by
  rw [norm]; rw [valuation]; rw [dif_neg hf]; rw [dif_neg hf]; rw [padicNorm]; rw [if_neg]
  intro H
  apply CauSeq.not_limZero_of_not_congr_zero hf
  intro ε hε
  use stationaryPoint hf
  intro n hn
  rw [stationaryPoint_spec hf le_rfl hn]
  simpa [H] using hε

Depends on / 依赖: CauSeq, CauSeq.not_limZero_of_not_congr_zero, dif_neg, if_neg, le_rfl, not_limZero_of_not_congr_zero, padicNorm, stationaryPoint, stationaryPoint_spec, valuation
-/
theorem norm_eq_zpow_neg_valuation {f : PadicSeq p} (hf : ¬f ≈ 0) :
    f.norm = (p : Rat) ^ (-f.valuation : Int) := by
  rw [norm]; rw [valuation]; rw [dif_neg hf]; rw [dif_neg hf]; rw [padicNorm]; rw [if_neg]
  intro H
  apply CauSeq.not_limZero_of_not_congr_zero hf
  intro ε hε
  use stationaryPoint hf
  intro n hn
  rw [stationaryPoint_spec hf le_rfl hn]
  simpa [H] using hε

/--
theorem `val_eq_iff_norm_eq` / 定理 `val_eq_iff_norm_eq`

English:
theorem val_eq_iff_norm_eq
  given: {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0)
  proof: by
  rw [norm_eq_zpow_neg_valuation hf]; rw [norm_eq_zpow_neg_valuation hg]; rw [← neg_inj]; rw [zpow_right_inj₀]
  · exact mod_cast (Fact.out : p.Prime).pos
  · exact mod_cast (Fact.out : p.Prime).ne_one

中文:
定理 val_eq_iff_norm_eq
  条件: {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0)
  证明: by
  rw [norm_eq_zpow_neg_valuation hf]; rw [norm_eq_zpow_neg_valuation hg]; rw [← neg_inj]; rw [zpow_right_inj₀]
  · exact mod_cast (Fact.out : p.Prime).pos
  · exact mod_cast (Fact.out : p.Prime).ne_one

Depends on / 依赖: Fact.out, mod_cast, ne_one, neg_inj, norm_eq_zpow_neg_valuation, p.Prime
-/
theorem val_eq_iff_norm_eq {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) :
    f.valuation = g.valuation ↔ f.norm = g.norm := by
  rw [norm_eq_zpow_neg_valuation hf]; rw [norm_eq_zpow_neg_valuation hg]; rw [← neg_inj]; rw [zpow_right_inj₀]
  · exact mod_cast (Fact.out : p.Prime).pos
  · exact mod_cast (Fact.out : p.Prime).ne_one

end Valuation

end PadicSeq

-- Porting note: Commented out `padic_index_simp` tactic

/-
section

open PadicSeq

private unsafe def index_simp_core (hh hf hg : expr)
    (at_ : Interactive.Loc := Interactive.Loc.ns [none]) : tactic Unit := do
  let [v1, v2, v3] ← [hh, hf, hg].mapM fun n => tactic.mk_app `` stationary_point [n] <|> return n
  let e1 ← tactic.mk_app `` lift_index_left_left [hh, v2, v3] <|> return q(True)
  let e2 ← tactic.mk_app `` lift_index_left [hf, v1, v3] <|> return q(True)
  let e3 ← tactic.mk_app `` lift_index_right [hg, v1, v2] <|> return q(True)
  let sl ← [e1, e2, e3].foldlM (fun s e => simp_lemmas.add s e) simp_lemmas.mk
  when at_ (tactic.simp_target sl >> tactic.skip)
  let hs ← at_.get_locals
  hs (tactic.simp_hyp sl [])

/-- This is a special-purpose tactic that lifts `padicNorm (f (stationary_point f))` to
`padicNorm (f (max _ _ _))`. -/
unsafe def tactic.interactive.padic_index_simp (l : interactive.parse interactive.types.pexpr_list)
    (at_ : interactive.parse interactive.types.location) : tactic Unit := do
  let [h, f, g] ← l.mapM tactic.i_to_expr
  index_simp_core h f g at_

end
-/

namespace PadicSeq

section Embedding

open CauSeq

variable {p : Nat} [hp : Fact p.Prime]

/--
theorem `norm_mul` / 定理 `norm_mul`

English:
theorem norm_mul
  given: (f g : PadicSeq p)
  statement: (f * g).norm = f.norm * g.norm
  proof: by
  classical
  exact if hf : f ≈ 0 then by
    have hg : f * g ≈ 0 := mul_equiv_zero' _ hf
    simp only [hf, hg, norm, dif_pos, zero_mul]
  else
    if hg : g ≈ 0 then by
      have hf : f * g ≈ 0 := mul_equiv_zero _ hg
      simp only [hf, hg, norm, dif_pos, mul_zero]
    else by
      unfold no

中文:
定理 norm_mul
  条件: (f g : PadicSeq p)
  结论: (f * g).norm = f.norm * g.norm
  证明: by
  classical
  exact if hf : f ≈ 0 then by
    have hg : f * g ≈ 0 := mul_equiv_zero' _ hf
    simp only [hf, hg, norm, dif_pos, zero_mul]
  else
    if hg : g ≈ 0 then by
      have hf : f * g ≈ 0 := mul_equiv_zero _ hg
      simp only [hf, hg, norm, dif_pos, mul_zero]
    else by
      unfold no

Depends on / 依赖: classical, dif_pos, dite_false, mul_equiv_zero, mul_not_equiv_zero, mul_zero, zero_mul
-/
theorem norm_mul (f g : PadicSeq p) : (f * g).norm = f.norm * g.norm := by
  classical
  exact if hf : f ≈ 0 then by
    have hg : f * g ≈ 0 := mul_equiv_zero' _ hf
    simp only [hf, hg, norm, dif_pos, zero_mul]
  else
    if hg : g ≈ 0 then by
      have hf : f * g ≈ 0 := mul_equiv_zero _ hg
      simp only [hf, hg, norm, dif_pos, mul_zero]
    else by
      unfold norm
      have hfg := mul_not_equiv_zero hf hg
      simp only [hfg, hf, hg, dite_false]
      -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
      rw [lift_index_left_left hfg]; rw [lift_index_left hf]; rw [lift_index_right hg]
      apply padicNorm.mul

/--
theorem `eq_zero_iff_equiv_zero` / 定理 `eq_zero_iff_equiv_zero`

English:
theorem eq_zero_iff_equiv_zero
  given: (f : PadicSeq p)
  statement: mk f = 0 ↔ f ≈ 0
  proof: mk_eq

中文:
定理 eq_zero_iff_equiv_zero
  条件: (f : PadicSeq p)
  结论: mk f = 0 ↔ f ≈ 0
  证明: mk_eq

Depends on / 依赖: mk_eq
-/
theorem eq_zero_iff_equiv_zero (f : PadicSeq p) : mk f = 0 ↔ f ≈ 0 :=
  mk_eq

/--
theorem `ne_zero_iff_nequiv_zero` / 定理 `ne_zero_iff_nequiv_zero`

English:
theorem ne_zero_iff_nequiv_zero
  given: (f : PadicSeq p)
  statement: mk f != 0 ↔ ¬f ≈ 0
  proof: .not eq_zero_iff_equiv_zero _

中文:
定理 ne_zero_iff_nequiv_zero
  条件: (f : PadicSeq p)
  结论: mk f != 0 ↔ ¬f ≈ 0
  证明: .not eq_zero_iff_equiv_zero _

Depends on / 依赖: eq_zero_iff_equiv_zero
-/
theorem ne_zero_iff_nequiv_zero (f : PadicSeq p) : mk f != 0 ↔ ¬f ≈ 0 :=
.not eq_zero_iff_equiv_zero _

/--
theorem `norm_const` / 定理 `norm_const`

English:
theorem norm_const
  given: (q : Rat)
  statement: norm (const (padicNorm p) q) = padicNorm p q
  proof: by
  obtain rfl | hq := eq_or_ne q 0
  · simp [norm]
  · simp [norm, not_equiv_zero_const_of_nonzero hq]

中文:
定理 norm_const
  条件: (q : 有理数)
  结论: norm (const (padicNorm p) q) = padicNorm p q
  证明: by
  obtain rfl | hq := eq_or_ne q 0
  · simp [norm]
  · simp [norm, not_equiv_zero_const_of_nonzero hq]

Depends on / 依赖: eq_or_ne, not_equiv_zero_const_of_nonzero
-/
theorem norm_const (q : Rat) : norm (const (padicNorm p) q) = padicNorm p q := by
  obtain rfl | hq := eq_or_ne q 0
  · simp [norm]
  · simp [norm, not_equiv_zero_const_of_nonzero hq]

/--
theorem `norm_values_discrete` / 定理 `norm_values_discrete`

English:
theorem norm_values_discrete
  given: (a : PadicSeq p) (ha : ¬a ≈ 0)
  statement: exists z : Int, a.norm = (p : Rat) ^ (-z)
  proof: by
  let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha
  simpa [hk] using padicNorm.values_discrete hk'

中文:
定理 norm_values_discrete
  条件: (a : PadicSeq p) (ha : ¬a ≈ 0)
  结论: 存在 z : 整数, a.norm = (p : 有理数) ^ (-z)
  证明: by
  let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha
  simpa [hk] using padicNorm.values_discrete hk'

Depends on / 依赖: norm_eq_norm_app_of_nonzero, padicNorm, padicNorm.values_discrete, values_discrete
-/
theorem norm_values_discrete (a : PadicSeq p) (ha : ¬a ≈ 0) : exists z : Int, a.norm = (p : Rat) ^ (-z) := by
  let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha
  simpa [hk] using padicNorm.values_discrete hk'

/--
theorem `norm_one` / 定理 `norm_one`

English:
theorem norm_one
  statement: norm (1 : PadicSeq p) = 1
  proof: by
  have h1 : ¬(1 : PadicSeq p) ≈ 0 := one_not_equiv_zero _
  simp [h1, norm]

中文:
定理 norm_one
  结论: norm (1 : PadicSeq p) = 1
  证明: by
  have h1 : ¬(1 : PadicSeq p) ≈ 0 := one_not_equiv_zero _
  simp [h1, norm]

Depends on / 依赖: PadicSeq, one_not_equiv_zero
-/
theorem norm_one : norm (1 : PadicSeq p) = 1 := by
  have h1 : ¬(1 : PadicSeq p) ≈ 0 := one_not_equiv_zero _
  simp [h1, norm]

/--
theorem `norm_eq_of_equiv_aux` / 定理 `norm_eq_of_equiv_aux`

English:
theorem norm_eq_of_equiv_aux
  statement: {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
  proof: by
  have hpn : 0 < padicNorm p (f (stationaryPoint hf)) - padicNorm p (g (stationaryPoint hg)) :=
    sub_pos_of_lt hlt
  obtain ⟨N, hN⟩ := hfg _ hpn
  let i := max N (max (stationaryPoint hf) (stationaryPoint hg))
  have hi : N <= i := le_max_left _ _
  have hN' := hN _ hi
  -- Porting note: origi

中文:
定理 norm_eq_of_equiv_aux
  结论: {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
  证明: by
  have hpn : 0 < padicNorm p (f (stationaryPoint hf)) - padicNorm p (g (stationaryPoint hg)) :=
    sub_pos_of_lt hlt
  obtain ⟨N, hN⟩ := hfg _ hpn
  let i := max N (max (stationaryPoint hf) (stationaryPoint hg))
  have hi : N <= i := le_max_left _ _
  have hN' := hN _ hi
  -- Porting note: origi
-/
private theorem norm_eq_of_equiv_aux {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
    (h : padicNorm p (f (stationaryPoint hf)) != padicNorm p (g (stationaryPoint hg)))
    (hlt : padicNorm p (g (stationaryPoint hg)) < padicNorm p (f (stationaryPoint hf))) :
    False := by
  have hpn : 0 < padicNorm p (f (stationaryPoint hf)) - padicNorm p (g (stationaryPoint hg)) :=
    sub_pos_of_lt hlt
  obtain ⟨N, hN⟩ := hfg _ hpn
  let i := max N (max (stationaryPoint hf) (stationaryPoint hg))
  have hi : N <= i := le_max_left _ _
  have hN' := hN _ hi
  -- Porting note: originally `padic_index_simp [N, hf, hg] at hN' h hlt`
  rw [lift_index_left hf N (stationaryPoint hg)]; rw [lift_index_right hg N (stationaryPoint hf)]
    at hN' h hlt
  have hpne : padicNorm p (f i) != padicNorm p (-g i) := by rwa [← padicNorm.neg (g i)] at h
  rw [CauSeq.sub_apply]; rw [sub_eq_add_neg]; rw [add_eq_max_of_ne hpne]; rw [padicNorm.neg]; rw [max_eq_left_of_lt hlt]
    at hN'
  have : padicNorm p (f i) < padicNorm p (f i) := by
    apply lt_of_lt_of_le hN'
    apply sub_le_self
    apply padicNorm.nonneg
  exact lt_irrefl _ this

/--
theorem `norm_eq_of_equiv` / 定理 `norm_eq_of_equiv`

English:
theorem norm_eq_of_equiv
  given: {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
  proof: by
  by_contra h
  cases lt_or_ge (padicNorm p (g (stationaryPoint hg))) (padicNorm p (f (stationaryPoint hf))) with
  | inl hlt =>
    exact norm_eq_of_equiv_aux hf hg hfg h hlt
  | inr hle =>
    apply norm_eq_of_equiv_aux hg hf (Setoid.symm hfg) (Ne.symm h)
    exact lt_of_le_of_ne hle h

中文:
定理 norm_eq_of_equiv
  条件: {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
  证明: by
  by_contra h
  cases lt_or_ge (padicNorm p (g (stationaryPoint hg))) (padicNorm p (f (stationaryPoint hf))) with
  | inl hlt =>
    exact norm_eq_of_equiv_aux hf hg hfg h hlt
  | inr hle =>
    apply norm_eq_of_equiv_aux hg hf (Setoid.symm hfg) (Ne.symm h)
    exact lt_of_le_of_ne hle h
-/
private theorem norm_eq_of_equiv {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g) :
    padicNorm p (f (stationaryPoint hf)) = padicNorm p (g (stationaryPoint hg)) := by
  by_contra h
  cases lt_or_ge (padicNorm p (g (stationaryPoint hg))) (padicNorm p (f (stationaryPoint hf))) with
  | inl hlt =>
    exact norm_eq_of_equiv_aux hf hg hfg h hlt
  | inr hle =>
    apply norm_eq_of_equiv_aux hg hf (Setoid.symm hfg) (Ne.symm h)
    exact lt_of_le_of_ne hle h

/--
theorem `norm_equiv` / 定理 `norm_equiv`

English:
theorem norm_equiv
  given: {f g : PadicSeq p} (hfg : f ≈ g)
  statement: f.norm = g.norm
  proof: by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := Setoid.trans (Setoid.symm hfg) hf
    simp [norm, hf, hg]
  else by
    have hg : ¬g ≈ 0 := hf ∘ Setoid.trans hfg
    unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg

中文:
定理 norm_equiv
  条件: {f g : PadicSeq p} (hfg : f ≈ g)
  结论: f.norm = g.norm
  证明: by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := Setoid.trans (Setoid.symm hfg) hf
    simp [norm, hf, hg]
  else by
    have hg : ¬g ≈ 0 := hf ∘ Setoid.trans hfg
    unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg

Depends on / 依赖: Setoid, Setoid.symm, Setoid.trans, classical, norm_eq_of_equiv, split_ifs
-/
theorem norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.norm = g.norm := by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := Setoid.trans (Setoid.symm hfg) hf
    simp [norm, hf, hg]
  else by
    have hg : ¬g ≈ 0 := hf ∘ Setoid.trans hfg
    unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg

/--
theorem `norm_nonarchimedean_aux` / 定理 `norm_nonarchimedean_aux`

English:
theorem norm_nonarchimedean_aux
  statement: {f g : PadicSeq p} (hfg : ¬f + g ≈ 0) (hf : ¬f ≈ 0)
  proof: by
  unfold norm; split_ifs
  -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
  rw [lift_index_left_left hfg]; rw [lift_index_left hf]; rw [lift_index_right hg]
  apply padicNorm.nonarchimedean

中文:
定理 norm_nonarchimedean_aux
  结论: {f g : PadicSeq p} (hfg : ¬f + g ≈ 0) (hf : ¬f ≈ 0)
  证明: by
  unfold norm; split_ifs
  -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
  rw [lift_index_left_left hfg]; rw [lift_index_left hf]; rw [lift_index_right hg]
  apply padicNorm.nonarchimedean
-/
private theorem norm_nonarchimedean_aux {f g : PadicSeq p} (hfg : ¬f + g ≈ 0) (hf : ¬f ≈ 0)
    (hg : ¬g ≈ 0) : (f + g).norm <= max f.norm g.norm := by
  unfold norm; split_ifs
  -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
  rw [lift_index_left_left hfg]; rw [lift_index_left hf]; rw [lift_index_right hg]
  apply padicNorm.nonarchimedean

/--
theorem `norm_nonarchimedean` / 定理 `norm_nonarchimedean`

English:
theorem norm_nonarchimedean
  given: (f g : PadicSeq p)
  statement: (f + g).norm <= max f.norm g.norm
  proof: by
  classical
  exact if hfg : f + g ≈ 0 then by
    have : 0 <= max f.norm g.norm := le_max_of_le_left (norm_nonneg _)
    simpa only [hfg, norm]
  else
    if hf : f ≈ 0 then by
      have hfg' : f + g ≈ g := by
        change LimZero (f - 0) at hf
        change LimZero (f + g - g); · simpa only

中文:
定理 norm_nonarchimedean
  条件: (f g : PadicSeq p)
  结论: (f + g).norm <= 最大值 f.norm g.norm
  证明: by
  classical
  exact if hfg : f + g ≈ 0 then by
    have : 0 <= max f.norm g.norm := le_max_of_le_left (norm_nonneg _)
    simpa only [hfg, norm]
  else
    if hf : f ≈ 0 then by
      have hfg' : f + g ≈ g := by
        change LimZero (f - 0) at hf
        change LimZero (f + g - g); · simpa only

Depends on / 依赖: LimZero, add_sub_cancel_right, classical, f.norm, g.norm, le_max_of_le_left, max_eq_right, norm_equiv, norm_nonneg, norm_zero_iff, sub_zero
-/
theorem norm_nonarchimedean (f g : PadicSeq p) : (f + g).norm <= max f.norm g.norm := by
  classical
  exact if hfg : f + g ≈ 0 then by
    have : 0 <= max f.norm g.norm := le_max_of_le_left (norm_nonneg _)
    simpa only [hfg, norm]
  else
    if hf : f ≈ 0 then by
      have hfg' : f + g ≈ g := by
        change LimZero (f - 0) at hf
        change LimZero (f + g - g); · simpa only [sub_zero, add_sub_cancel_right] using hf
      have hcfg : (f + g).norm = g.norm := norm_equiv hfg'
      have hcl : f.norm = 0 := (norm_zero_iff f).2 hf
      have : max f.norm g.norm = g.norm := by rw [hcl]; exact max_eq_right (norm_nonneg _)
      rw [this]; rw [hcfg]
    else
      if hg : g ≈ 0 then by
        have hfg' : f + g ≈ f := by
          change LimZero (g - 0) at hg
          change LimZero (f + g - f); · simpa only [add_sub_cancel_left, sub_zero] using hg
        have hcfg : (f + g).norm = f.norm := norm_equiv hfg'
        have hcl : g.norm = 0 := (norm_zero_iff g).2 hg
        have : max f.norm g.norm = f.norm := by rw [hcl]; exact max_eq_left (norm_nonneg _)
        rw [this]; rw [hcfg]
      else norm_nonarchimedean_aux hfg hf hg

/--
theorem `norm_eq` / 定理 `norm_eq`

English:
theorem norm_eq
  given: {f g : PadicSeq p} (h : forall k, padicNorm p (f k) = padicNorm p (g k))
  proof: by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := equiv_zero_of_val_eq_of_equiv_zero h hf
    simp only [hf, hg, norm, dif_pos]
  else by
    have hg : ¬g ≈ 0 := fun hg =>
hf equiv_zero_of_val_eq_of_equiv_zero (by simp only [h, forall_const]) hg
    simp only [hg, hf, norm, dif_neg

中文:
定理 norm_eq
  条件: {f g : PadicSeq p} (h : 对任意 k, padicNorm p (f k) = padicNorm p (g k))
  证明: by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := equiv_zero_of_val_eq_of_equiv_zero h hf
    simp only [hf, hg, norm, dif_pos]
  else by
    have hg : ¬g ≈ 0 := fun hg =>
hf equiv_zero_of_val_eq_of_equiv_zero (by simp only [h, forall_const]) hg
    simp only [hg, hf, norm, dif_neg

Depends on / 依赖: classical, dif_neg, dif_pos, equiv_zero_of_val_eq_of_equiv_zero, forall_const, le_max_left, le_rfl, not_false_iff, padicNorm, stationaryPoint, stationaryPoint_spec
-/
theorem norm_eq {f g : PadicSeq p} (h : forall k, padicNorm p (f k) = padicNorm p (g k)) :
    f.norm = g.norm := by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := equiv_zero_of_val_eq_of_equiv_zero h hf
    simp only [hf, hg, norm, dif_pos]
  else by
    have hg : ¬g ≈ 0 := fun hg =>
hf equiv_zero_of_val_eq_of_equiv_zero (by simp only [h, forall_const]) hg
    simp only [hg, hf, norm, dif_neg, not_false_iff]
    let i := max (stationaryPoint hf) (stationaryPoint hg)
    have hpf : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f i) := by
      apply stationaryPoint_spec
      · apply le_max_left
      · exact le_rfl
    have hpg : padicNorm p (g (stationaryPoint hg)) = padicNorm p (g i) := by
      apply stationaryPoint_spec
      · apply le_max_right
      · exact le_rfl
    rw [hpf]; rw [hpg]; rw [h]

/--
theorem `norm_neg` / 定理 `norm_neg`

English:
theorem norm_neg
  given: (a : PadicSeq p)
  statement: (-a).norm = a.norm
  proof: norm_eq by simp

中文:
定理 norm_neg
  条件: (a : PadicSeq p)
  结论: (-a).norm = a.norm
  证明: norm_eq by simp

Depends on / 依赖: norm_eq
-/
theorem norm_neg (a : PadicSeq p) : (-a).norm = a.norm :=
norm_eq by simp

/--
theorem `norm_eq_of_add_equiv_zero` / 定理 `norm_eq_of_add_equiv_zero`

English:
theorem norm_eq_of_add_equiv_zero
  given: {f g : PadicSeq p} (h : f + g ≈ 0)
  statement: f.norm = g.norm
  proof: by
  have : LimZero (f + g - 0) := h
  have : f ≈ -g := show LimZero (f - -g) by simpa only [sub_zero, sub_neg_eq_add]
  have : f.norm = (-g).norm := norm_equiv this
  simpa only [norm_neg] using this

中文:
定理 norm_eq_of_add_equiv_zero
  条件: {f g : PadicSeq p} (h : f + g ≈ 0)
  结论: f.norm = g.norm
  证明: by
  have : LimZero (f + g - 0) := h
  have : f ≈ -g := show LimZero (f - -g) by simpa only [sub_zero, sub_neg_eq_add]
  have : f.norm = (-g).norm := norm_equiv this
  simpa only [norm_neg] using this

Depends on / 依赖: LimZero, f.norm, norm_equiv, norm_neg, sub_neg_eq_add, sub_zero
-/
theorem norm_eq_of_add_equiv_zero {f g : PadicSeq p} (h : f + g ≈ 0) : f.norm = g.norm := by
  have : LimZero (f + g - 0) := h
  have : f ≈ -g := show LimZero (f - -g) by simpa only [sub_zero, sub_neg_eq_add]
  have : f.norm = (-g).norm := norm_equiv this
  simpa only [norm_neg] using this

/--
theorem `add_eq_max_of_ne` / 定理 `add_eq_max_of_ne`

English:
theorem add_eq_max_of_ne
  given: {f g : PadicSeq p} (hfgne : f.norm != g.norm)
  proof: by
  classical
  have hfg : ¬f + g ≈ 0 := mt norm_eq_of_add_equiv_zero hfgne
  exact if hf : f ≈ 0 then by
    have : LimZero (f - 0) := hf
    have : f + g ≈ g := show LimZero (f + g - g) by simpa only [sub_zero, add_sub_cancel_right]
    have h1 : (f + g).norm = g.norm := norm_equiv this
    have 

中文:
定理 add_eq_max_of_ne
  条件: {f g : PadicSeq p} (hfgne : f.norm != g.norm)
  证明: by
  classical
  have hfg : ¬f + g ≈ 0 := mt norm_eq_of_add_equiv_zero hfgne
  exact if hf : f ≈ 0 then by
    have : LimZero (f - 0) := hf
    have : f + g ≈ g := show LimZero (f + g - g) by simpa only [sub_zero, add_sub_cancel_right]
    have h1 : (f + g).norm = g.norm := norm_equiv this
    have 

Depends on / 依赖: LimZero, add_sub_canc, add_sub_cancel_right, classical, f.norm, g.norm, max_eq_right, norm_eq_of_add_equiv_zero, norm_equiv, norm_nonneg, norm_zero_iff, sub_zero
-/
theorem add_eq_max_of_ne {f g : PadicSeq p} (hfgne : f.norm != g.norm) :
    (f + g).norm = max f.norm g.norm := by
  classical
  have hfg : ¬f + g ≈ 0 := mt norm_eq_of_add_equiv_zero hfgne
  exact if hf : f ≈ 0 then by
    have : LimZero (f - 0) := hf
    have : f + g ≈ g := show LimZero (f + g - g) by simpa only [sub_zero, add_sub_cancel_right]
    have h1 : (f + g).norm = g.norm := norm_equiv this
    have h2 : f.norm = 0 := (norm_zero_iff _).2 hf
    rw [h1]; rw [h2]; rw [max_eq_right (norm_nonneg _)]
  else
    if hg : g ≈ 0 then by
      have : LimZero (g - 0) := hg
      have : f + g ≈ f := show LimZero (f + g - f) by simpa only [add_sub_cancel_left, sub_zero]
      have h1 : (f + g).norm = f.norm := norm_equiv this
      have h2 : g.norm = 0 := (norm_zero_iff _).2 hg
      rw [h1]; rw [h2]; rw [max_eq_left (norm_nonneg _)]
    else by
      unfold norm at hfgne ⊢; split_ifs at hfgne ⊢
      -- Porting note: originally `padic_index_simp [hfg, hf, hg] at hfgne ⊢`
      rw [lift_index_left hf]; rw [lift_index_right hg] at hfgne
      · rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
        exact padicNorm.add_eq_max_of_ne hfgne

end Embedding

end PadicSeq

/-- The `p`-adic numbers `ℚ_[p]` are the Cauchy completion of `ℚ` with respect to the `p`-adic norm.
-/
@[wikidata Q311627]
/--
Definition of `Padic` / `Padic` 的定义

English:
definition Padic
  signature: (p : Nat) [Fact p.Prime]
  body: CauSeq.Completion.Cauchy (padicNorm p)
deriving Zero, One, Add, Neg, Sub, Mul, Div, AddCommGroup, Ring, CommRing, Field, Inhabited

中文:
定义 Padic
  签名: (p : 自然数) [Fact p.素]
  定义体: CauSeq.Completion.Cauchy (padicNorm p)
deriving Zero, One, Add, Neg, Sub, Mul, Div, AddCommGroup, Ring, CommRing, Field, Inhabited

Depends on / 依赖: CauSeq, CauSeq.Completion.Cauchy, Cauchy, Completion, padicNorm
-/
def Padic (p : Nat) [Fact p.Prime] :=
  CauSeq.Completion.Cauchy (padicNorm p)
deriving Zero, One, Add, Neg, Sub, Mul, Div, AddCommGroup, Ring, CommRing, Field, Inhabited

/-- notation for p-padic rationals -/
notation "Rat_[" p "]" => Padic p

namespace Padic

section Completion

variable {p : Nat} [Fact p.Prime]

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : PadicSeq p -> Rat_[p]
  body: Quotient.mk'

中文:
定义 mk
  签名: : PadicSeq p -> Rat_[p]
  定义体: Quotient.mk'

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk : PadicSeq p -> Rat_[p] :=
  Quotient.mk'

variable (p)

/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: (0 : Rat_[p]) = ⟦0⟧
  proof: rfl

中文:
定理 zero_def
  结论: (0 : Rat_[p]) = ⟦0⟧
  证明: rfl
-/
theorem zero_def : (0 : Rat_[p]) = ⟦0⟧ := rfl

/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: {f g : PadicSeq p}
  statement: mk f = mk g ↔ f ≈ g
  proof: Quotient.eq'

中文:
定理 mk_eq
  条件: {f g : PadicSeq p}
  结论: mk f = mk g ↔ f ≈ g
  证明: Quotient.eq'

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq {f g : PadicSeq p} : mk f = mk g ↔ f ≈ g :=
  Quotient.eq'

/--
theorem `const_equiv` / 定理 `const_equiv`

English:
theorem const_equiv
  given: {q r : Rat}
  statement: const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r
  proof: ⟨fun heq => eq_of_sub_eq_zero const_limZero.1 heq, fun heq => by
    rw [heq]⟩

@[norm_cast]

中文:
定理 const_equiv
  条件: {q r : 有理数}
  结论: const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r
  证明: ⟨fun heq => eq_of_sub_eq_zero const_limZero.1 heq, fun heq => by
    rw [heq]⟩

@[norm_cast]

Depends on / 依赖: const_limZero, eq_of_sub_eq_zero
-/
theorem const_equiv {q r : Rat} : const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r :=
⟨fun heq => eq_of_sub_eq_zero const_limZero.1 heq, fun heq => by
    rw [heq]⟩

@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {q r : Rat}
  statement: (↑q : Rat_[p]) = ↑r ↔ q = r
  proof: ⟨(const_equiv p).1 ∘ Quotient.eq'.1, fun h => by rw [h]⟩

中文:
定理 coe_inj
  条件: {q r : 有理数}
  结论: (↑q : Rat_[p]) = ↑r ↔ q = r
  证明: ⟨(const_equiv p).1 ∘ Quotient.eq'.1, fun h => by rw [h]⟩

Depends on / 依赖: Quotient, Quotient.eq, const_equiv
-/
theorem coe_inj {q r : Rat} : (↑q : Rat_[p]) = ↑r ↔ q = r :=
  ⟨(const_equiv p).1 ∘ Quotient.eq'.1, fun h => by rw [h]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharZero Rat_[p]
  body: ⟨fun m n => by
    rw [← Rat.cast_natCast]
    norm_cast
    exact id⟩

@[norm_cast]

中文:
实例 :
  签名: 特征零 Rat_[p]
  定义体: ⟨fun m n => by
    rw [← Rat.cast_natCast]
    norm_cast
    exact id⟩

@[norm_cast]

Depends on / 依赖: Rat.cast_natCast, cast_natCast
-/
instance : CharZero Rat_[p] :=
  ⟨fun m n => by
    rw [← Rat.cast_natCast]
    norm_cast
    exact id⟩

@[norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: forall {x y : Rat}, (↑(x + y) : Rat_[p]) = ↑x + ↑y
  proof: Rat.cast_add _ _

@[norm_cast]

中文:
定理 coe_add
  结论: 对任意 {x y : 有理数}, (↑(x + y) : Rat_[p]) = ↑x + ↑y
  证明: Rat.cast_add _ _

@[norm_cast]

Depends on / 依赖: Rat.cast_add, cast_add
-/
theorem coe_add : forall {x y : Rat}, (↑(x + y) : Rat_[p]) = ↑x + ↑y :=
  Rat.cast_add _ _

@[norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: forall {x : Rat}, (↑(-x) : Rat_[p]) = -↑x
  proof: Rat.cast_neg _

@[norm_cast]

中文:
定理 coe_neg
  结论: 对任意 {x : 有理数}, (↑(-x) : Rat_[p]) = -↑x
  证明: Rat.cast_neg _

@[norm_cast]

Depends on / 依赖: Rat.cast_neg, cast_neg
-/
theorem coe_neg : forall {x : Rat}, (↑(-x) : Rat_[p]) = -↑x :=
  Rat.cast_neg _

@[norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: forall {x y : Rat}, (↑(x * y) : Rat_[p]) = ↑x * ↑y
  proof: Rat.cast_mul _ _

@[norm_cast]

中文:
定理 coe_mul
  结论: 对任意 {x y : 有理数}, (↑(x * y) : Rat_[p]) = ↑x * ↑y
  证明: Rat.cast_mul _ _

@[norm_cast]

Depends on / 依赖: Rat.cast_mul, cast_mul
-/
theorem coe_mul : forall {x y : Rat}, (↑(x * y) : Rat_[p]) = ↑x * ↑y :=
  Rat.cast_mul _ _

@[norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: forall {x y : Rat}, (↑(x - y) : Rat_[p]) = ↑x - ↑y
  proof: Rat.cast_sub _ _

@[norm_cast]

中文:
定理 coe_sub
  结论: 对任意 {x y : 有理数}, (↑(x - y) : Rat_[p]) = ↑x - ↑y
  证明: Rat.cast_sub _ _

@[norm_cast]

Depends on / 依赖: Rat.cast_sub, cast_sub
-/
theorem coe_sub : forall {x y : Rat}, (↑(x - y) : Rat_[p]) = ↑x - ↑y :=
  Rat.cast_sub _ _

@[norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  statement: forall {x y : Rat}, (↑(x / y) : Rat_[p]) = ↑x / ↑y
  proof: Rat.cast_div _ _

@[norm_cast]

中文:
定理 coe_div
  结论: 对任意 {x y : 有理数}, (↑(x / y) : Rat_[p]) = ↑x / ↑y
  证明: Rat.cast_div _ _

@[norm_cast]

Depends on / 依赖: Rat.cast_div, cast_div
-/
theorem coe_div : forall {x y : Rat}, (↑(x / y) : Rat_[p]) = ↑x / ↑y :=
  Rat.cast_div _ _

@[norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: (↑(1 : Rat) : Rat_[p]) = 1
  proof: rfl

@[norm_cast]

中文:
定理 coe_one
  结论: (↑(1 : 有理数) : Rat_[p]) = 1
  证明: rfl

@[norm_cast]
-/
theorem coe_one : (↑(1 : Rat) : Rat_[p]) = 1 := rfl

@[norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: (↑(0 : Rat) : Rat_[p]) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: (↑(0 : 有理数) : Rat_[p]) = 0
  证明: rfl
-/
theorem coe_zero : (↑(0 : Rat) : Rat_[p]) = 0 := rfl

end Completion

end Padic

/--
Definition of `padicNormE` / `padicNormE` 的定义

English:
definition padicNormE
  signature: {p : Nat} [hp : Fact p.Prime]
  body: Quotient.lift PadicSeq.norm @PadicSeq.norm_equiv _ _
map_mul' q r := Quotient.inductionOn₂ q r PadicSeq.norm_mul
nonneg' q := Quotient.inductionOn q PadicSeq.norm_nonneg
  eq_zero' q := Quotient.inductionOn q fun r => by
    rw [Padic.zero_def]; rw [Quotient.lift_mk]; rw [PadicSeq.norm_zero_iff r]
 

中文:
定义 padicNormE
  签名: {p : 自然数} [hp : Fact p.素]
  定义体: Quotient.lift PadicSeq.norm @PadicSeq.norm_equiv _ _
map_mul' q r := Quotient.inductionOn₂ q r PadicSeq.norm_mul
nonneg' q := Quotient.inductionOn q PadicSeq.norm_nonneg
  eq_zero' q := Quotient.inductionOn q fun r => by
    rw [Padic.zero_def]; rw [Quotient.lift_mk]; rw [PadicSeq.norm_zero_iff r]
 

Depends on / 依赖: PadicSeq, PadicSeq.norm, PadicSeq.norm_equiv, Quotient, Quotient.lift, norm_equiv
-/
def padicNormE {p : Nat} [hp : Fact p.Prime] : AbsoluteValue Rat_[p] Rat where
toFun := Quotient.lift PadicSeq.norm @PadicSeq.norm_equiv _ _
map_mul' q r := Quotient.inductionOn₂ q r PadicSeq.norm_mul
nonneg' q := Quotient.inductionOn q PadicSeq.norm_nonneg
  eq_zero' q := Quotient.inductionOn q fun r => by
    rw [Padic.zero_def]; rw [Quotient.lift_mk]; rw [PadicSeq.norm_zero_iff r]
    exact Quotient.eq.symm
  add_le' q r := by
    trans
      max ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) q)
        ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) r)
    · induction q, r using Quotient.inductionOn₂; apply PadicSeq.norm_nonarchimedean
    · apply max_le_add_of_nonneg
      · induction q using Quotient.inductionOn; apply PadicSeq.norm_nonneg
      · induction r using Quotient.inductionOn; apply PadicSeq.norm_nonneg

namespace padicNormE

section Embedding

open PadicSeq

variable {p : Nat} [Fact p.Prime]

/--
theorem `defn` / 定理 `defn`

English:
theorem defn
  given: (f : PadicSeq p) {ε : Rat} (hε : 0 < ε)
  proof: by
  dsimp [padicNormE]
  -- `change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε` also works, but is very slow
  suffices hyp : exists N, forall i >= N, (f - const _ (f i)).norm < ε by peel hyp with N; use N
  by_contra! h
  obtain ⟨N, hN⟩ := cauchy₂ f hε
  rcases h N with ⟨i, hi, hge⟩
  have hne : ¬

中文:
定理 defn
  条件: (f : PadicSeq p) {ε : 有理数} (hε : 0 < ε)
  证明: by
  dsimp [padicNormE]
  -- `change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε` also works, but is very slow
  suffices hyp : exists N, forall i >= N, (f - const _ (f i)).norm < ε by peel hyp with N; use N
  by_contra! h
  obtain ⟨N, hN⟩ := cauchy₂ f hε
  rcases h N with ⟨i, hi, hge⟩
  have hne : ¬

Depends on / 依赖: padicNormE
-/
theorem defn (f : PadicSeq p) {ε : Rat} (hε : 0 < ε) :
    exists N, forall i >= N, padicNormE (Padic.mk f - f i : Rat_[p]) < ε := by
  dsimp [padicNormE]
  -- `change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε` also works, but is very slow
  suffices hyp : exists N, forall i >= N, (f - const _ (f i)).norm < ε by peel hyp with N; use N
  by_contra! h
  obtain ⟨N, hN⟩ := cauchy₂ f hε
  rcases h N with ⟨i, hi, hge⟩
  have hne : ¬f - const (padicNorm p) (f i) ≈ 0 := fun h => by
    rw [PadicSeq.norm]; rw [dif_pos h] at hge
    exact not_lt_of_ge hge hε
  unfold PadicSeq.norm at hge; split_ifs at hge
  apply not_le_of_gt _ hge
  cases _root_.le_total N (stationaryPoint hne) with
  | inl hgen =>
    exact hN _ hgen _ hi
  | inr hngen =>
    have := stationaryPoint_spec hne le_rfl hngen
    rw [← this]
    exact hN _ le_rfl _ hi

/--
theorem `nonarchimedean'` / 定理 `nonarchimedean'`

English:
theorem nonarchimedean'
  given: (q r : Rat_[p])
  proof: Quotient.inductionOn₂ q r norm_nonarchimedean

中文:
定理 nonarchimedean'
  条件: (q r : Rat_[p])
  证明: Quotient.inductionOn₂ q r norm_nonarchimedean

Depends on / 依赖: Quotient, Quotient.inductionOn, norm_nonarchimedean
-/
theorem nonarchimedean' (q r : Rat_[p]) :
    padicNormE (q + r : Rat_[p]) <= max (padicNormE q) (padicNormE r) :=
Quotient.inductionOn₂ q r norm_nonarchimedean

/--
theorem `add_eq_max_of_ne'` / 定理 `add_eq_max_of_ne'`

English:
theorem add_eq_max_of_ne'
  given: {q r : Rat_[p]}
  proof: Quotient.inductionOn₂ q r fun _ _ => PadicSeq.add_eq_max_of_ne

@[simp]

中文:
定理 add_eq_max_of_ne'
  条件: {q r : Rat_[p]}
  证明: Quotient.inductionOn₂ q r fun _ _ => PadicSeq.add_eq_max_of_ne

@[simp]

Depends on / 依赖: PadicSeq, PadicSeq.add_eq_max_of_ne, Quotient, Quotient.inductionOn, add_eq_max_of_ne
-/
theorem add_eq_max_of_ne' {q r : Rat_[p]} :
    padicNormE q != padicNormE r -> padicNormE (q + r : Rat_[p]) = max (padicNormE q) (padicNormE r) :=
  Quotient.inductionOn₂ q r fun _ _ => PadicSeq.add_eq_max_of_ne

@[simp]
/--
theorem `eq_padic_norm'` / 定理 `eq_padic_norm'`

English:
theorem eq_padic_norm'
  given: (q : Rat)
  statement: padicNormE (q : Rat_[p]) = padicNorm p q
  proof: norm_const _

中文:
定理 eq_padic_norm'
  条件: (q : 有理数)
  结论: padicNormE (q : Rat_[p]) = padicNorm p q
  证明: norm_const _

Depends on / 依赖: norm_const
-/
theorem eq_padic_norm' (q : Rat) : padicNormE (q : Rat_[p]) = padicNorm p q :=
  norm_const _

/--
theorem `image'` / 定理 `image'`

English:
theorem image'
  given: {q : Rat_[p]}
  statement: q != 0 -> exists n : Int, padicNormE q = (p : Rat) ^ (-n)
  proof: Quotient.inductionOn q fun f hf =>
    have : ¬f ≈ 0 := (ne_zero_iff_nequiv_zero f).1 hf
    norm_values_discrete f this

中文:
定理 像'
  条件: {q : Rat_[p]}
  结论: q != 0 -> 存在 n : 整数, padicNormE q = (p : 有理数) ^ (-n)
  证明: Quotient.inductionOn q fun f hf =>
    have : ¬f ≈ 0 := (ne_zero_iff_nequiv_zero f).1 hf
    norm_values_discrete f this
-/
protected theorem image' {q : Rat_[p]} : q != 0 -> exists n : Int, padicNormE q = (p : Rat) ^ (-n) :=
  Quotient.inductionOn q fun f hf =>
    have : ¬f ≈ 0 := (ne_zero_iff_nequiv_zero f).1 hf
    norm_values_discrete f this

end Embedding

end padicNormE

namespace Padic

section Complete

open PadicSeq Padic

variable {p : Nat} [Fact p.Prime] (f : CauSeq _ (@padicNormE p _))

/--
theorem `rat_dense'` / 定理 `rat_dense'`

English:
theorem rat_dense'
  given: (q : Rat_[p]) {ε : Rat} (hε : 0 < ε)
  statement: exists r : Rat, padicNormE (q - r : Rat_[p]) < ε
  proof: Quotient.inductionOn q fun q' =>
    have : exists N, forall m >= N, forall n >= N, padicNorm p (q' m - q' n) < ε := cauchy₂ _ hε
    let ⟨N, hN⟩ := this
    ⟨q' N, by
      classical
      dsimp [padicNormE]
      convert_to! PadicSeq.norm (q' - const _ (q' N)) < ε -- `change` times out here.
     

中文:
定理 rat_dense'
  条件: (q : Rat_[p]) {ε : 有理数} (hε : 0 < ε)
  结论: 存在 r : 有理数, padicNormE (q - r : Rat_[p]) < ε
  证明: Quotient.inductionOn q fun q' =>
    have : exists N, forall m >= N, forall n >= N, padicNorm p (q' m - q' n) < ε := cauchy₂ _ hε
    let ⟨N, hN⟩ := this
    ⟨q' N, by
      classical
      dsimp [padicNormE]
      convert_to! PadicSeq.norm (q' - const _ (q' N)) < ε -- `change` times out here.
     

Depends on / 依赖: Decidable, Decidable.em, PadicSeq, PadicSeq.norm, Quotient, Quotient.inductionOn, classical, convert_to, dif_neg, dif_pos, inductionOn, padicNorm, padicNormE, stationaryPoint
-/
theorem rat_dense' (q : Rat_[p]) {ε : Rat} (hε : 0 < ε) : exists r : Rat, padicNormE (q - r : Rat_[p]) < ε :=
  Quotient.inductionOn q fun q' =>
    have : exists N, forall m >= N, forall n >= N, padicNorm p (q' m - q' n) < ε := cauchy₂ _ hε
    let ⟨N, hN⟩ := this
    ⟨q' N, by
      classical
      dsimp [padicNormE]
      convert_to! PadicSeq.norm (q' - const _ (q' N)) < ε -- `change` times out here.
      rcases Decidable.em (q' - const (padicNorm p) (q' N) ≈ 0) with heq | hne'
      · simpa only [heq, PadicSeq.norm, dif_pos]
      · simp only [PadicSeq.norm, dif_neg hne']
        change padicNorm p (q' _ - q' _) < ε
        rcases Decidable.em (stationaryPoint hne' <= N) with hle | hle
        · have := (stationaryPoint_spec hne' le_rfl hle).symm
          simp only [const_apply, CauSeq.sub_apply, padicNorm.zero, sub_self] at this
          simpa only [this]
        · exact hN _ (lt_of_not_ge hle).le _ le_rfl⟩

set_option backward.privateInPublic true in
/--
theorem `div_nat_pos` / 定理 `div_nat_pos`

English:
theorem div_nat_pos
  given: (n : Nat)
  statement: 0 < 1 / (n + 1 : Rat)
  proof: div_pos zero_lt_one (mod_cast succ_pos _)

中文:
定理 div_nat_pos
  条件: (n : 自然数)
  结论: 0 < 1 / (n + 1 : 有理数)
  证明: div_pos zero_lt_one (mod_cast succ_pos _)
-/
private theorem div_nat_pos (n : Nat) : 0 < 1 / (n + 1 : Rat) :=
  div_pos zero_lt_one (mod_cast succ_pos _)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `limSeq` / `limSeq` 的定义

English:
definition limSeq
  signature: : Nat -> Rat
  body: fun n => Classical.choose (rat_dense' (f n) (div_nat_pos n))

中文:
定义 limSeq
  签名: : 自然数 -> 有理数
  定义体: fun n => Classical.choose (rat_dense' (f n) (div_nat_pos n))

Depends on / 依赖: Classical, Classical.choose, div_nat_pos, rat_dense
-/
def limSeq : Nat -> Rat :=
  fun n => Classical.choose (rat_dense' (f n) (div_nat_pos n))

/--
theorem `exi_rat_seq_conv` / 定理 `exi_rat_seq_conv`

English:
theorem exi_rat_seq_conv
  given: {ε : Rat} (hε : 0 < ε)
  proof: by
  refine (exists_nat_gt (1 / ε)).imp fun N hN i hi => ?_
  have h := Classical.choose_spec (rat_dense' (f i) (div_nat_pos i))
  refine lt_of_lt_of_le h ((div_le_iff₀' <| mod_cast succ_pos _).mpr ?_)
  rw [right_distrib]
  apply le_add_of_le_of_nonneg
  · exact (div_le_iff₀ hε).mp (le_trans (le_of

中文:
定理 exi_rat_seq_conv
  条件: {ε : 有理数} (hε : 0 < ε)
  证明: by
  refine (exists_nat_gt (1 / ε)).imp fun N hN i hi => ?_
  have h := Classical.choose_spec (rat_dense' (f i) (div_nat_pos i))
  refine lt_of_lt_of_le h ((div_le_iff₀' <| mod_cast succ_pos _).mpr ?_)
  rw [right_distrib]
  apply le_add_of_le_of_nonneg
  · exact (div_le_iff₀ hε).mp (le_trans (le_of

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, div_nat_pos, exists_nat_gt, le_add_of_le_of_nonneg, le_of_lt, le_trans, lt_of_lt_of_le, mod_cast, rat_dense, right_distrib, succ_pos
-/
theorem exi_rat_seq_conv {ε : Rat} (hε : 0 < ε) :
    exists N, forall i >= N, padicNormE (f i - (limSeq f i : Rat_[p]) : Rat_[p]) < ε := by
  refine (exists_nat_gt (1 / ε)).imp fun N hN i hi => ?_
  have h := Classical.choose_spec (rat_dense' (f i) (div_nat_pos i))
  refine lt_of_lt_of_le h ((div_le_iff₀' <| mod_cast succ_pos _).mpr ?_)
  rw [right_distrib]
  apply le_add_of_le_of_nonneg
  · exact (div_le_iff₀ hε).mp (le_trans (le_of_lt hN) (mod_cast hi))
  · apply le_of_lt
    simpa

/--
theorem `exi_rat_seq_conv_cauchy` / 定理 `exi_rat_seq_conv_cauchy`

English:
theorem exi_rat_seq_conv_cauchy
  statement: IsCauSeq (padicNorm p) (limSeq f)
  proof: fun ε hε => by
  have hε3 : 0 < ε / 3 := div_pos hε (by simp)
  let ⟨N, hN⟩ := exi_rat_seq_conv f hε3
  let ⟨N2, hN2⟩ := f.cauchy₂ hε3
  exists max N N2
  intro j hj
  suffices
    padicNormE (limSeq f j - f (max N N2) + (f (max N N2) - limSeq f (max N N2)) : Rat_[p]) < ε by
    ring_nf at this
    

中文:
定理 exi_rat_seq_conv_cauchy
  结论: IsCauSeq (padicNorm p) (limSeq f)
  证明: fun ε hε => by
  have hε3 : 0 < ε / 3 := div_pos hε (by simp)
  let ⟨N, hN⟩ := exi_rat_seq_conv f hε3
  let ⟨N2, hN2⟩ := f.cauchy₂ hε3
  exists max N N2
  intro j hj
  suffices
    padicNormE (limSeq f j - f (max N N2) + (f (max N N2) - limSeq f (max N N2)) : Rat_[p]) < ε by
    ring_nf at this
    

Depends on / 依赖: Rat_, _root_, _root_.add_lt_add, add_le, add_lt_add, add_thirds, div_pos, eq_padic_norm, exi_rat_seq_conv, f.cauchy, limSeq, lt_of_le_of_lt, mod_cast, padicNormE, padicNormE.add_le, padicNormE.eq_padic_norm, ring_nf
-/
theorem exi_rat_seq_conv_cauchy : IsCauSeq (padicNorm p) (limSeq f) := fun ε hε => by
  have hε3 : 0 < ε / 3 := div_pos hε (by simp)
  let ⟨N, hN⟩ := exi_rat_seq_conv f hε3
  let ⟨N2, hN2⟩ := f.cauchy₂ hε3
  exists max N N2
  intro j hj
  suffices
    padicNormE (limSeq f j - f (max N N2) + (f (max N N2) - limSeq f (max N N2)) : Rat_[p]) < ε by
    ring_nf at this
    rw [← padicNormE.eq_padic_norm']
    exact mod_cast this
  apply lt_of_le_of_lt
  · apply padicNormE.add_le
  · rw [← add_thirds ε]
    apply _root_.add_lt_add
    · suffices padicNormE (limSeq f j - f j + (f j - f (max N N2)) : Rat_[p]) < ε / 3 + ε / 3 by
        simpa only [sub_add_sub_cancel]
      apply lt_of_le_of_lt
      · apply padicNormE.add_le
      · apply _root_.add_lt_add
        · rw [padicNormE.map_sub]
          apply mod_cast hN j
          exact le_of_max_le_left hj
        · exact hN2 _ (le_of_max_le_right hj) _ (le_max_right _ _)
    · apply mod_cast hN (max N N2)
      apply le_max_left

/--
Definition of `lim'` / `lim'` 的定义

English:
definition lim'
  signature: : PadicSeq p
  body: ⟨_, exi_rat_seq_conv_cauchy f⟩

中文:
定义 lim'
  签名: : PadicSeq p
  定义体: ⟨_, exi_rat_seq_conv_cauchy f⟩
-/
private def lim' : PadicSeq p :=
  ⟨_, exi_rat_seq_conv_cauchy f⟩

/--
Definition of `lim` / `lim` 的定义

English:
definition lim
  signature: : Rat_[p]
  body: ⟦lim' f⟧

中文:
定义 lim
  签名: : Rat_[p]
  定义体: ⟦lim' f⟧
-/
private def lim : Rat_[p] :=
  ⟦lim' f⟧

/--
theorem `complete'` / 定理 `complete'`

English:
theorem complete'
  statement: exists q : Rat_[p], forall ε > 0, exists N, forall i >= N, padicNormE (q - f i : Rat_[p]) < ε
  proof: ⟨lim f, fun ε hε => by
    obtain ⟨N, hN⟩ := exi_rat_seq_conv f (half_pos hε)
    obtain ⟨N2, hN2⟩ := padicNormE.defn (lim' f) (half_pos hε)
    refine ⟨max N N2, fun i hi => ?_⟩
    rw [← sub_add_sub_cancel _ (lim' f i : Rat_[p]) _]
    refine (padicNormE.add_le _ _).trans_lt ?_
    rw [← add_halve

中文:
定理 complete'
  结论: 存在 q : Rat_[p], 对任意 ε > 0, 存在 N, 对任意 i >= N, padicNormE (q - f i : Rat_[p]) < ε
  证明: ⟨lim f, fun ε hε => by
    obtain ⟨N, hN⟩ := exi_rat_seq_conv f (half_pos hε)
    obtain ⟨N2, hN2⟩ := padicNormE.defn (lim' f) (half_pos hε)
    refine ⟨max N N2, fun i hi => ?_⟩
    rw [← sub_add_sub_cancel _ (lim' f i : Rat_[p]) _]
    refine (padicNormE.add_le _ _).trans_lt ?_
    rw [← add_halve

Depends on / 依赖: Rat_, _root_, _root_.add_lt_add, add_halves, add_le, add_lt_add, exi_rat_seq_conv, half_pos, le_of_max_le_left, le_of_max_le_right, map_sub, padicNormE, padicNormE.add_le, padicNormE.defn, padicNormE.map_sub, sub_add_sub_cancel, trans_lt
-/
theorem complete' : exists q : Rat_[p], forall ε > 0, exists N, forall i >= N, padicNormE (q - f i : Rat_[p]) < ε :=
  ⟨lim f, fun ε hε => by
    obtain ⟨N, hN⟩ := exi_rat_seq_conv f (half_pos hε)
    obtain ⟨N2, hN2⟩ := padicNormE.defn (lim' f) (half_pos hε)
    refine ⟨max N N2, fun i hi => ?_⟩
    rw [← sub_add_sub_cancel _ (lim' f i : Rat_[p]) _]
    refine (padicNormE.add_le _ _).trans_lt ?_
    rw [← add_halves ε]
    apply _root_.add_lt_add
    · apply hN2 _ (le_of_max_le_right hi)
    · rw [padicNormE.map_sub]
      exact hN _ (le_of_max_le_left hi)⟩

/--
theorem `complete''` / 定理 `complete''`

English:
theorem complete''
  statement: exists q : Rat_[p], forall ε > 0, exists N, forall i >= N, padicNormE (f i - q : Rat_[p]) < ε
  proof: by
  obtain ⟨x, hx⟩ := complete' f
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun i hi => ?_⟩
  rw [padicNormE.map_sub]
  exact hN i hi

中文:
定理 complete''
  结论: 存在 q : Rat_[p], 对任意 ε > 0, 存在 N, 对任意 i >= N, padicNormE (f i - q : Rat_[p]) < ε
  证明: by
  obtain ⟨x, hx⟩ := complete' f
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun i hi => ?_⟩
  rw [padicNormE.map_sub]
  exact hN i hi

Depends on / 依赖: complete, map_sub, padicNormE, padicNormE.map_sub
-/
theorem complete'' : exists q : Rat_[p], forall ε > 0, exists N, forall i >= N, padicNormE (f i - q : Rat_[p]) < ε := by
  obtain ⟨x, hx⟩ := complete' f
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun i hi => ?_⟩
  rw [padicNormE.map_sub]
  exact hN i hi
end Complete

section NormedSpace

variable (p : Nat) [Fact p.Prime]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist Rat_[p]
  body: ⟨fun x y => padicNormE (x - y : Rat_[p])⟩

中文:
实例 :
  签名: Dist Rat_[p]
  定义体: ⟨fun x y => padicNormE (x - y : Rat_[p])⟩

Depends on / 依赖: Rat_, padicNormE
-/
instance : Dist Rat_[p] :=
  ⟨fun x y => padicNormE (x - y : Rat_[p])⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUltrametricDist Rat_[p]
  body: ⟨fun x y z => by simpa [dist] using padicNormE.nonarchimedean' (x - y) (y - z)⟩

中文:
实例 :
  签名: 是UltrametricDist Rat_[p]
  定义体: ⟨fun x y z => by simpa [dist] using padicNormE.nonarchimedean' (x - y) (y - z)⟩

Depends on / 依赖: nonarchimedean, padicNormE, padicNormE.nonarchimedean
-/
instance : IsUltrametricDist Rat_[p] :=
  ⟨fun x y z => by simpa [dist] using padicNormE.nonarchimedean' (x - y) (y - z)⟩

/--
Instance `metricSpace` / 实例 `metricSpace`

English:
instance metricSpace
  signature: : MetricSpace Rat_[p] where
  body: by simp [dist]
  dist := dist
  dist_comm x y := by simp [dist, ← padicNormE.map_neg (x - y : Rat_[p])]
  dist_triangle x y z := by
    dsimp [dist]
    exact mod_cast padicNormE.sub_le x y z
  eq_of_dist_eq_zero := by
    dsimp [dist]; intro _ _ h
    apply eq_of_sub_eq_zero
    apply padicNormE.eq

中文:
实例 metricSpace
  签名: : 度量空间 Rat_[p] where
  定义体: by simp [dist]
  dist := dist
  dist_comm x y := by simp [dist, ← padicNormE.map_neg (x - y : Rat_[p])]
  dist_triangle x y z := by
    dsimp [dist]
    exact mod_cast padicNormE.sub_le x y z
  eq_of_dist_eq_zero := by
    dsimp [dist]; intro _ _ h
    apply eq_of_sub_eq_zero
    apply padicNormE.eq

Depends on / 依赖: Rat_, dist_comm, dist_triangle, eq_of_dist_eq_zero, eq_of_sub_eq_zero, eq_zero, map_neg, mod_cast, padicNormE, padicNormE.eq_zero, padicNormE.map_neg, padicNormE.sub_le, sub_le
-/
instance metricSpace : MetricSpace Rat_[p] where
  dist_self := by simp [dist]
  dist := dist
  dist_comm x y := by simp [dist, ← padicNormE.map_neg (x - y : Rat_[p])]
  dist_triangle x y z := by
    dsimp [dist]
    exact mod_cast padicNormE.sub_le x y z
  eq_of_dist_eq_zero := by
    dsimp [dist]; intro _ _ h
    apply eq_of_sub_eq_zero
    apply padicNormE.eq_zero.1
    exact mod_cast h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Norm Rat_[p]
  body: ⟨fun x => padicNormE x⟩

中文:
实例 :
  签名: 范数 Rat_[p]
  定义体: ⟨fun x => padicNormE x⟩

Depends on / 依赖: padicNormE
-/
instance : Norm Rat_[p] :=
  ⟨fun x => padicNormE x⟩

/--
Instance `normedField` / 实例 `normedField`

English:
instance normedField
  signature: : NormedField Rat_[p] where
  body: by
    rw [add_comm]; rw [← sub_eq_add_neg]
    change ‖x - y‖ = ‖y - x‖
    have : y - x = (-1) * (x - y) := by ring
    simp only [this, Norm.norm, map_mul, map_neg_eq_map, AbsoluteValue.map_one, one_mul]
  norm_mul := by simp [Norm.norm, map_mul]
  norm := norm

中文:
实例 normedField
  签名: : 赋范域 Rat_[p] where
  定义体: by
    rw [add_comm]; rw [← sub_eq_add_neg]
    change ‖x - y‖ = ‖y - x‖
    have : y - x = (-1) * (x - y) := by ring
    simp only [this, Norm.norm, map_mul, map_neg_eq_map, AbsoluteValue.map_one, one_mul]
  norm_mul := by simp [Norm.norm, map_mul]
  norm := norm

Depends on / 依赖: AbsoluteValue, AbsoluteValue.map_one, Norm.norm, add_comm, map_mul, map_neg_eq_map, map_one, norm_mul, one_mul, sub_eq_add_neg
-/
instance normedField : NormedField Rat_[p] where
  dist_eq x y := by
    rw [add_comm]; rw [← sub_eq_add_neg]
    change ‖x - y‖ = ‖y - x‖
    have : y - x = (-1) * (x - y) := by ring
    simp only [this, Norm.norm, map_mul, map_neg_eq_map, AbsoluteValue.map_one, one_mul]
  norm_mul := by simp [Norm.norm, map_mul]
  norm := norm

/--
Instance `isAbsoluteValue` / 实例 `isAbsoluteValue`

English:
instance isAbsoluteValue
  signature: : IsAbsoluteValue fun a : Rat_[p] => ‖a‖ where
  body: norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := by simp [Norm.norm, map_mul]

中文:
实例 isAbsoluteValue
  签名: : 是绝对值 fun a : Rat_[p] => ‖a‖ where
  定义体: norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := by simp [Norm.norm, map_mul]

Depends on / 依赖: norm_nonneg
-/
instance isAbsoluteValue : IsAbsoluteValue fun a : Rat_[p] => ‖a‖ where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := by simp [Norm.norm, map_mul]

/--
theorem `rat_dense` / 定理 `rat_dense`

English:
theorem rat_dense
  given: (q : Rat_[p]) {ε : Real} (hε : 0 < ε)
  statement: exists r : Rat, ‖q - r‖ < ε
  proof: let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε
  let ⟨r, hr⟩ := rat_dense' q (ε := ε') (by simpa using hε'l)
  ⟨r, lt_trans (by simpa [Norm.norm] using hr) hε'r⟩

中文:
定理 rat_dense
  条件: (q : Rat_[p]) {ε : 实数} (hε : 0 < ε)
  结论: 存在 r : 有理数, ‖q - r‖ < ε
  证明: let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε
  let ⟨r, hr⟩ := rat_dense' q (ε := ε') (by simpa using hε'l)
  ⟨r, lt_trans (by simpa [Norm.norm] using hr) hε'r⟩

Depends on / 依赖: Norm.norm, exists_rat_btwn, lt_trans, rat_dense
-/
theorem rat_dense (q : Rat_[p]) {ε : Real} (hε : 0 < ε) : exists r : Rat, ‖q - r‖ < ε :=
  let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε
  let ⟨r, hr⟩ := rat_dense' q (ε := ε') (by simpa using hε'l)
  ⟨r, lt_trans (by simpa [Norm.norm] using hr) hε'r⟩

/--
lemma `denseRange_ratCast` / 引理 `denseRange_ratCast`

English:
lemma denseRange_ratCast
  statement: DenseRange ((↑) : Rat -> Rat_[p])
  proof: by
  intro x
  rw [Metric.mem_closure_range_iff]
  exact fun _ => Padic.rat_dense _ x

中文:
引理 denseRange_ratCast
  结论: DenseRange ((↑) : 有理数 -> Rat_[p])
  证明: by
  intro x
  rw [Metric.mem_closure_range_iff]
  exact fun _ => Padic.rat_dense _ x

Depends on / 依赖: Metric, Metric.mem_closure_range_iff, Padic.rat_dense, mem_closure_range_iff, rat_dense
-/
lemma denseRange_ratCast : DenseRange ((↑) : Rat -> Rat_[p]) := by
  intro x
  rw [Metric.mem_closure_range_iff]
  exact fun _ => Padic.rat_dense _ x

end NormedSpace

end Padic

namespace Padic

variable {p : Nat} [hp : Fact p.Prime]

section NormedSpace

/--
theorem `padicNormE.mul` / 定理 `padicNormE.mul`

English:
theorem padicNormE.mul
  given: (q r : Rat_[p])
  statement: ‖q * r‖ = ‖q‖ * ‖r‖
  proof: by simp [Norm.norm, map_mul]

中文:
定理 padicNormE.mul
  条件: (q r : Rat_[p])
  结论: ‖q * r‖ = ‖q‖ * ‖r‖
  证明: by simp [Norm.norm, map_mul]
-/
protected theorem padicNormE.mul (q r : Rat_[p]) : ‖q * r‖ = ‖q‖ * ‖r‖ := by simp [Norm.norm, map_mul]

/--
theorem `padicNormE.is_norm` / 定理 `padicNormE.is_norm`

English:
theorem padicNormE.is_norm
  given: (q : Rat_[p])
  statement: ↑(padicNormE q) = ‖q‖
  proof: rfl

中文:
定理 padicNormE.is_norm
  条件: (q : Rat_[p])
  结论: ↑(padicNormE q) = ‖q‖
  证明: rfl
-/
protected theorem padicNormE.is_norm (q : Rat_[p]) : ↑(padicNormE q) = ‖q‖ := rfl

/--
theorem `nonarchimedean` / 定理 `nonarchimedean`

English:
theorem nonarchimedean
  given: (q r : Rat_[p])
  statement: ‖q + r‖ <= max ‖q‖ ‖r‖
  proof: by
  dsimp [norm]
  exact mod_cast padicNormE.nonarchimedean' _ _

中文:
定理 nonarchimedean
  条件: (q r : Rat_[p])
  结论: ‖q + r‖ <= 最大值 ‖q‖ ‖r‖
  证明: by
  dsimp [norm]
  exact mod_cast padicNormE.nonarchimedean' _ _

Depends on / 依赖: mod_cast, nonarchimedean, padicNormE, padicNormE.nonarchimedean
-/
theorem nonarchimedean (q r : Rat_[p]) : ‖q + r‖ <= max ‖q‖ ‖r‖ := by
  dsimp [norm]
  exact mod_cast padicNormE.nonarchimedean' _ _

/--
theorem `add_eq_max_of_ne` / 定理 `add_eq_max_of_ne`

English:
theorem add_eq_max_of_ne
  given: {q r : Rat_[p]} (h : ‖q‖ != ‖r‖)
  statement: ‖q + r‖ = max ‖q‖ ‖r‖
  proof: by
  dsimp [norm] at h ⊢
  have : padicNormE q != padicNormE r := mod_cast h
  exact mod_cast padicNormE.add_eq_max_of_ne' this

@[simp]

中文:
定理 add_eq_max_of_ne
  条件: {q r : Rat_[p]} (h : ‖q‖ != ‖r‖)
  结论: ‖q + r‖ = 最大值 ‖q‖ ‖r‖
  证明: by
  dsimp [norm] at h ⊢
  have : padicNormE q != padicNormE r := mod_cast h
  exact mod_cast padicNormE.add_eq_max_of_ne' this

@[simp]

Depends on / 依赖: add_eq_max_of_ne, mod_cast, padicNormE, padicNormE.add_eq_max_of_ne
-/
theorem add_eq_max_of_ne {q r : Rat_[p]} (h : ‖q‖ != ‖r‖) : ‖q + r‖ = max ‖q‖ ‖r‖ := by
  dsimp [norm] at h ⊢
  have : padicNormE q != padicNormE r := mod_cast h
  exact mod_cast padicNormE.add_eq_max_of_ne' this

@[simp]
/--
theorem `eq_padicNorm` / 定理 `eq_padicNorm`

English:
theorem eq_padicNorm
  given: (q : Rat)
  statement: ‖(q : Rat_[p])‖ = padicNorm p q
  proof: by
  dsimp [norm]
  rw [← padicNormE.eq_padic_norm']

@[simp]

中文:
定理 eq_padicNorm
  条件: (q : 有理数)
  结论: ‖(q : Rat_[p])‖ = padicNorm p q
  证明: by
  dsimp [norm]
  rw [← padicNormE.eq_padic_norm']

@[simp]

Depends on / 依赖: eq_padic_norm, padicNormE, padicNormE.eq_padic_norm
-/
theorem eq_padicNorm (q : Rat) : ‖(q : Rat_[p])‖ = padicNorm p q := by
  dsimp [norm]
  rw [← padicNormE.eq_padic_norm']

@[simp]
/--
theorem `norm_p` / 定理 `norm_p`

English:
theorem norm_p
  statement: ‖(p : Rat_[p])‖ = (p : Real)⁻¹
  proof: by
  rw [← @Rat.cast_natCast Real _ p]
  rw [← @Rat.cast_natCast Rat_[p] _ p]
  simp [hp.1.ne_zero, norm, padicNorm, padicValRat, padicValInt, zpow_neg,
    -Rat.cast_natCast]

中文:
定理 norm_p
  结论: ‖(p : Rat_[p])‖ = (p : 实数)⁻¹
  证明: by
  rw [← @Rat.cast_natCast Real _ p]
  rw [← @Rat.cast_natCast Rat_[p] _ p]
  simp [hp.1.ne_zero, norm, padicNorm, padicValRat, padicValInt, zpow_neg,
    -Rat.cast_natCast]

Depends on / 依赖: Rat.cast_natCast, Rat_, cast_natCast, ne_zero, padicNorm, padicValInt, padicValRat, zpow_neg
-/
theorem norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹ := by
  rw [← @Rat.cast_natCast Real _ p]
  rw [← @Rat.cast_natCast Rat_[p] _ p]
  simp [hp.1.ne_zero, norm, padicNorm, padicValRat, padicValInt, zpow_neg,
    -Rat.cast_natCast]

/--
theorem `norm_p_lt_one` / 定理 `norm_p_lt_one`

English:
theorem norm_p_lt_one
  statement: ‖(p : Rat_[p])‖ < 1
  proof: by
  rw [norm_p]
exact inv_lt_one_of_one_lt₀ mod_cast hp.1.one_lt

@[simp high] -- Shortcut lemma with higher priority.

中文:
定理 norm_p_lt_one
  结论: ‖(p : Rat_[p])‖ < 1
  证明: by
  rw [norm_p]
exact inv_lt_one_of_one_lt₀ mod_cast hp.1.one_lt

@[simp high] -- Shortcut lemma with higher priority.

Depends on / 依赖: mod_cast, norm_p, one_lt
-/
theorem norm_p_lt_one : ‖(p : Rat_[p])‖ < 1 := by
  rw [norm_p]
exact inv_lt_one_of_one_lt₀ mod_cast hp.1.one_lt

@[simp high] -- Shortcut lemma with higher priority.
/--
theorem `norm_p_zpow` / 定理 `norm_p_zpow`

English:
theorem norm_p_zpow
  given: (n : Int)
  statement: ‖(p : Rat_[p]) ^ n‖ = (p : Real) ^ (-n)
  proof: by
  rw [norm_zpow]; rw [norm_p]; rw [zpow_neg]; rw [inv_zpow]

@[simp high] -- Shortcut lemma with higher priority.

中文:
定理 norm_p_zpow
  条件: (n : 整数)
  结论: ‖(p : Rat_[p]) ^ n‖ = (p : 实数) ^ (-n)
  证明: by
  rw [norm_zpow]; rw [norm_p]; rw [zpow_neg]; rw [inv_zpow]

@[simp high] -- Shortcut lemma with higher priority.

Depends on / 依赖: inv_zpow, norm_p, norm_zpow, zpow_neg
-/
theorem norm_p_zpow (n : Int) : ‖(p : Rat_[p]) ^ n‖ = (p : Real) ^ (-n) := by
  rw [norm_zpow]; rw [norm_p]; rw [zpow_neg]; rw [inv_zpow]

@[simp high] -- Shortcut lemma with higher priority.
/--
theorem `norm_p_pow` / 定理 `norm_p_pow`

English:
theorem norm_p_pow
  given: (n : Nat)
  statement: ‖(p : Rat_[p]) ^ n‖ = (p : Real) ^ (-n : Int)
  proof: by
  rw [← norm_p_zpow]; rw [zpow_natCast]

中文:
定理 norm_p_pow
  条件: (n : 自然数)
  结论: ‖(p : Rat_[p]) ^ n‖ = (p : 实数) ^ (-n : 整数)
  证明: by
  rw [← norm_p_zpow]; rw [zpow_natCast]

Depends on / 依赖: norm_p_zpow, zpow_natCast
-/
theorem norm_p_pow (n : Nat) : ‖(p : Rat_[p]) ^ n‖ = (p : Real) ^ (-n : Int) := by
  rw [← norm_p_zpow]; rw [zpow_natCast]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NontriviallyNormedField Rat_[p]
  body: { Padic.normedField p with
    non_trivial :=
      ⟨p⁻¹, by
        rw [norm_inv]; rw [norm_p]; rw [inv_inv]
        exact mod_cast hp.1.one_lt⟩ }

中文:
实例 :
  签名: NontriviallyNormedField Rat_[p]
  定义体: { Padic.normedField p with
    non_trivial :=
      ⟨p⁻¹, by
        rw [norm_inv]; rw [norm_p]; rw [inv_inv]
        exact mod_cast hp.1.one_lt⟩ }

Depends on / 依赖: Padic.normedField, inv_inv, mod_cast, non_trivial, norm_inv, norm_p, normedField, one_lt
-/
instance : NontriviallyNormedField Rat_[p] :=
  { Padic.normedField p with
    non_trivial :=
      ⟨p⁻¹, by
        rw [norm_inv]; rw [norm_p]; rw [inv_inv]
        exact mod_cast hp.1.one_lt⟩ }

/--
theorem `padicNormE.image` / 定理 `padicNormE.image`

English:
theorem padicNormE.image
  given: {q : Rat_[p]}
  statement: q != 0 -> exists n : Int, ‖q‖ = ↑((p : Rat) ^ (-n))
  proof: Quotient.inductionOn q fun f hf =>
    have : ¬f ≈ 0 := (PadicSeq.ne_zero_iff_nequiv_zero f).1 hf
    let ⟨n, hn⟩ := PadicSeq.norm_values_discrete f this
    ⟨n, by rw [← hn]; rfl⟩

中文:
定理 padicNormE.像
  条件: {q : Rat_[p]}
  结论: q != 0 -> 存在 n : 整数, ‖q‖ = ↑((p : 有理数) ^ (-n))
  证明: Quotient.inductionOn q fun f hf =>
    have : ¬f ≈ 0 := (PadicSeq.ne_zero_iff_nequiv_zero f).1 hf
    let ⟨n, hn⟩ := PadicSeq.norm_values_discrete f this
    ⟨n, by rw [← hn]; rfl⟩
-/
protected theorem padicNormE.image {q : Rat_[p]} : q != 0 -> exists n : Int, ‖q‖ = ↑((p : Rat) ^ (-n)) :=
  Quotient.inductionOn q fun f hf =>
    have : ¬f ≈ 0 := (PadicSeq.ne_zero_iff_nequiv_zero f).1 hf
    let ⟨n, hn⟩ := PadicSeq.norm_values_discrete f this
    ⟨n, by rw [← hn]; rfl⟩

/--
theorem `padicNormE.is_rat` / 定理 `padicNormE.is_rat`

English:
theorem padicNormE.is_rat
  given: (q : Rat_[p])
  statement: exists q' : Rat, ‖q‖ = q'
  proof: by
  classical
  exact if h : q = 0 then ⟨0, by simp [h]⟩
  else
    let ⟨n, hn⟩ := padicNormE.image h
    ⟨_, hn⟩

中文:
定理 padicNormE.is_rat
  条件: (q : Rat_[p])
  结论: 存在 q' : 有理数, ‖q‖ = q'
  证明: by
  classical
  exact if h : q = 0 then ⟨0, by simp [h]⟩
  else
    let ⟨n, hn⟩ := padicNormE.image h
    ⟨_, hn⟩
-/
protected theorem padicNormE.is_rat (q : Rat_[p]) : exists q' : Rat, ‖q‖ = q' := by
  classical
  exact if h : q = 0 then ⟨0, by simp [h]⟩
  else
    let ⟨n, hn⟩ := padicNormE.image h
    ⟨_, hn⟩

/--
Definition of `ratNorm` / `ratNorm` 的定义

English:
definition ratNorm
  signature: (q : Rat_[p])
  body: Classical.choose (padicNormE.is_rat q)

中文:
定义 ratNorm
  签名: (q : Rat_[p])
  定义体: Classical.choose (padicNormE.is_rat q)

Depends on / 依赖: Classical, Classical.choose, is_rat, padicNormE, padicNormE.is_rat
-/
def ratNorm (q : Rat_[p]) : Rat :=
  Classical.choose (padicNormE.is_rat q)

/--
theorem `eq_ratNorm` / 定理 `eq_ratNorm`

English:
theorem eq_ratNorm
  given: (q : Rat_[p])
  statement: ‖q‖ = ratNorm q
  proof: Classical.choose_spec (padicNormE.is_rat q)

中文:
定理 eq_ratNorm
  条件: (q : Rat_[p])
  结论: ‖q‖ = ratNorm q
  证明: Classical.choose_spec (padicNormE.is_rat q)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, is_rat, padicNormE, padicNormE.is_rat
-/
theorem eq_ratNorm (q : Rat_[p]) : ‖q‖ = ratNorm q :=
  Classical.choose_spec (padicNormE.is_rat q)

/--
theorem `norm_rat_le_one` / 定理 `norm_rat_le_one`

English:
theorem norm_rat_le_one
  statement: forall {q : Rat} (_ : ¬p ∣ q.den), ‖(q : Rat_[p])‖ <= 1
  proof: Rat.zero_iff_num_zero.mpr hnz
      norm_num [this]
    else by
      have hnz' : (⟨n, d, hn, hd⟩ : Rat) != 0 := mt Rat.zero_iff_num_zero.1 hnz
      rw [eq_padicNorm]
      norm_cast
      -- Porting note: `Nat.cast_zero` instead of another `norm_cast` call
      rw [padicNorm.eq_zpow_of_nonzero hn

中文:
定理 norm_rat_le_one
  结论: 对任意 {q : 有理数} (_ : ¬p ∣ q.den), ‖(q : Rat_[p])‖ <= 1
  证明: Rat.zero_iff_num_zero.mpr hnz
      norm_num [this]
    else by
      have hnz' : (⟨n, d, hn, hd⟩ : Rat) != 0 := mt Rat.zero_iff_num_zero.1 hnz
      rw [eq_padicNorm]
      norm_cast
      -- Porting note: `Nat.cast_zero` instead of another `norm_cast` call
      rw [padicNorm.eq_zpow_of_nonzero hn

Depends on / 依赖: Rat.zero_iff_num_zero.mpr, zero_iff_num_zero
-/
theorem norm_rat_le_one : forall {q : Rat} (_ : ¬p ∣ q.den), ‖(q : Rat_[p])‖ <= 1
  | ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d =>
    if hnz : n = 0 then by
      have : (⟨n, d, hn, hd⟩ : Rat) = 0 := Rat.zero_iff_num_zero.mpr hnz
      norm_num [this]
    else by
      have hnz' : (⟨n, d, hn, hd⟩ : Rat) != 0 := mt Rat.zero_iff_num_zero.1 hnz
      rw [eq_padicNorm]
      norm_cast
      -- Porting note: `Nat.cast_zero` instead of another `norm_cast` call
      rw [padicNorm.eq_zpow_of_nonzero hnz']; rw [padicValRat]; rw [neg_sub]; rw [padicValNat.eq_zero_of_not_dvd hq]; rw [Nat.cast_zero]; rw [zero_sub]; rw [zpow_neg]; rw [zpow_natCast]
      apply inv_le_one_of_one_le₀
      norm_cast
      apply one_le_pow
      exact hp.1.pos

/--
theorem `norm_int_le_one` / 定理 `norm_int_le_one`

English:
theorem norm_int_le_one
  given: (z : Int)
  statement: ‖(z : Rat_[p])‖ <= 1
  proof: suffices ‖((z : Rat) : Rat_[p])‖ <= 1 by simpa
norm_rat_le_one by simp [hp.1.ne_one]

@[simp]

中文:
定理 norm_int_le_one
  条件: (z : 整数)
  结论: ‖(z : Rat_[p])‖ <= 1
  证明: suffices ‖((z : Rat) : Rat_[p])‖ <= 1 by simpa
norm_rat_le_one by simp [hp.1.ne_one]

@[simp]

Depends on / 依赖: Rat_, ne_one, norm_rat_le_one
-/
theorem norm_int_le_one (z : Int) : ‖(z : Rat_[p])‖ <= 1 :=
  suffices ‖((z : Rat) : Rat_[p])‖ <= 1 by simpa
norm_rat_le_one by simp [hp.1.ne_one]

@[simp]
/--
theorem `norm_intCast_lt_one_iff` / 定理 `norm_intCast_lt_one_iff`

English:
theorem norm_intCast_lt_one_iff
  given: {k : Int}
  statement: ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k
  proof: by
  constructor
  · intro h
    contrapose! h
    apply le_of_eq
    rw [eq_comm]
    calc
      ‖(k : Rat_[p])‖ = ‖((k : Rat) : Rat_[p])‖ := by norm_cast
      _ = padicNorm p k := eq_padicNorm _
      _ = 1 := mod_cast (int_eq_one_iff k).mpr h
  · rintro ⟨x, rfl⟩
    push_cast
    rw [padicNormE.

中文:
定理 norm_intCast_lt_one_iff
  条件: {k : 整数}
  结论: ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k
  证明: by
  constructor
  · intro h
    contrapose! h
    apply le_of_eq
    rw [eq_comm]
    calc
      ‖(k : Rat_[p])‖ = ‖((k : Rat) : Rat_[p])‖ := by norm_cast
      _ = padicNorm p k := eq_padicNorm _
      _ = 1 := mod_cast (int_eq_one_iff k).mpr h
  · rintro ⟨x, rfl⟩
    push_cast
    rw [padicNormE.

Depends on / 依赖: Rat_, contrapose, eq_comm, eq_padicNorm, int_eq_one_iff, le_of_eq, le_rfl, mod_cast, mul_le_mul, mul_one, norm_int_le_one, norm_nonneg, norm_p, one_lt, padicNorm, padicNormE, padicNormE.mul
-/
theorem norm_intCast_lt_one_iff {k : Int} : ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k := by
  constructor
  · intro h
    contrapose! h
    apply le_of_eq
    rw [eq_comm]
    calc
      ‖(k : Rat_[p])‖ = ‖((k : Rat) : Rat_[p])‖ := by norm_cast
      _ = padicNorm p k := eq_padicNorm _
      _ = 1 := mod_cast (int_eq_one_iff k).mpr h
  · rintro ⟨x, rfl⟩
    push_cast
    rw [padicNormE.mul]
    calc
      _ <= ‖(p : Rat_[p])‖ * 1 :=
        mul_le_mul le_rfl (by simpa using norm_int_le_one _) (norm_nonneg _) (norm_nonneg _)
      _ < 1 := by
        rw [mul_one]; rw [norm_p]
exact inv_lt_one_of_one_lt₀ mod_cast hp.1.one_lt

@[simp]
/--
lemma `norm_natCast_lt_one_iff` / 引理 `norm_natCast_lt_one_iff`

English:
lemma norm_natCast_lt_one_iff
  given: {n : Nat}
  proof: by
  simpa [Int.natCast_dvd_natCast] using norm_intCast_lt_one_iff (p := p) (k := n)

@[simp]

中文:
引理 norm_natCast_lt_one_iff
  条件: {n : 自然数}
  证明: by
  simpa [Int.natCast_dvd_natCast] using norm_intCast_lt_one_iff (p := p) (k := n)

@[simp]

Depends on / 依赖: Int.natCast_dvd_natCast, natCast_dvd_natCast, norm_intCast_lt_one_iff
-/
lemma norm_natCast_lt_one_iff {n : Nat} :
    ‖(n : Rat_[p])‖ < 1 ↔ p ∣ n := by
  simpa [Int.natCast_dvd_natCast] using norm_intCast_lt_one_iff (p := p) (k := n)

@[simp]
/--
lemma `norm_intCast_eq_one_iff` / 引理 `norm_intCast_eq_one_iff`

English:
lemma norm_intCast_eq_one_iff
  given: {z : Int}
  proof: by
  rw [← not_iff_not]
  simp [Nat.coprime_comm, ← norm_natCast_lt_one_iff, -norm_intCast_lt_one_iff,
    Int.isCoprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, Int.gcd,
    ← hp.out.dvd_iff_not_coprime, norm_natAbs, -cast_natAbs, norm_int_le_one]

@[simp]

中文:
引理 norm_intCast_eq_one_iff
  条件: {z : 整数}
  证明: by
  rw [← not_iff_not]
  simp [Nat.coprime_comm, ← norm_natCast_lt_one_iff, -norm_intCast_lt_one_iff,
    Int.isCoprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, Int.gcd,
    ← hp.out.dvd_iff_not_coprime, norm_natAbs, -cast_natAbs, norm_int_le_one]

@[simp]

Depends on / 依赖: Int.gcd, Int.isCoprime_iff_gcd_eq_one, Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, cast_natAbs, coprime_comm, coprime_iff_gcd_eq_one, dvd_iff_not_coprime, hp.out.dvd_iff_not_coprime, isCoprime_iff_gcd_eq_one, norm_intCast_lt_one_iff, norm_int_le_one, norm_natAbs, norm_natCast_lt_one_iff, not_iff_not
-/
lemma norm_intCast_eq_one_iff {z : Int} :
    ‖(z : Rat_[p])‖ = 1 ↔ IsCoprime z p := by
  rw [← not_iff_not]
  simp [Nat.coprime_comm, ← norm_natCast_lt_one_iff, -norm_intCast_lt_one_iff,
    Int.isCoprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, Int.gcd,
    ← hp.out.dvd_iff_not_coprime, norm_natAbs, -cast_natAbs, norm_int_le_one]

@[simp]
/--
lemma `norm_natCast_eq_one_iff` / 引理 `norm_natCast_eq_one_iff`

English:
lemma norm_natCast_eq_one_iff
  given: {n : Nat}
  proof: by
  simpa [p.coprime_comm] using norm_intCast_eq_one_iff (p := p) (z := n)

中文:
引理 norm_natCast_eq_one_iff
  条件: {n : 自然数}
  证明: by
  simpa [p.coprime_comm] using norm_intCast_eq_one_iff (p := p) (z := n)

Depends on / 依赖: coprime_comm, norm_intCast_eq_one_iff, p.coprime_comm
-/
lemma norm_natCast_eq_one_iff {n : Nat} :
    ‖(n : Rat_[p])‖ = 1 ↔ p.Coprime n := by
  simpa [p.coprime_comm] using norm_intCast_eq_one_iff (p := p) (z := n)

/--
theorem `norm_int_le_pow_iff_dvd` / 定理 `norm_int_le_pow_iff_dvd`

English:
theorem norm_int_le_pow_iff_dvd
  given: (k : Int) (n : Nat)
  proof: by
  have : (p : Real) ^ (-n : Int) = (p : Rat) ^ (-n : Int) := by simp
  rw [show (k : Rat_[p]) = ((k : Rat) : Rat_[p]) by norm_cast, eq_padicNorm, this]
  norm_cast
  rw [← padicNorm.dvd_iff_norm_le]

中文:
定理 norm_int_le_pow_iff_dvd
  条件: (k : 整数) (n : 自然数)
  证明: by
  have : (p : Real) ^ (-n : Int) = (p : Rat) ^ (-n : Int) := by simp
  rw [show (k : Rat_[p]) = ((k : Rat) : Rat_[p]) by norm_cast, eq_padicNorm, this]
  norm_cast
  rw [← padicNorm.dvd_iff_norm_le]

Depends on / 依赖: Rat_, dvd_iff_norm_le, eq_padicNorm, padicNorm, padicNorm.dvd_iff_norm_le
-/
theorem norm_int_le_pow_iff_dvd (k : Int) (n : Nat) :
    ‖(k : Rat_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k := by
  have : (p : Real) ^ (-n : Int) = (p : Rat) ^ (-n : Int) := by simp
  rw [show (k : Rat_[p]) = ((k : Rat) : Rat_[p]) by norm_cast, eq_padicNorm, this]
  norm_cast
  rw [← padicNorm.dvd_iff_norm_le]

/--
theorem `norm_eq_of_norm_add_lt_right` / 定理 `norm_eq_of_norm_add_lt_right`

English:
theorem norm_eq_of_norm_add_lt_right
  given: {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z2‖)
  statement: ‖z1‖ = ‖z2‖
  proof: _root_.by_contradiction fun hne =>
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_right) h

中文:
定理 norm_eq_of_norm_add_lt_right
  条件: {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z2‖)
  结论: ‖z1‖ = ‖z2‖
  证明: _root_.by_contradiction fun hne =>
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_right) h

Depends on / 依赖: _root_, _root_.by_contradiction, add_eq_max_of_ne, by_contradiction, le_max_right, not_lt_of_ge
-/
theorem norm_eq_of_norm_add_lt_right {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  _root_.by_contradiction fun hne =>
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_right) h

/--
theorem `norm_eq_of_norm_add_lt_left` / 定理 `norm_eq_of_norm_add_lt_left`

English:
theorem norm_eq_of_norm_add_lt_left
  given: {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z1‖)
  statement: ‖z1‖ = ‖z2‖
  proof: _root_.by_contradiction fun hne =>
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_left) h

中文:
定理 norm_eq_of_norm_add_lt_left
  条件: {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z1‖)
  结论: ‖z1‖ = ‖z2‖
  证明: _root_.by_contradiction fun hne =>
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_left) h

Depends on / 依赖: _root_, _root_.by_contradiction, add_eq_max_of_ne, by_contradiction, le_max_left, not_lt_of_ge
-/
theorem norm_eq_of_norm_add_lt_left {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  _root_.by_contradiction fun hne =>
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_left) h

/--
theorem `norm_eq_of_norm_sub_lt_right` / 定理 `norm_eq_of_norm_sub_lt_right`

English:
theorem norm_eq_of_norm_sub_lt_right
  given: {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z2‖)
  statement: ‖z1‖ = ‖z2‖
  proof: by
  rw [← norm_neg z2]
  apply norm_eq_of_norm_add_lt_right
  simp [← sub_eq_add_neg, h]

中文:
定理 norm_eq_of_norm_sub_lt_right
  条件: {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z2‖)
  结论: ‖z1‖ = ‖z2‖
  证明: by
  rw [← norm_neg z2]
  apply norm_eq_of_norm_add_lt_right
  simp [← sub_eq_add_neg, h]

Depends on / 依赖: norm_eq_of_norm_add_lt_right, norm_neg, sub_eq_add_neg
-/
theorem norm_eq_of_norm_sub_lt_right {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ := by
  rw [← norm_neg z2]
  apply norm_eq_of_norm_add_lt_right
  simp [← sub_eq_add_neg, h]

/--
theorem `norm_eq_of_norm_sub_lt_left` / 定理 `norm_eq_of_norm_sub_lt_left`

English:
theorem norm_eq_of_norm_sub_lt_left
  given: {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z1‖)
  statement: ‖z1‖ = ‖z2‖
  proof: by
  rw [eq_comm]
  apply norm_eq_of_norm_sub_lt_right
  simpa [← norm_neg (z1 - _)] using h

@[simp]

中文:
定理 norm_eq_of_norm_sub_lt_left
  条件: {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z1‖)
  结论: ‖z1‖ = ‖z2‖
  证明: by
  rw [eq_comm]
  apply norm_eq_of_norm_sub_lt_right
  simpa [← norm_neg (z1 - _)] using h

@[simp]

Depends on / 依赖: eq_comm, norm_eq_of_norm_sub_lt_right, norm_neg
-/
theorem norm_eq_of_norm_sub_lt_left {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ := by
  rw [eq_comm]
  apply norm_eq_of_norm_sub_lt_right
  simpa [← norm_neg (z1 - _)] using h

@[simp]
/--
lemma `norm_natCast_p_sub_one` / 引理 `norm_natCast_p_sub_one`

English:
lemma norm_natCast_p_sub_one
  proof: by
  rw [norm_natCast_eq_one_iff]
  exact (coprime_self_sub_right hp.out.one_le).mpr p.coprime_one_right

中文:
引理 norm_natCast_p_sub_one
  证明: by
  rw [norm_natCast_eq_one_iff]
  exact (coprime_self_sub_right hp.out.one_le).mpr p.coprime_one_right

Depends on / 依赖: coprime_one_right, coprime_self_sub_right, hp.out.one_le, norm_natCast_eq_one_iff, one_le, p.coprime_one_right
-/
lemma norm_natCast_p_sub_one :
    ‖((p - 1 : Nat) : Rat_[p])‖ = 1 := by
  rw [norm_natCast_eq_one_iff]
  exact (coprime_self_sub_right hp.out.one_le).mpr p.coprime_one_right

end NormedSpace

/--
Instance `complete` / 实例 `complete`

English:
instance complete
  signature: : CauSeq.IsComplete Rat_[p] norm where
  body: by
    have cau_seq_norm_e : IsCauSeq padicNormE f := fun ε hε => by
      have h := isCauSeq f ε (mod_cast hε)
      dsimp [norm] at h
      exact mod_cast h
    -- Porting note: Padic.complete' works with `f i - q`, but the goal needs `q - f i`,
    -- using `rewrite [padicNormE.map_sub]` causes t

中文:
实例 complete
  签名: : CauSeq.是完备 Rat_[p] norm where
  定义体: by
    have cau_seq_norm_e : IsCauSeq padicNormE f := fun ε hε => by
      have h := isCauSeq f ε (mod_cast hε)
      dsimp [norm] at h
      exact mod_cast h
    -- Porting note: Padic.complete' works with `f i - q`, but the goal needs `q - f i`,
    -- using `rewrite [padicNormE.map_sub]` causes t

Depends on / 依赖: IsCauSeq, cau_seq_norm_e, isCauSeq, mod_cast, padicNormE
-/
instance complete : CauSeq.IsComplete Rat_[p] norm where
  isComplete f := by
    have cau_seq_norm_e : IsCauSeq padicNormE f := fun ε hε => by
      have h := isCauSeq f ε (mod_cast hε)
      dsimp [norm] at h
      exact mod_cast h
    -- Porting note: Padic.complete' works with `f i - q`, but the goal needs `q - f i`,
    -- using `rewrite [padicNormE.map_sub]` causes time out, so a separate lemma is created
    obtain ⟨q, hq⟩ := Padic.complete'' ⟨f, cau_seq_norm_e⟩
    exists q
    intro ε hε
    obtain ⟨ε', hε'⟩ := exists_rat_btwn hε
    norm_cast at hε'
    obtain ⟨N, hN⟩ := hq ε' hε'.1
    exists N
    intro i hi
    have h := hN i hi
    change norm (f i - q) < ε
    refine lt_trans ?_ hε'.2
    dsimp [norm]
    exact mod_cast h

/--
theorem `padicNormE_lim_le` / 定理 `padicNormE_lim_le`

English:
theorem padicNormE_lim_le
  given: {f : CauSeq Rat_[p] norm} {a : Real} (ha : 0 < a) (hf : forall i, ‖f i‖ <= a)
  proof: by
  obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ ha
  calc
    ‖f.lim‖ = ‖f.lim - f N + f N‖ := by simp
    _ <= max ‖f.lim - f N‖ ‖f N‖ := nonarchimedean _ _
    _ <= a := max_le (le_of_lt (hN _ le_rfl)) (hf _)

中文:
定理 padicNormE_lim_le
  条件: {f : CauSeq Rat_[p] norm} {a : 实数} (ha : 0 < a) (hf : 对任意 i, ‖f i‖ <= a)
  证明: by
  obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ ha
  calc
    ‖f.lim‖ = ‖f.lim - f N + f N‖ := by simp
    _ <= max ‖f.lim - f N‖ ‖f N‖ := nonarchimedean _ _
    _ <= a := max_le (le_of_lt (hN _ le_rfl)) (hf _)

Depends on / 依赖: CauSeq, CauSeq.equiv_lim, Setoid, Setoid.symm, equiv_lim, f.lim, le_of_lt, le_rfl, max_le, nonarchimedean
-/
theorem padicNormE_lim_le {f : CauSeq Rat_[p] norm} {a : Real} (ha : 0 < a) (hf : forall i, ‖f i‖ <= a) :
    ‖f.lim‖ <= a := by
  obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ ha
  calc
    ‖f.lim‖ = ‖f.lim - f N + f N‖ := by simp
    _ <= max ‖f.lim - f N‖ ‖f N‖ := nonarchimedean _ _
    _ <= a := max_le (le_of_lt (hN _ le_rfl)) (hf _)

open Filter Set

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace Rat_[p]
  body: by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq Rat_[p] norm := ⟨u, Metric.cauchySeq_iff'.mp hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn =>

中文:
实例 :
  签名: 完备空间 Rat_[p]
  定义体: by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq Rat_[p] norm := ⟨u, Metric.cauchySeq_iff'.mp hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn =>

Depends on / 依赖: CauSeq, Metric, Metric.cauchySeq_iff, Metric.mem_nhds_iff, Rat_, c.equiv_lim, c.lim, cauchySeq_iff, complete_of_cauchySeq_tendsto, equiv_lim, mem_atTop_sets, mem_map, mem_nhds_iff, this.imp
-/
instance : CompleteSpace Rat_[p] := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq Rat_[p] norm := ⟨u, Metric.cauchySeq_iff'.mp hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn => hε (hN n hn)

/-! ### Valuation on `ℚ_[p]` -/


/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Rat_[p] -> Int
  body: Quotient.lift (@PadicSeq.valuation p _) fun f g h => by
    by_cases hf : f ≈ 0
    · have hg : g ≈ 0 := Setoid.trans (Setoid.symm h) hf
      simp [hf, hg, PadicSeq.valuation]
    · have hg : ¬g ≈ 0 := fun hg => hf (Setoid.trans h hg)
      rw [PadicSeq.val_eq_iff_norm_eq hf hg]
      exact PadicSe

中文:
定义 valuation
  签名: : Rat_[p] -> 整数
  定义体: Quotient.lift (@PadicSeq.valuation p _) fun f g h => by
    by_cases hf : f ≈ 0
    · have hg : g ≈ 0 := Setoid.trans (Setoid.symm h) hf
      simp [hf, hg, PadicSeq.valuation]
    · have hg : ¬g ≈ 0 := fun hg => hf (Setoid.trans h hg)
      rw [PadicSeq.val_eq_iff_norm_eq hf hg]
      exact PadicSe

Depends on / 依赖: PadicSeq, PadicSeq.norm_equiv, PadicSeq.val_eq_iff_norm_eq, PadicSeq.valuation, Quotient, Quotient.lift, Setoid, Setoid.symm, Setoid.trans, norm_equiv, val_eq_iff_norm_eq, valuation
-/
def valuation : Rat_[p] -> Int :=
  Quotient.lift (@PadicSeq.valuation p _) fun f g h => by
    by_cases hf : f ≈ 0
    · have hg : g ≈ 0 := Setoid.trans (Setoid.symm h) hf
      simp [hf, hg, PadicSeq.valuation]
    · have hg : ¬g ≈ 0 := fun hg => hf (Setoid.trans h hg)
      rw [PadicSeq.val_eq_iff_norm_eq hf hg]
      exact PadicSeq.norm_equiv h

@[simp]
/--
theorem `valuation_zero` / 定理 `valuation_zero`

English:
theorem valuation_zero
  statement: valuation (0 : Rat_[p]) = 0
  proof: dif_pos ((const_equiv p).2 rfl)

中文:
定理 valuation_zero
  结论: valuation (0 : Rat_[p]) = 0
  证明: dif_pos ((const_equiv p).2 rfl)

Depends on / 依赖: const_equiv, dif_pos
-/
theorem valuation_zero : valuation (0 : Rat_[p]) = 0 :=
  dif_pos ((const_equiv p).2 rfl)

/--
theorem `norm_eq_zpow_neg_valuation` / 定理 `norm_eq_zpow_neg_valuation`

English:
theorem norm_eq_zpow_neg_valuation
  given: {x : Rat_[p]}
  statement: x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
  proof: by
  induction x using Quotient.inductionOn with | _ f
  intro hf
  change (PadicSeq.norm _ : Real) = (p : Real) ^ (-PadicSeq.valuation _)
  rw [PadicSeq.norm_eq_zpow_neg_valuation]
  · rw [Rat.cast_zpow, Rat.cast_natCast]
  · apply CauSeq.not_limZero_of_not_congr_zero
    contrapose hf
    apply Qu

中文:
定理 norm_eq_zpow_neg_valuation
  条件: {x : Rat_[p]}
  结论: x != 0 -> ‖x‖ = (p : 实数) ^ (-x.valuation)
  证明: by
  induction x using Quotient.inductionOn with | _ f
  intro hf
  change (PadicSeq.norm _ : Real) = (p : Real) ^ (-PadicSeq.valuation _)
  rw [PadicSeq.norm_eq_zpow_neg_valuation]
  · rw [Rat.cast_zpow, Rat.cast_natCast]
  · apply CauSeq.not_limZero_of_not_congr_zero
    contrapose hf
    apply Qu

Depends on / 依赖: CauSeq, CauSeq.not_limZero_of_not_congr_zero, PadicSeq, PadicSeq.norm, PadicSeq.norm_eq_zpow_neg_valuation, PadicSeq.valuation, Quotient, Quotient.inductionOn, Quotient.sound, Rat.cast_natCast, Rat.cast_zpow, cast_natCast, cast_zpow, contrapose, inductionOn, norm_eq_zpow_neg_valuation, not_limZero_of_not_congr_zero, valuation
-/
theorem norm_eq_zpow_neg_valuation {x : Rat_[p]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation) := by
  induction x using Quotient.inductionOn with | _ f
  intro hf
  change (PadicSeq.norm _ : Real) = (p : Real) ^ (-PadicSeq.valuation _)
  rw [PadicSeq.norm_eq_zpow_neg_valuation]
  · rw [Rat.cast_zpow, Rat.cast_natCast]
  · apply CauSeq.not_limZero_of_not_congr_zero
    contrapose hf
    apply Quotient.sound
    simpa using hf

@[simp]
/--
lemma `valuation_ratCast` / 引理 `valuation_ratCast`

English:
lemma valuation_ratCast
  given: (q : Rat)
  statement: valuation (q : Rat_[p]) = padicValRat p q
  proof: by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Rat.cast_zero, valuation_zero, padicValRat.zero]
  refine neg_injective ((zpow_right_strictMono₀ (mod_cast hp.out.one_lt)).injective
 (norm_eq_zpow_neg_valuation (mod_cast hq)).symm.trans ?_)
  rw [eq_padicNorm]; rw [← Rat.cast_natCast]; rw [← Ra

中文:
引理 valuation_ratCast
  条件: (q : 有理数)
  结论: valuation (q : Rat_[p]) = padicValRat p q
  证明: by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Rat.cast_zero, valuation_zero, padicValRat.zero]
  refine neg_injective ((zpow_right_strictMono₀ (mod_cast hp.out.one_lt)).injective
 (norm_eq_zpow_neg_valuation (mod_cast hq)).symm.trans ?_)
  rw [eq_padicNorm]; rw [← Rat.cast_natCast]; rw [← Ra

Depends on / 依赖: Rat.cast_inj, Rat.cast_natCast, Rat.cast_zero, Rat.cast_zpow, cast_inj, cast_natCast, cast_zero, cast_zpow, eq_or_ne, eq_padicNorm, eq_zpow_of_nonzero, hasSum_one_poissonMeasure, hp.out.one_lt, injective, isProbabilityMeasure_sum_dirac, mod_cast, neg_injective, norm_eq_zpow_neg_valuation, one_lt, padicNorm
-/
lemma valuation_ratCast (q : Rat) : valuation (q : Rat_[p]) = padicValRat p q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Rat.cast_zero, valuation_zero, padicValRat.zero]
  refine neg_injective ((zpow_right_strictMono₀ (mod_cast hp.out.one_lt)).injective
 (norm_eq_zpow_neg_valuation (mod_cast hq)).symm.trans ?_)
  rw [eq_padicNorm]; rw [← Rat.cast_natCast]; rw [← Rat.cast_zpow]; rw [Rat.cast_inj]
  exact padicNorm.eq_zpow_of_nonzero hq

@[simp]
/--
lemma `valuation_intCast` / 引理 `valuation_intCast`

English:
lemma valuation_intCast
  given: (n : Int)
  statement: valuation (n : Rat_[p]) = padicValInt p n
  proof: by
  rw [← Rat.cast_intCast]; rw [valuation_ratCast]; rw [padicValRat.of_int]

@[simp]

中文:
引理 valuation_intCast
  条件: (n : 整数)
  结论: valuation (n : Rat_[p]) = padicVal整数 p n
  证明: by
  rw [← Rat.cast_intCast]; rw [valuation_ratCast]; rw [padicValRat.of_int]

@[simp]

Depends on / 依赖: Measure, Measure.isProbabilityMeasure_map, Rat.cast_intCast, cast_intCast, isProbabilityMeasure_map, of_discrete, of_int, padicValRat, padicValRat.of_int, valuation_ratCast
-/
lemma valuation_intCast (n : Int) : valuation (n : Rat_[p]) = padicValInt p n := by
  rw [← Rat.cast_intCast]; rw [valuation_ratCast]; rw [padicValRat.of_int]

@[simp]
/--
lemma `valuation_natCast` / 引理 `valuation_natCast`

English:
lemma valuation_natCast
  given: (n : Nat)
  statement: valuation (n : Rat_[p]) = padicValNat p n
  proof: by
  rw [← Rat.cast_natCast]; rw [valuation_ratCast]; rw [padicValRat.of_nat]

@[simp]

中文:
引理 valuation_natCast
  条件: (n : 自然数)
  结论: valuation (n : Rat_[p]) = padicVal自然数 p n
  证明: by
  rw [← Rat.cast_natCast]; rw [valuation_ratCast]; rw [padicValRat.of_nat]

@[simp]

Depends on / 依赖: Rat.cast_natCast, cast_natCast, of_nat, padicValRat, padicValRat.of_nat, valuation_ratCast
-/
lemma valuation_natCast (n : Nat) : valuation (n : Rat_[p]) = padicValNat p n := by
  rw [← Rat.cast_natCast]; rw [valuation_ratCast]; rw [padicValRat.of_nat]

@[simp]
/--
lemma `valuation_ofNat` / 引理 `valuation_ofNat`

English:
lemma valuation_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: valuation_natCast n

@[simp]

中文:
引理 valuation_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: valuation_natCast n

@[simp]

Depends on / 依赖: valuation_natCast
-/
lemma valuation_ofNat (n : Nat) [n.AtLeastTwo] :
    valuation (ofNat(n) : Rat_[p]) = padicValNat p n :=
  valuation_natCast n

@[simp]
/--
lemma `valuation_one` / 引理 `valuation_one`

English:
lemma valuation_one
  statement: valuation (1 : Rat_[p]) = 0
  proof: by
  rw [← Nat.cast_one]; rw [valuation_natCast]; rw [padicValNat_one_right]; rw [cast_zero]

中文:
引理 valuation_one
  结论: valuation (1 : Rat_[p]) = 0
  证明: by
  rw [← Nat.cast_one]; rw [valuation_natCast]; rw [padicValNat_one_right]; rw [cast_zero]

Depends on / 依赖: Nat.cast_one, cast_one, cast_zero, padicValNat_one_right, valuation_natCast
-/
lemma valuation_one : valuation (1 : Rat_[p]) = 0 := by
  rw [← Nat.cast_one]; rw [valuation_natCast]; rw [padicValNat_one_right]; rw [cast_zero]

-- not @[simp], since simp can prove it
/--
lemma `valuation_p` / 引理 `valuation_p`

English:
lemma valuation_p
  statement: valuation (p : Rat_[p]) = 1
  proof: by
  rw [valuation_natCast]; rw [padicValNat_self]; rw [cast_one]

中文:
引理 valuation_p
  结论: valuation (p : Rat_[p]) = 1
  证明: by
  rw [valuation_natCast]; rw [padicValNat_self]; rw [cast_one]

Depends on / 依赖: cast_one, padicValNat_self, valuation_natCast
-/
lemma valuation_p : valuation (p : Rat_[p]) = 1 := by
  rw [valuation_natCast]; rw [padicValNat_self]; rw [cast_one]

/--
theorem `le_valuation_add` / 定理 `le_valuation_add`

English:
theorem le_valuation_add
  given: {x y : Rat_[p]} (hxy : x + y != 0)
  proof: by
  by_cases hx : x = 0
  · simpa only [hx, zero_add] using min_le_right _ _
  by_cases hy : y = 0
  · simpa only [hy, add_zero] using min_le_left _ _
  have : ‖x + y‖ <= max ‖x‖ ‖y‖ := nonarchimedean x y
  simpa only [norm_eq_zpow_neg_valuation hxy, norm_eq_zpow_neg_valuation hx,
    norm_eq_zpow_

中文:
定理 le_valuation_add
  条件: {x y : Rat_[p]} (hxy : x + y != 0)
  证明: by
  by_cases hx : x = 0
  · simpa only [hx, zero_add] using min_le_right _ _
  by_cases hy : y = 0
  · simpa only [hy, add_zero] using min_le_left _ _
  have : ‖x + y‖ <= max ‖x‖ ‖y‖ := nonarchimedean x y
  simpa only [norm_eq_zpow_neg_valuation hxy, norm_eq_zpow_neg_valuation hx,
    norm_eq_zpow_

Depends on / 依赖: add_zero, hp.out.one_lt, le_max_iff, min_le_iff, min_le_left, min_le_right, mod_cast, neg_le_neg_iff, nonarchimedean, norm_eq_zpow_neg_valuation, one_lt, zero_add
-/
theorem le_valuation_add {x y : Rat_[p]} (hxy : x + y != 0) :
    min x.valuation y.valuation <= (x + y).valuation := by
  by_cases hx : x = 0
  · simpa only [hx, zero_add] using min_le_right _ _
  by_cases hy : y = 0
  · simpa only [hy, add_zero] using min_le_left _ _
  have : ‖x + y‖ <= max ‖x‖ ‖y‖ := nonarchimedean x y
  simpa only [norm_eq_zpow_neg_valuation hxy, norm_eq_zpow_neg_valuation hx,
    norm_eq_zpow_neg_valuation hy, le_max_iff,
    zpow_le_zpow_iff_right₀ (mod_cast hp.out.one_lt : 1 < (p : Real)), neg_le_neg_iff, ← min_le_iff]

@[simp]
/--
lemma `valuation_mul` / 引理 `valuation_mul`

English:
lemma valuation_mul
  given: {x y : Rat_[p]} (hx : x != 0) (hy : y != 0)
  proof: by
  have h_norm : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  have hp_ne_one : (p : Real) != 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : Real) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation hy,
    norm_eq_zpow_neg_valuation (mul_ne_zero h

中文:
引理 valuation_mul
  条件: {x y : Rat_[p]} (hx : x != 0) (hy : y != 0)
  证明: by
  have h_norm : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  have hp_ne_one : (p : Real) != 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : Real) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation hy,
    norm_eq_zpow_neg_valuation (mul_ne_zero h

Depends on / 依赖: Fact.out, NeZero, NeZero.pos, h_norm, hp_ne_one, hp_pos, hp_pos.ne, mod_cast, mul_ne_zero, ne_one, neg_add, neg_inj, norm_eq_zpow_neg_valuation, norm_mul, p.Prime
-/
lemma valuation_mul {x y : Rat_[p]} (hx : x != 0) (hy : y != 0) :
    (x * y).valuation = x.valuation + y.valuation := by
  have h_norm : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  have hp_ne_one : (p : Real) != 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : Real) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation hy,
    norm_eq_zpow_neg_valuation (mul_ne_zero hx hy), ← zpow_add₀ hp_pos.ne',
    zpow_right_inj₀ hp_pos hp_ne_one, ← neg_add, neg_inj] at h_norm

@[simp]
/--
lemma `valuation_inv` / 引理 `valuation_inv`

English:
lemma valuation_inv
  given: (x : Rat_[p])
  statement: x⁻¹.valuation = -x.valuation
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have h_norm : ‖x⁻¹‖ = ‖x‖⁻¹ := norm_inv x
  have hp_ne_one : (p : Real) != 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : Real) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation <| inv_ne_zero

中文:
引理 valuation_inv
  条件: (x : Rat_[p])
  结论: x⁻¹.valuation = -x.valuation
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have h_norm : ‖x⁻¹‖ = ‖x‖⁻¹ := norm_inv x
  have hp_ne_one : (p : Real) != 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : Real) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation <| inv_ne_zero

Depends on / 依赖: Fact.out, NeZero, NeZero.pos, eq_or_ne, h_norm, hp_ne_one, hp_pos, inv_ne_zero, mod_cast, ne_one, neg_inj, norm_eq_zpow_neg_valuation, norm_inv, p.Prime, zpow_neg
-/
lemma valuation_inv (x : Rat_[p]) : x⁻¹.valuation = -x.valuation := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have h_norm : ‖x⁻¹‖ = ‖x‖⁻¹ := norm_inv x
  have hp_ne_one : (p : Real) != 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : Real) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation <| inv_ne_zero hx,
    ← zpow_neg, zpow_right_inj₀ hp_pos hp_ne_one, neg_inj] at h_norm

@[simp]
/--
lemma `valuation_pow` / 引理 `valuation_pow`

English:
lemma valuation_pow
  given: (x : Rat_[p])
  statement: forall n : Nat, (x ^ n).valuation = n * x.valuation
  proof: eq_or_ne x 0
    · simp
    · simp [pow_succ, hx, valuation_mul, valuation_pow, _root_.add_one_mul]

@[simp]

中文:
引理 valuation_pow
  条件: (x : Rat_[p])
  结论: 对任意 n : 自然数, (x ^ n).valuation = n * x.valuation
  证明: eq_or_ne x 0
    · simp
    · simp [pow_succ, hx, valuation_mul, valuation_pow, _root_.add_one_mul]

@[simp]

Depends on / 依赖: eq_or_ne
-/
lemma valuation_pow (x : Rat_[p]) : forall n : Nat, (x ^ n).valuation = n * x.valuation
  | 0 => by simp
  | n + 1 => by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    · simp [pow_succ, hx, valuation_mul, valuation_pow, _root_.add_one_mul]

@[simp]
/--
lemma `valuation_zpow` / 引理 `valuation_zpow`

English:
lemma valuation_zpow
  given: (x : Rat_[p])
  statement: forall n : Int, (x ^ n).valuation = n * x.valuation

中文:
引理 valuation_zpow
  条件: (x : Rat_[p])
  结论: 对任意 n : 整数, (x ^ n).valuation = n * x.valuation
-/
lemma valuation_zpow (x : Rat_[p]) : forall n : Int, (x ^ n).valuation = n * x.valuation
  | (n : Nat) => by simp
  | .negSucc n => by simp [← neg_mul]; simp [Int.negSucc_eq]

open scoped Classical in
/--
Definition of `addValuationDef` / `addValuationDef` 的定义

English:
definition addValuationDef
  signature: : Rat_[p] -> WithTop Int
  body: fun x => if x = 0 then ⊤ else x.valuation

@[simp]

中文:
定义 addValuationDef
  签名: : Rat_[p] -> WithTop 整数
  定义体: fun x => if x = 0 then ⊤ else x.valuation

@[simp]

Depends on / 依赖: valuation, x.valuation
-/
def addValuationDef : Rat_[p] -> WithTop Int :=
  fun x => if x = 0 then ⊤ else x.valuation

@[simp]
/--
theorem `AddValuation.map_zero` / 定理 `AddValuation.map_zero`

English:
theorem AddValuation.map_zero
  statement: addValuationDef (0 : Rat_[p]) = ⊤
  proof: by
  rw [addValuationDef]; rw [if_pos rfl]

@[simp]

中文:
定理 AddValuation.map_zero
  结论: addValuationDef (0 : Rat_[p]) = ⊤
  证明: by
  rw [addValuationDef]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: addValuationDef, if_pos
-/
theorem AddValuation.map_zero : addValuationDef (0 : Rat_[p]) = ⊤ := by
  rw [addValuationDef]; rw [if_pos rfl]

@[simp]
/--
theorem `AddValuation.map_one` / 定理 `AddValuation.map_one`

English:
theorem AddValuation.map_one
  statement: addValuationDef (1 : Rat_[p]) = 0
  proof: by
  rw [addValuationDef]; rw [if_neg one_ne_zero]; rw [valuation_one]; rw [WithTop.coe_zero]

中文:
定理 AddValuation.map_one
  结论: addValuationDef (1 : Rat_[p]) = 0
  证明: by
  rw [addValuationDef]; rw [if_neg one_ne_zero]; rw [valuation_one]; rw [WithTop.coe_zero]

Depends on / 依赖: WithTop, WithTop.coe_zero, addValuationDef, coe_zero, if_neg, one_ne_zero, valuation_one
-/
theorem AddValuation.map_one : addValuationDef (1 : Rat_[p]) = 0 := by
  rw [addValuationDef]; rw [if_neg one_ne_zero]; rw [valuation_one]; rw [WithTop.coe_zero]

/--
theorem `AddValuation.map_mul` / 定理 `AddValuation.map_mul`

English:
theorem AddValuation.map_mul
  given: (x y : Rat_[p])
  proof: by
  simp only [addValuationDef]
  by_cases hx : x = 0
  · rw [hx, if_pos rfl, zero_mul, if_pos rfl, WithTop.top_add]
  · by_cases hy : y = 0
    · rw [hy, if_pos rfl, mul_zero, if_pos rfl, WithTop.add_top]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq

中文:
定理 AddValuation.map_mul
  条件: (x y : Rat_[p])
  证明: by
  simp only [addValuationDef]
  by_cases hx : x = 0
  · rw [hx, if_pos rfl, zero_mul, if_pos rfl, WithTop.top_add]
  · by_cases hy : y = 0
    · rw [hy, if_pos rfl, mul_zero, if_pos rfl, WithTop.add_top]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq

Depends on / 依赖: WithTop, WithTop.add_top, WithTop.coe_add, WithTop.coe_eq_coe, WithTop.top_add, addValuationDef, add_top, coe_add, coe_eq_coe, if_neg, if_pos, mul_ne_zero, mul_zero, top_add, valuation_mul, zero_mul
-/
theorem AddValuation.map_mul (x y : Rat_[p]) :
    addValuationDef (x * y : Rat_[p]) = addValuationDef x + addValuationDef y := by
  simp only [addValuationDef]
  by_cases hx : x = 0
  · rw [hx, if_pos rfl, zero_mul, if_pos rfl, WithTop.top_add]
  · by_cases hy : y = 0
    · rw [hy, if_pos rfl, mul_zero, if_pos rfl, WithTop.add_top]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
        valuation_mul hx hy]

/--
theorem `AddValuation.map_add` / 定理 `AddValuation.map_add`

English:
theorem AddValuation.map_add
  given: (x y : Rat_[p])
  proof: by
  simp only [addValuationDef]
  by_cases hxy : x + y = 0
  · rw [hxy, if_pos rfl]
    exact le_top
  · by_cases hx : x = 0
    · rw [hx, if_pos rfl, min_eq_right, zero_add]
      exact le_top
    · by_cases hy : y = 0
      · rw [hy, if_pos rfl, min_eq_left, add_zero]
        exact le_top
      ·

中文:
定理 AddValuation.map_add
  条件: (x y : Rat_[p])
  证明: by
  simp only [addValuationDef]
  by_cases hxy : x + y = 0
  · rw [hxy, if_pos rfl]
    exact le_top
  · by_cases hx : x = 0
    · rw [hx, if_pos rfl, min_eq_right, zero_add]
      exact le_top
    · by_cases hy : y = 0
      · rw [hy, if_pos rfl, min_eq_left, add_zero]
        exact le_top
      ·

Depends on / 依赖: WithTop, WithTop.coe_le_coe, WithTop.coe_min, addValuationDef, add_zero, coe_le_coe, coe_min, if_neg, if_pos, le_top, le_valuation_add, min_eq_left, min_eq_right, zero_add
-/
theorem AddValuation.map_add (x y : Rat_[p]) :
    min (addValuationDef x) (addValuationDef y) <= addValuationDef (x + y : Rat_[p]) := by
  simp only [addValuationDef]
  by_cases hxy : x + y = 0
  · rw [hxy, if_pos rfl]
    exact le_top
  · by_cases hx : x = 0
    · rw [hx, if_pos rfl, min_eq_right, zero_add]
      exact le_top
    · by_cases hy : y = 0
      · rw [hy, if_pos rfl, min_eq_left, add_zero]
        exact le_top
      · rw [if_neg hx, if_neg hy, if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
        exact le_valuation_add hxy

open WithZero

open scoped Classical in
/-- The `p`-adic valuation on `ℚ_[p]`, as a `Valuation`, bundled `Padic.valuation`. -/
@[simps]
/--
Definition of `mulValuation` / `mulValuation` 的定义

English:
definition mulValuation
  signature: : Valuation Rat_[p] Intᵐ⁰ where
  body: if x = 0 then 0 else exp (-x.valuation)
  map_zero' := by simp
  map_one' := by simp
  map_mul' _ _ := by split_ifs <;> simp_all [add_comm]
  map_add_le_max' _ _ := by
    split_ifs
    any_goals simp_all [inv_le_inv₀]
    simpa using le_valuation_add ‹_›

中文:
定义 mulValuation
  签名: : 赋值 Rat_[p] 整数ᵐ⁰ where
  定义体: if x = 0 then 0 else exp (-x.valuation)
  map_zero' := by simp
  map_one' := by simp
  map_mul' _ _ := by split_ifs <;> simp_all [add_comm]
  map_add_le_max' _ _ := by
    split_ifs
    any_goals simp_all [inv_le_inv₀]
    simpa using le_valuation_add ‹_›

Depends on / 依赖: valuation, x.valuation
-/
noncomputable def mulValuation : Valuation Rat_[p] Intᵐ⁰ where
  toFun x := if x = 0 then 0 else exp (-x.valuation)
  map_zero' := by simp
  map_one' := by simp
  map_mul' _ _ := by split_ifs <;> simp_all [add_comm]
  map_add_le_max' _ _ := by
    split_ifs
    any_goals simp_all [inv_le_inv₀]
    simpa using le_valuation_add ‹_›

/--
lemma `comap_mulValuation_eq_padicValuation` / 引理 `comap_mulValuation_eq_padicValuation`

English:
lemma comap_mulValuation_eq_padicValuation
  proof: by
  ext
  simp [Rat.padicValuation]

中文:
引理 comap_mulValuation_eq_padicValuation
  证明: by
  ext
  simp [Rat.padicValuation]

Depends on / 依赖: Rat.castHom, Rat.padicValuation, castHom, padicValuation
-/
lemma comap_mulValuation_eq_padicValuation :
    (mulValuation (p := p)).comap (Rat.castHom _) = Rat.padicValuation p := by
  ext
  simp [Rat.padicValuation]

/--
lemma `comap_mulValuation_eq_int_padicValuation` / 引理 `comap_mulValuation_eq_int_padicValuation`

English:
lemma comap_mulValuation_eq_int_padicValuation
  proof: by
  ext
  simp [← Rat.padicValuation_cast, ← comap_mulValuation_eq_padicValuation]

中文:
引理 comap_mulValuation_eq_int_padicValuation
  证明: by
  ext
  simp [← Rat.padicValuation_cast, ← comap_mulValuation_eq_padicValuation]

Depends on / 依赖: Int.castRingHom, Int.padicValuation, Rat.padicValuation_cast, castRingHom, comap_mulValuation_eq_padicValuation, padicValuation, padicValuation_cast
-/
lemma comap_mulValuation_eq_int_padicValuation :
    (mulValuation (p := p)).comap (Int.castRingHom _) = Int.padicValuation p := by
  ext
  simp [← Rat.padicValuation_cast, ← comap_mulValuation_eq_padicValuation]

/--
lemma `norm_eq_zpow_log_mulValuation` / 引理 `norm_eq_zpow_log_mulValuation`

English:
lemma norm_eq_zpow_log_mulValuation
  given: {x : Rat_[p]} (hx : x != 0)
  proof: by
  simp [norm_eq_zpow_neg_valuation, hx]

中文:
引理 norm_eq_zpow_log_mulValuation
  条件: {x : Rat_[p]} (hx : x != 0)
  证明: by
  simp [norm_eq_zpow_neg_valuation, hx]

Depends on / 依赖: norm_eq_zpow_neg_valuation
-/
lemma norm_eq_zpow_log_mulValuation {x : Rat_[p]} (hx : x != 0) :
    ‖x‖ = (p : Real) ^ (log (mulValuation x)) := by
  simp [norm_eq_zpow_neg_valuation, hx]

/--
Definition of `addValuation` / `addValuation` 的定义

English:
definition addValuation
  signature: : AddValuation Rat_[p] (WithTop Int)
  body: AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul

@[simp]

中文:
定义 addValuation
  签名: : AddValuation Rat_[p] (WithTop 整数)
  定义体: AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul

@[simp]

Depends on / 依赖: AddValuation, AddValuation.map_add, AddValuation.map_mul, AddValuation.map_one, AddValuation.map_zero, AddValuation.of, addValuationDef, map_add, map_mul, map_one, map_zero
-/
def addValuation : AddValuation Rat_[p] (WithTop Int) :=
  AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul

@[simp]
/--
theorem `addValuation.apply` / 定理 `addValuation.apply`

English:
theorem addValuation.apply
  given: {x : Rat_[p]} (hx : x != 0)
  proof: by
  simp only [Padic.addValuation, AddValuation.of_apply, addValuationDef, if_neg hx]

中文:
定理 addValuation.apply
  条件: {x : Rat_[p]} (hx : x != 0)
  证明: by
  simp only [Padic.addValuation, AddValuation.of_apply, addValuationDef, if_neg hx]

Depends on / 依赖: AddValuation, AddValuation.of_apply, Padic.addValuation, addValuation, addValuationDef, if_neg, of_apply
-/
theorem addValuation.apply {x : Rat_[p]} (hx : x != 0) :
    Padic.addValuation x = (x.valuation : WithTop Int) := by
  simp only [Padic.addValuation, AddValuation.of_apply, addValuationDef, if_neg hx]

section NormLEIff



/--
theorem `norm_le_pow_iff_norm_lt_pow_add_one` / 定理 `norm_le_pow_iff_norm_lt_pow_add_one`

English:
theorem norm_le_pow_iff_norm_lt_pow_add_one
  given: (x : Rat_[p]) (n : Int)
  proof: by
  have aux (n : Int) : 0 < ((p : Real) ^ n) := zpow_pos (mod_cast hp.1.pos) _
  by_cases hx0 : x = 0
  · simp [hx0, norm_zero, aux, le_of_lt (aux _)]
  rw [norm_eq_zpow_neg_valuation hx0]
  have h1p : 1 < (p : Real) := mod_cast hp.1.one_lt
  have H := zpow_right_strictMono₀ h1p
  rw [H.le_iff_le]

中文:
定理 norm_le_pow_iff_norm_lt_pow_add_one
  条件: (x : Rat_[p]) (n : 整数)
  证明: by
  have aux (n : Int) : 0 < ((p : Real) ^ n) := zpow_pos (mod_cast hp.1.pos) _
  by_cases hx0 : x = 0
  · simp [hx0, norm_zero, aux, le_of_lt (aux _)]
  rw [norm_eq_zpow_neg_valuation hx0]
  have h1p : 1 < (p : Real) := mod_cast hp.1.one_lt
  have H := zpow_right_strictMono₀ h1p
  rw [H.le_iff_le]

Depends on / 依赖: H.le_iff_le, H.lt_iff_lt, Int.lt_add_one_iff, le_iff_le, le_of_lt, lt_add_one_iff, lt_iff_lt, mod_cast, norm_eq_zpow_neg_valuation, norm_zero, one_lt, zpow_pos
-/
theorem norm_le_pow_iff_norm_lt_pow_add_one (x : Rat_[p]) (n : Int) :
    ‖x‖ <= (p : Real) ^ n ↔ ‖x‖ < (p : Real) ^ (n + 1) := by
  have aux (n : Int) : 0 < ((p : Real) ^ n) := zpow_pos (mod_cast hp.1.pos) _
  by_cases hx0 : x = 0
  · simp [hx0, norm_zero, aux, le_of_lt (aux _)]
  rw [norm_eq_zpow_neg_valuation hx0]
  have h1p : 1 < (p : Real) := mod_cast hp.1.one_lt
  have H := zpow_right_strictMono₀ h1p
  rw [H.le_iff_le]; rw [H.lt_iff_lt]; rw [Int.lt_add_one_iff]

/--
theorem `norm_lt_pow_iff_norm_le_pow_sub_one` / 定理 `norm_lt_pow_iff_norm_le_pow_sub_one`

English:
theorem norm_lt_pow_iff_norm_le_pow_sub_one
  given: (x : Rat_[p]) (n : Int)
  proof: by
  rw [norm_le_pow_iff_norm_lt_pow_add_one]; rw [sub_add_cancel]

中文:
定理 norm_lt_pow_iff_norm_le_pow_sub_one
  条件: (x : Rat_[p]) (n : 整数)
  证明: by
  rw [norm_le_pow_iff_norm_lt_pow_add_one]; rw [sub_add_cancel]

Depends on / 依赖: norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel
-/
theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : Rat_[p]) (n : Int) :
    ‖x‖ < (p : Real) ^ n ↔ ‖x‖ <= (p : Real) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one]; rw [sub_add_cancel]

/--
theorem `norm_le_one_iff_val_nonneg` / 定理 `norm_le_one_iff_val_nonneg`

English:
theorem norm_le_one_iff_val_nonneg
  given: (x : Rat_[p])
  statement: ‖x‖ <= 1 ↔ 0 <= x.valuation
  proof: by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, valuation_zero, zero_le_one, le_refl]
  · rw [norm_eq_zpow_neg_valuation hx, ← zpow_zero (p : Real), zpow_le_zpow_iff_right₀, neg_nonpos]
    exact Nat.one_lt_cast.2 (Nat.Prime.one_lt' p).1

中文:
定理 norm_le_one_iff_val_nonneg
  条件: (x : Rat_[p])
  结论: ‖x‖ <= 1 ↔ 0 <= x.valuation
  证明: by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, valuation_zero, zero_le_one, le_refl]
  · rw [norm_eq_zpow_neg_valuation hx, ← zpow_zero (p : Real), zpow_le_zpow_iff_right₀, neg_nonpos]
    exact Nat.one_lt_cast.2 (Nat.Prime.one_lt' p).1

Depends on / 依赖: Nat.Prime.one_lt, Nat.one_lt_cast, le_refl, neg_nonpos, norm_eq_zpow_neg_valuation, norm_zero, one_lt, one_lt_cast, valuation_zero, zero_le_one, zpow_zero
-/
theorem norm_le_one_iff_val_nonneg (x : Rat_[p]) : ‖x‖ <= 1 ↔ 0 <= x.valuation := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, valuation_zero, zero_le_one, le_refl]
  · rw [norm_eq_zpow_neg_valuation hx, ← zpow_zero (p : Real), zpow_le_zpow_iff_right₀, neg_nonpos]
    exact Nat.one_lt_cast.2 (Nat.Prime.one_lt' p).1

end NormLEIff

end Padic
