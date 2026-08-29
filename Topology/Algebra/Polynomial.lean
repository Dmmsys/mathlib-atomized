/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `Polynomial.continuous_eval₂`: `Polynomial.eval₂` defines a continuous function.
* `Polynomial.continuous_aeval`: `Polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `Polynomial.continuousAt_aeval`,
  `Polynomial.continuousWithinAt_aeval`, `Polynomial.continuousOn_aeval`.
* `Polynomial.continuous`: `Polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `Polynomial.continuousAt`, `Polynomial.continuousWithinAt`,
  `Polynomial.continuousOn`.
* `Polynomial.tendsto_norm_atTop`: `fun x ↦ ‖Polynomial.eval (z x) p‖` tends to infinity provided
  that `fun x ↦ ‖z x‖` tends to infinity and `0 < degree p`;
* `Polynomial.tendsto_abv_eval₂_atTop`, `Polynomial.tendsto_abv_atTop`,
  `Polynomial.tendsto_abv_aeval_atTop`: a few versions of the previous statement for
  `IsAbsoluteValue abv` instead of norm.

## Tags

Polynomial, continuity
-/

public section


open IsAbsoluteValue Filter

namespace Polynomial

section IsTopologicalSemiring

variable {R S : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] (p : R[X])

@[continuity, fun_prop]
/--
theorem `continuous_eval₂` / 定理 `continuous_eval₂`

English:
theorem continuous_eval₂
  given: [Semiring S] (p : S[X]) (f : S ->+* R)
  proof: by
  simp only [eval₂_eq_sum]
  exact continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_pow _)

@[continuity, fun_prop]

中文:
定理 continuous_eval₂
  条件: [Semiring S] (p : S[X]) (f : S ->+* R)
  证明: by
  simp only [eval₂_eq_sum]
  exact continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_pow _)

@[continuity, fun_prop]
-/
protected theorem continuous_eval₂ [Semiring S] (p : S[X]) (f : S ->+* R) :
    Continuous fun x => p.eval₂ f x := by
  simp only [eval₂_eq_sum]
  exact continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_pow _)

@[continuity, fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous fun x => p.eval x
  proof: p.continuous_eval₂ _

@[fun_prop]

中文:
定理 continuous
  结论: Continuous fun x => p.eval x
  证明: p.continuous_eval₂ _

@[fun_prop]
-/
protected theorem continuous : Continuous fun x => p.eval x :=
  p.continuous_eval₂ _

@[fun_prop]
/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: {a : R}
  statement: ContinuousAt (fun x => p.eval x) a
  proof: p.continuous.continuousAt

@[fun_prop]

中文:
定理 continuousAt
  条件: {a : R}
  结论: ContinuousAt (fun x => p.eval x) a
  证明: p.continuous.continuousAt

@[fun_prop]
-/
protected theorem continuousAt {a : R} : ContinuousAt (fun x => p.eval x) a :=
  p.continuous.continuousAt

@[fun_prop]
/--
theorem `continuousWithinAt` / 定理 `continuousWithinAt`

English:
theorem continuousWithinAt
  given: {s a}
  statement: ContinuousWithinAt (fun x => p.eval x) s a
  proof: p.continuous.continuousWithinAt

@[fun_prop]

中文:
定理 continuousWithinAt
  条件: {s a}
  结论: ContinuousWithinAt (fun x => p.eval x) s a
  证明: p.continuous.continuousWithinAt

@[fun_prop]
-/
protected theorem continuousWithinAt {s a} : ContinuousWithinAt (fun x => p.eval x) s a :=
  p.continuous.continuousWithinAt

@[fun_prop]
/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: {s}
  statement: ContinuousOn (fun x => p.eval x) s
  proof: p.continuous.continuousOn

中文:
定理 continuousOn
  条件: {s}
  结论: ContinuousOn (fun x => p.eval x) s
  证明: p.continuous.continuousOn
-/
protected theorem continuousOn {s} : ContinuousOn (fun x => p.eval x) s :=
  p.continuous.continuousOn

end IsTopologicalSemiring

section TopologicalAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A] (p : R[X])

@[continuity, fun_prop]
/--
theorem `continuous_aeval` / 定理 `continuous_aeval`

English:
theorem continuous_aeval
  statement: Continuous fun x : A => aeval x p
  proof: p.continuous_eval₂ _

@[fun_prop]

中文:
定理 continuous_aeval
  结论: Continuous fun x : A => aeval x p
  证明: p.continuous_eval₂ _

@[fun_prop]
-/
protected theorem continuous_aeval : Continuous fun x : A => aeval x p :=
  p.continuous_eval₂ _

@[fun_prop]
/--
theorem `continuousAt_aeval` / 定理 `continuousAt_aeval`

English:
theorem continuousAt_aeval
  given: {a : A}
  statement: ContinuousAt (fun x : A => aeval x p) a
  proof: p.continuous_aeval.continuousAt

@[fun_prop]

中文:
定理 continuousAt_aeval
  条件: {a : A}
  结论: ContinuousAt (fun x : A => aeval x p) a
  证明: p.continuous_aeval.continuousAt

@[fun_prop]
-/
protected theorem continuousAt_aeval {a : A} : ContinuousAt (fun x : A => aeval x p) a :=
  p.continuous_aeval.continuousAt

@[fun_prop]
/--
theorem `continuousWithinAt_aeval` / 定理 `continuousWithinAt_aeval`

English:
theorem continuousWithinAt_aeval
  given: {s a}
  proof: p.continuous_aeval.continuousWithinAt

@[fun_prop]

中文:
定理 continuousWithinAt_aeval
  条件: {s a}
  证明: p.continuous_aeval.continuousWithinAt

@[fun_prop]
-/
protected theorem continuousWithinAt_aeval {s a} :
    ContinuousWithinAt (fun x : A => aeval x p) s a :=
  p.continuous_aeval.continuousWithinAt

@[fun_prop]
/--
theorem `continuousOn_aeval` / 定理 `continuousOn_aeval`

English:
theorem continuousOn_aeval
  given: {s}
  statement: ContinuousOn (fun x : A => aeval x p) s
  proof: p.continuous_aeval.continuousOn

中文:
定理 continuousOn_aeval
  条件: {s}
  结论: ContinuousOn (fun x : A => aeval x p) s
  证明: p.continuous_aeval.continuousOn
-/
protected theorem continuousOn_aeval {s} : ContinuousOn (fun x : A => aeval x p) s :=
  p.continuous_aeval.continuousOn

end TopologicalAlgebra

/--
theorem `tendsto_abv_eval₂_atTop` / 定理 `tendsto_abv_eval₂_atTop`

English:
theorem tendsto_abv_eval₂_atTop
  statement: {R S k α : Type*} [Semiring R] [Ring S]
  proof: by
  revert hf; refine degree_pos_induction_on p hd ?_ ?_ ?_ <;> clear hd p
  · rintro _ - hc
    rw [leadingCoeff_mul_X]; rw [leadingCoeff_C] at hc
    simpa [abv_mul abv] using hz.const_mul_atTop ((abv_pos abv).2 hc)
  · intro _ _ ihp hf
    rw [leadingCoeff_mul_X] at hf
    simpa [abv_mul abv] us

中文:
定理 tendsto_abv_eval₂_atTop
  结论: {R S k α : 类型} [Semiring R] [Ring S]
  证明: by
  revert hf; refine degree_pos_induction_on p hd ?_ ?_ ?_ <;> clear hd p
  · rintro _ - hc
    rw [leadingCoeff_mul_X]; rw [leadingCoeff_C] at hc
    simpa [abv_mul abv] using hz.const_mul_atTop ((abv_pos abv).2 hc)
  · intro _ _ ihp hf
    rw [leadingCoeff_mul_X] at hf
    simpa [abv_mul abv] us

Depends on / 依赖: abv_ad, abv_mul, abv_pos, add_comm, atTop_of_add_const, const_mul_atTop, degree_C_le, degree_C_le.trans_lt, degree_pos_induction_on, hz.const_mul_atTop, leadingCoeff_C, leadingCoeff_add_of_degree_lt, leadingCoeff_mul_X, revert, tendsto_atTop_mono, trans_lt
-/
theorem tendsto_abv_eval₂_atTop {R S k α : Type*} [Semiring R] [Ring S]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : R ->+* S) (abv : S -> k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p)
    (hf : f p.leadingCoeff != 0) {l : Filter α} {z : α -> S} (hz : Tendsto (abv ∘ z) l atTop) :
    Tendsto (fun x => abv (p.eval₂ f (z x))) l atTop := by
  revert hf; refine degree_pos_induction_on p hd ?_ ?_ ?_ <;> clear hd p
  · rintro _ - hc
    rw [leadingCoeff_mul_X]; rw [leadingCoeff_C] at hc
    simpa [abv_mul abv] using hz.const_mul_atTop ((abv_pos abv).2 hc)
  · intro _ _ ihp hf
    rw [leadingCoeff_mul_X] at hf
    simpa [abv_mul abv] using (ihp hf).atTop_mul_atTop₀ hz
  · intro _ a hd ihp hf
    rw [add_comm]; rw [leadingCoeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf
    refine .atTop_of_add_const (abv (-f a)) ?_
    refine tendsto_atTop_mono (fun _ => abv_add abv _ _) ?_
    simpa using ihp hf

/--
theorem `tendsto_abv_atTop` / 定理 `tendsto_abv_atTop`

English:
theorem tendsto_abv_atTop
  statement: {R k α : Type*} [Ring R]
  proof: by
  apply tendsto_abv_eval₂_atTop _ _ _ h _ hz
  exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

中文:
定理 tendsto_abv_atTop
  结论: {R k α : 类型} [Ring R]
  证明: by
  apply tendsto_abv_eval₂_atTop _ _ _ h _ hz
  exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

Depends on / 依赖: leadingCoeff_eq_zero, ne_zero_of_degree_gt
-/
theorem tendsto_abv_atTop {R k α : Type*} [Ring R]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k] (abv : R -> k)
    [IsAbsoluteValue abv] (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α -> R}
    (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (p.eval (z x))) l atTop := by
  apply tendsto_abv_eval₂_atTop _ _ _ h _ hz
  exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

/--
theorem `tendsto_abv_aeval_atTop` / 定理 `tendsto_abv_aeval_atTop`

English:
theorem tendsto_abv_aeval_atTop
  statement: {R A k α : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  proof: tendsto_abv_eval₂_atTop _ abv p hd h₀ hz

中文:
定理 tendsto_abv_aeval_atTop
  结论: {R A k α : 类型} [CommSemiring R] [Ring A] [Algebra R A]
  证明: tendsto_abv_eval₂_atTop _ abv p hd h₀ hz
-/
theorem tendsto_abv_aeval_atTop {R A k α : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (abv : A -> k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p)
    (h₀ : algebraMap R A p.leadingCoeff != 0) {l : Filter α} {z : α -> A}
    (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (aeval (z x) p)) l atTop :=
  tendsto_abv_eval₂_atTop _ abv p hd h₀ hz

variable {α R : Type*} [NormedRing R] [IsAbsoluteValue (norm : R -> Real)]

/--
theorem `tendsto_norm_atTop` / 定理 `tendsto_norm_atTop`

English:
theorem tendsto_norm_atTop
  statement: (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α -> R}
  proof: p.tendsto_abv_atTop norm h hz

中文:
定理 tendsto_norm_atTop
  结论: (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α -> R}
  证明: p.tendsto_abv_atTop norm h hz

Depends on / 依赖: p.tendsto_abv_atTop, tendsto_abv_atTop
-/
theorem tendsto_norm_atTop (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α -> R}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) : Tendsto (fun x => ‖p.eval (z x)‖) l atTop :=
  p.tendsto_abv_atTop norm h hz

/--
theorem `exists_forall_norm_le` / 定理 `exists_forall_norm_le`

English:
theorem exists_forall_norm_le
  given: [ProperSpace R] (p : R[X])
  statement: exists x, forall y, ‖p.eval x‖ <= ‖p.eval y‖
  proof: if hp0 : 0 < degree p then
p.continuous.norm.exists_forall_le p.tendsto_norm_atTop hp0 tendsto_norm_cocompact_atTop
  else
    ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

中文:
定理 exists_forall_norm_le
  条件: [命题erSpace R] (p : R[X])
  结论: 存在 x, 对任意 y, ‖p.eval x‖ <= ‖p.eval y‖
  证明: if hp0 : 0 < degree p then
p.continuous.norm.exists_forall_le p.tendsto_norm_atTop hp0 tendsto_norm_cocompact_atTop
  else
    ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

Depends on / 依赖: continuous, degree, eq_C_of_degree_le_zero, exists_forall_le, le_of_not_gt, p.coeff, p.continuous.norm.exists_forall_le, p.tendsto_norm_atTop, tendsto_norm_atTop, tendsto_norm_cocompact_atTop
-/
theorem exists_forall_norm_le [ProperSpace R] (p : R[X]) : exists x, forall y, ‖p.eval x‖ <= ‖p.eval y‖ :=
  if hp0 : 0 < degree p then
p.continuous.norm.exists_forall_le p.tendsto_norm_atTop hp0 tendsto_norm_cocompact_atTop
  else
    ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

/--
theorem `isProperMap_eval` / 定理 `isProperMap_eval`

English:
theorem isProperMap_eval
  given: [ProperSpace R] (p : R[X]) (h : 0 < degree p)
  statement: IsProperMap p.eval
  proof: isProperMap_iff_tendsto_cocompact.mpr ⟨by fun_prop, by
    rw [← Metric.cobounded_eq_cocompact]; rw [← tendsto_norm_atTop_iff_cobounded]
    exact p.tendsto_norm_atTop h tendsto_norm_cobounded_atTop⟩

中文:
定理 isProperMap_eval
  条件: [命题erSpace R] (p : R[X]) (h : 0 < degree p)
  结论: Is命题erMap p.eval
  证明: isProperMap_iff_tendsto_cocompact.mpr ⟨by fun_prop, by
    rw [← Metric.cobounded_eq_cocompact]; rw [← tendsto_norm_atTop_iff_cobounded]
    exact p.tendsto_norm_atTop h tendsto_norm_cobounded_atTop⟩

Depends on / 依赖: Metric, Metric.cobounded_eq_cocompact, cobounded_eq_cocompact, fun_prop, isProperMap_iff_tendsto_cocompact, isProperMap_iff_tendsto_cocompact.mpr, p.tendsto_norm_atTop, tendsto_norm_atTop, tendsto_norm_atTop_iff_cobounded, tendsto_norm_cobounded_atTop
-/
theorem isProperMap_eval [ProperSpace R] (p : R[X]) (h : 0 < degree p) : IsProperMap p.eval :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨by fun_prop, by
    rw [← Metric.cobounded_eq_cocompact]; rw [← tendsto_norm_atTop_iff_cobounded]
    exact p.tendsto_norm_atTop h tendsto_norm_cobounded_atTop⟩

/--
theorem `isClosedMap_eval` / 定理 `isClosedMap_eval`

English:
theorem isClosedMap_eval
  given: [ProperSpace R] (p : R[X])
  statement: IsClosedMap p.eval
  proof: by
  obtain h | h := le_or_gt p.degree 0
  · rw [degree_le_zero_iff.mp h]; simpa using! isClosedMap_const
  · exact (p.isProperMap_eval h).isClosedMap

中文:
定理 isClosedMap_eval
  条件: [命题erSpace R] (p : R[X])
  结论: IsClosedMap p.eval
  证明: by
  obtain h | h := le_or_gt p.degree 0
  · rw [degree_le_zero_iff.mp h]; simpa using! isClosedMap_const
  · exact (p.isProperMap_eval h).isClosedMap

Depends on / 依赖: degree, degree_le_zero_iff, degree_le_zero_iff.mp, isClosedMap, isClosedMap_const, isProperMap_eval, le_or_gt, p.degree, p.isProperMap_eval
-/
theorem isClosedMap_eval [ProperSpace R] (p : R[X]) : IsClosedMap p.eval := by
  obtain h | h := le_or_gt p.degree 0
  · rw [degree_le_zero_iff.mp h]; simpa using! isClosedMap_const
  · exact (p.isProperMap_eval h).isClosedMap

variable (R) in
/--
theorem `_root_.isClosedMap_pow` / 定理 `_root_.isClosedMap_pow`

English:
theorem _root_.isClosedMap_pow
  given: [ProperSpace R] (n : Nat)
  statement: IsClosedMap fun x : R => x ^ n
  proof: by
  simpa [eval_X_pow] using (X ^ n).isClosedMap_eval

中文:
定理 _root_.isClosedMap_pow
  条件: [命题erSpace R] (n : 自然数)
  结论: IsClosedMap fun x : R => x ^ n
  证明: by
  simpa [eval_X_pow] using (X ^ n).isClosedMap_eval

Depends on / 依赖: eval_X_pow, isClosedMap_eval
-/
theorem _root_.isClosedMap_pow [ProperSpace R] (n : Nat) : IsClosedMap fun x : R => x ^ n := by
  simpa [eval_X_pow] using (X ^ n).isClosedMap_eval

section Roots

open Polynomial NNReal

variable {F K : Type*} [CommRing F] [NormedField K]

open Multiset

/--
theorem `eq_one_of_roots_le` / 定理 `eq_one_of_roots_le`

English:
theorem eq_one_of_roots_le
  statement: {p : F[X]} {f : F ->+* K} {B : Real} (hB : B < 0) (h1 : p.Monic)
  proof: h1.natDegree_eq_zero.mp (by
    contrapose! hB
    rw [← h1.natDegree_map f]; rw [Splits.natDegree_eq_card_roots h2] at hB
    obtain ⟨z, hz⟩ := card_pos_iff_exists_mem.mp (zero_lt_iff.mpr hB)
    exact le_trans (norm_nonneg _) (h3 z hz))

中文:
定理 eq_one_of_roots_le
  结论: {p : F[X]} {f : F ->+* K} {B : 实数} (hB : B < 0) (h1 : p.Monic)
  证明: h1.natDegree_eq_zero.mp (by
    contrapose! hB
    rw [← h1.natDegree_map f]; rw [Splits.natDegree_eq_card_roots h2] at hB
    obtain ⟨z, hz⟩ := card_pos_iff_exists_mem.mp (zero_lt_iff.mpr hB)
    exact le_trans (norm_nonneg _) (h3 z hz))

Depends on / 依赖: Splits, Splits.natDegree_eq_card_roots, card_pos_iff_exists_mem, card_pos_iff_exists_mem.mp, contrapose, h1.natDegree_eq_zero.mp, h1.natDegree_map, le_trans, natDegree_eq_card_roots, natDegree_eq_zero, natDegree_map, norm_nonneg, zero_lt_iff, zero_lt_iff.mpr
-/
theorem eq_one_of_roots_le {p : F[X]} {f : F ->+* K} {B : Real} (hB : B < 0) (h1 : p.Monic)
    (h2 : Splits (p.map f)) (h3 : forall z in (map f p).roots, ‖z‖ <= B) : p = 1 :=
  h1.natDegree_eq_zero.mp (by
    contrapose! hB
    rw [← h1.natDegree_map f]; rw [Splits.natDegree_eq_card_roots h2] at hB
    obtain ⟨z, hz⟩ := card_pos_iff_exists_mem.mp (zero_lt_iff.mpr hB)
    exact le_trans (norm_nonneg _) (h3 z hz))

/--
theorem `coeff_le_of_roots_le` / 定理 `coeff_le_of_roots_le`

English:
theorem coeff_le_of_roots_le
  statement: {p : F[X]} {f : F ->+* K} {B : Real} (i : Nat) (h1 : p.Monic)
  proof: by
  obtain hB | hB := lt_or_ge B 0
  · rw [eq_one_of_roots_le hB h1 h2 h3, Polynomial.map_one, natDegree_one, zero_tsub, pow_zero,
      one_mul, coeff_one]
    split_ifs with h <;> simp [h]
  rw [← h1.natDegree_map f]
  obtain hi | hi := lt_or_ge (map f p).natDegree i
  · rw [coeff_eq_zero_of_natD

中文:
定理 coeff_le_of_roots_le
  结论: {p : F[X]} {f : F ->+* K} {B : 实数} (i : 自然数) (h1 : p.Monic)
  证明: by
  obtain hB | hB := lt_or_ge B 0
  · rw [eq_one_of_roots_le hB h1 h2 h3, Polynomial.map_one, natDegree_one, zero_tsub, pow_zero,
      one_mul, coeff_one]
    split_ifs with h <;> simp [h]
  rw [← h1.natDegree_map f]
  obtain hi | hi := lt_or_ge (map f p).natDegree i
  · rw [coeff_eq_zero_of_natD

Depends on / 依赖: Polynomial, Polynomial.map_one, coeff_eq_esymm_roots_of_splits, coeff_eq_zero_of_natDegree_lt, coeff_one, eq_one_of_roots_le, h1.map, h1.natDegree_map, leadingCoeff, lt_or_ge, map_one, natDegree, natDegree_map, natDegree_one, norm_mul, norm_neg, norm_one, norm_pow, norm_zero, one_mul
-/
theorem coeff_le_of_roots_le {p : F[X]} {f : F ->+* K} {B : Real} (i : Nat) (h1 : p.Monic)
    (h2 : Splits (p.map f)) (h3 : forall z in (map f p).roots, ‖z‖ <= B) :
    ‖(map f p).coeff i‖ <= B ^ (p.natDegree - i) * p.natDegree.choose i := by
  obtain hB | hB := lt_or_ge B 0
  · rw [eq_one_of_roots_le hB h1 h2 h3, Polynomial.map_one, natDegree_one, zero_tsub, pow_zero,
      one_mul, coeff_one]
    split_ifs with h <;> simp [h]
  rw [← h1.natDegree_map f]
  obtain hi | hi := lt_or_ge (map f p).natDegree i
  · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero]
    positivity
  rw [coeff_eq_esymm_roots_of_splits h2 hi]; rw [(h1.map _).leadingCoeff]; rw [one_mul]; rw [norm_mul]; rw [norm_pow]; rw [norm_neg]; rw [norm_one]; rw [one_pow]; rw [one_mul]
  apply ((norm_multiset_sum_le _).trans <| sum_le_card_nsmul _ _ fun r hr => _).trans
  · rw [Multiset.map_map, card_map, card_powersetCard, ← Splits.natDegree_eq_card_roots h2,
      Nat.choose_symm hi, mul_comm, nsmul_eq_mul]
  intro r hr
  simp_rw [Multiset.mem_map] at hr
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hr
  rw [mem_powersetCard] at hs
  lift B to Real>=0 using hB
  rw [← coe_nnnorm]; rw [← NNReal.coe_pow]; rw [NNReal.coe_le_coe]; rw [← nnnormHom_apply]; rw [← MonoidHom.coe_coe]; rw [MonoidHom.map_multiset_prod]
  refine (prod_le_pow_card _ B fun x hx => ?_).trans_eq (by rw [card_map, hs.2])
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
  exact h3 z (mem_of_le hs.1 hz)

/--
theorem `coeff_bdd_of_roots_le` / 定理 `coeff_bdd_of_roots_le`

English:
theorem coeff_bdd_of_roots_le
  statement: {B : Real} {d : Nat} (f : F ->+* K) {p : F[X]} (h1 : p.Monic)
  proof: by
  obtain hB | hB := le_or_gt 0 B
  · apply (coeff_le_of_roots_le i h1 h2 h4).trans
    calc
      _ <= max B 1 ^ (p.natDegree - i) * p.natDegree.choose i := by gcongr; apply le_max_left
      _ <= max B 1 ^ d * p.natDegree.choose i := by
        gcongr
        · apply le_max_right
        · exact

中文:
定理 coeff_bdd_of_roots_le
  结论: {B : 实数} {d : 自然数} (f : F ->+* K) {p : F[X]} (h1 : p.Monic)
  证明: by
  obtain hB | hB := le_or_gt 0 B
  · apply (coeff_le_of_roots_le i h1 h2 h4).trans
    calc
      _ <= max B 1 ^ (p.natDegree - i) * p.natDegree.choose i := by gcongr; apply le_max_left
      _ <= max B 1 ^ d * p.natDegree.choose i := by
        gcongr
        · apply le_max_right
        · exact

Depends on / 依赖: Nat.sub_le, Polynomial, Polynomial.map_one, choose_le_middle, choose_mono, coeff_le_of_roots_le, coeff_one, d.choose, eq_one_of_roots_le, i.choose_le_middle, i.choose_mono, le_max_left, le_max_right, le_or_gt, le_trans, map_one, natDegree, one_le_mul_of_one_le_, p.natDegree, p.natDegree.choose
-/
theorem coeff_bdd_of_roots_le {B : Real} {d : Nat} (f : F ->+* K) {p : F[X]} (h1 : p.Monic)
    (h2 : Splits (p.map f)) (h3 : p.natDegree <= d) (h4 : forall z in (map f p).roots, ‖z‖ <= B) (i : Nat) :
    ‖(map f p).coeff i‖ <= max B 1 ^ d * d.choose (d / 2) := by
  obtain hB | hB := le_or_gt 0 B
  · apply (coeff_le_of_roots_le i h1 h2 h4).trans
    calc
      _ <= max B 1 ^ (p.natDegree - i) * p.natDegree.choose i := by gcongr; apply le_max_left
      _ <= max B 1 ^ d * p.natDegree.choose i := by
        gcongr
        · apply le_max_right
        · exact le_trans (Nat.sub_le _ _) h3
      _ <= max B 1 ^ d * d.choose (d / 2) := by
        gcongr; exact (i.choose_mono h3).trans (i.choose_le_middle d)
  · rw [eq_one_of_roots_le hB h1 h2 h4, Polynomial.map_one, coeff_one]
    refine le_trans ?_ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_right B 1)) ?_)
    · split_ifs <;> norm_num
    · exact mod_cast Nat.succ_le_iff.mpr (Nat.choose_pos (d.div_le_self 2))

end Roots

end Polynomial
