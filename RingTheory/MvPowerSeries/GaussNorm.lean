/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Gauss norm for multivariate power series

This file defines the Gauss norm for power series. Given a multivariate power series `f`, a
function `v : R → ℝ` and a tuple `c` of real numbers, the Gauss norm is defined as the supremum of
the set of all values of `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.

## Main definitions and results

* `MvPowerSeries.gaussNorm` is the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`, where `f` is a multivariate power
  series, `v : R → ℝ` is a function and `c` is a tuple of real numbers.

* `MvPowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `MvPowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `MvPowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * ∏ i : t.support, c i` is bounded above (similarly for `g`), then
  the Gauss norm has the non-archimedean property.

* `MvPowerSeries.AchievesGaussNorm`: a type `i` is said to achieve gauss norm if
  `v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f`.

* `MvPowerSeries.gaussNorm_neg`: if `v` has the property that `∀ i, v i = v (-i)` then
  `gaussNorm v c (-f) = gaussNorm v c f `.

-/

@[expose] public section

namespace MvPowerSeries

variable {R σ : Type*} (v : R -> Real) (c : σ -> Real) (f : MvPowerSeries σ R)

section Semiring

variable [Semiring R]

/--
Definition of `gaussNorm` / `gaussNorm` 的定义

English:
definition gaussNorm
  signature: : Real
  body: ⨆ t : σ ->₀ Nat, v (coeff t f) * t.prod (c · ^ ·)

中文:
定义 gaussNorm
  签名: : 实数
  定义体: ⨆ t : σ ->₀ Nat, v (coeff t f) * t.prod (c · ^ ·)

Depends on / 依赖: t.prod
-/
noncomputable def gaussNorm : Real :=
   ⨆ t : σ ->₀ Nat, v (coeff t f) * t.prod (c · ^ ·)

/--
Definition of `HasGaussNorm` / `HasGaussNorm` 的定义

English:
abbreviation HasGaussNorm
  body: BddAbove (Set.range (fun (t : σ ->₀ Nat) => (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]

中文:
缩写 HasGaussNorm
  定义体: BddAbove (Set.range (fun (t : σ ->₀ Nat) => (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]

Depends on / 依赖: BddAbove, Set.range, t.prod
-/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : σ ->₀ Nat) => (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]
/--
theorem `gaussNorm_zero` / 定理 `gaussNorm_zero`

English:
theorem gaussNorm_zero
  given: (vZero : v 0 = 0)
  statement: gaussNorm v c 0 = 0
  proof: by simp [gaussNorm, vZero]

中文:
定理 gaussNorm_zero
  条件: (vZero : v 0 = 0)
  结论: gaussNorm v c 0 = 0
  证明: by simp [gaussNorm, vZero]

Depends on / 依赖: gaussNorm
-/
theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 := by simp [gaussNorm, vZero]

/--
lemma `le_gaussNorm` / 引理 `le_gaussNorm`

English:
lemma le_gaussNorm
  given: (hbd : HasGaussNorm v c f) (t : σ ->₀ Nat)
  proof: by
  apply le_ciSup hbd

中文:
引理 le_gaussNorm
  条件: (hbd : HasGaussNorm v c f) (t : σ ->₀ 自然数)
  证明: by
  apply le_ciSup hbd

Depends on / 依赖: le_ciSup
-/
lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : σ ->₀ Nat) :
    v (coeff t f) * t.prod (c · ^ ·) <= gaussNorm v c f := by
  apply le_ciSup hbd

/--
lemma `gaussNorm_nonneg` / 引理 `gaussNorm_nonneg`

English:
lemma gaussNorm_nonneg
  given: (vNonneg : forall a, v a >= 0)
  statement: 0 <= gaussNorm v c f
  proof: by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert! (le_gaussNorm v c f h 0)
      simp
  · simp [h]

中文:
引理 gaussNorm_nonneg
  条件: (vNonneg : 对任意 a, v a >= 0)
  结论: 0 <= gaussNorm v c f
  证明: by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert! (le_gaussNorm v c f h 0)
      simp
  · simp [h]

Depends on / 依赖: HasGaussNorm, constantCoeff, convert, gaussNorm, le_gaussNorm, vNonneg
-/
lemma gaussNorm_nonneg (vNonneg : forall a, v a >= 0) : 0 <= gaussNorm v c f := by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert! (le_gaussNorm v c f h 0)
      simp
  · simp [h]

/--
lemma `gaussNorm_eq_zero_iff` / 引理 `gaussNorm_eq_zero_iff`

English:
lemma gaussNorm_eq_zero_iff
  statement: (vZero : v 0 = 0) (vNonneg : forall a, v a >= 0)
  proof: by
  refine ⟨?_, fun hf => by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i in n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a => (fun i =>

中文:
引理 gaussNorm_eq_zero_iff
  结论: (vZero : v 0 = 0) (vNonneg : 对任意 a, v a >= 0)
  证明: by
  refine ⟨?_, fun hf => by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i in n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a => (fun i =>

Depends on / 依赖: Finset, Finset.prod_pos, MvPowerSeries, MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero, contrapose, f.coeff, h_eq_zero, le_gaussNorm, mul_pos, n.support, ne_of_gt, ne_zero_iff_exists_coeff_ne_zero, pow_pos, prod_pos, specialize, support
-/
lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : forall a, v a >= 0)
    (h_eq_zero : forall x : R, v x = 0 -> x = 0) (hc : forall i, 0 < c i) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf => by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i in n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a => (fun i => pow_pos (hc i) (n i)) i)
    specialize h_eq_zero (f.coeff n)
    grind
  _ <= _ := le_gaussNorm v c f hbd n

/--
lemma `gaussNorm_add_le_max` / 引理 `gaussNorm_add_le_max`

English:
lemma gaussNorm_add_le_max
  statement: (f g : MvPowerSeries σ R) (hc : 0 <= c)
  proof: by
  have H (t : σ ->₀ Nat) : 0 <= ∏ i in t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi => pow_nonneg (hc i) (t i))
  have Final (t : σ ->₀ Nat) : v ((coeff t) (f + g)) * ∏ i in t.support, c ↑i ^ t ↑i <=
      max (v ((coeff t) f) * ∏ i in t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * 

中文:
引理 gaussNorm_add_le_max
  结论: (f g : MvPowerSeries σ R) (hc : 0 <= c)
  证明: by
  have H (t : σ ->₀ Nat) : 0 <= ∏ i in t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi => pow_nonneg (hc i) (t i))
  have Final (t : σ ->₀ Nat) : v ((coeff t) (f + g)) * ∏ i in t.support, c ↑i ^ t ↑i <=
      max (v ((coeff t) f) * ∏ i in t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * 

Depends on / 依赖: Finset, Finset.prod_nonneg, max_choice, pow_nonneg, prod_nonneg, specialize, support, t.support
-/
lemma gaussNorm_add_le_max (f g : MvPowerSeries σ R) (hc : 0 <= c)
    (vNonneg : forall a, v a >= 0) (hv : IsNonarchimedean v)
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) <= max (gaussNorm v c f) (gaussNorm v c g) := by
  have H (t : σ ->₀ Nat) : 0 <= ∏ i in t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi => pow_nonneg (hc i) (t i))
  have Final (t : σ ->₀ Nat) : v ((coeff t) (f + g)) * ∏ i in t.support, c ↑i ^ t ↑i <=
      max (v ((coeff t) f) * ∏ i in t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * ∏ i in t.support, c ↑i ^ t ↑i) := by
    specialize hv (coeff t f) (coeff t g)
    rcases max_choice (v ((coeff t) f)) (v ((coeff t) g)) with h | h
    · have : max (v ((coeff t) f) * ∏ i in t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i in t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) f) * ∏ i in t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_left]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
    · have : max (v ((coeff t) f) * ∏ i in t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i in t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) g) * ∏ i in t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_right]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
  refine Real.iSup_le ?_ ?_
  · refine fun t => calc
    _ <= _ := Final t
    _ <= max (gaussNorm v c f) (gaussNorm v c g) := by
      simp only [le_sup_iff]
      rcases max_choice (v ((coeff t) f) * ∏ i in t.support, c i ^ t i)
        (v ((coeff t) g) * ∏ i in t.support, c i ^ t i) with h | h
      · left
        simpa [h] using! le_gaussNorm v c f hbfd t
      · right
        simpa [h] using! le_gaussNorm v c g hbgd t
  · simp only [le_sup_iff]
    left
    exact gaussNorm_nonneg v c f vNonneg

/--
lemma `c_prod_nonneg` / 引理 `c_prod_nonneg`

English:
lemma c_prod_nonneg
  given: (hc : 0 <= c) (t : σ ->₀ Nat)
  statement: 0 <= t.prod (c · ^ ·)
  proof: Finset.prod_nonneg (fun i _ => pow_nonneg (hc i) (t i))

中文:
引理 c_prod_nonneg
  条件: (hc : 0 <= c) (t : σ ->₀ 自然数)
  结论: 0 <= t.prod (c · ^ ·)
  证明: Finset.prod_nonneg (fun i _ => pow_nonneg (hc i) (t i))
-/
private lemma c_prod_nonneg (hc : 0 <= c) (t : σ ->₀ Nat) : 0 <= t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (hc i) (t i))

/--
lemma `gaussNorm_mul_le` / 引理 `gaussNorm_mul_le`

English:
lemma gaussNorm_mul_le
  statement: (f g : MvPowerSeries σ R) (hc : 0 <= c) (vNonneg : forall a, v a >= 0)
  proof: by
  classical
  refine Real.iSup_le ?_ ?_
  · intro t
    obtain ⟨k, hk, hsum⟩ := IsNonarchimedean.finset_image_add vZero vNonneg vna
      (fun a => coeff a.1 f * coeff a.2 g) (Finset.antidiagonal t)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk (Finset.nonempty

中文:
引理 gaussNorm_mul_le
  结论: (f g : MvPowerSeries σ R) (hc : 0 <= c) (vNonneg : 对任意 a, v a >= 0)
  证明: by
  classical
  refine Real.iSup_le ?_ ?_
  · intro t
    obtain ⟨k, hk, hsum⟩ := IsNonarchimedean.finset_image_add vZero vNonneg vna
      (fun a => coeff a.1 f * coeff a.2 g) (Finset.antidiagonal t)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk (Finset.nonempty

Depends on / 依赖: Finset, Finset.antidiagonal, Finset.mem_antidiagonal, Finset.nonempty_def.mpr, Finsupp, Finsupp.prod_add_index, IsNonarchimedean, IsNonarchimedean.finset_image_add, Real.iSup_le, antidiagonal, classical, finset_image_add, iSup_le, mem_antidiagonal, mul_le_mul, nonempty_def, prod_add_index, t.prod, vNonneg
-/
lemma gaussNorm_mul_le (f g : MvPowerSeries σ R) (hc : 0 <= c) (vNonneg : forall a, v a >= 0)
    (vMul : forall a b, v (a * b) <= v a * v b) (vna : IsNonarchimedean v)
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) <= gaussNorm v c f * gaussNorm v c g := by
  classical
  refine Real.iSup_le ?_ ?_
  · intro t
    obtain ⟨k, hk, hsum⟩ := IsNonarchimedean.finset_image_add vZero vNonneg vna
      (fun a => coeff a.1 f * coeff a.2 g) (Finset.antidiagonal t)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk (Finset.nonempty_def.mpr ⟨(t, 0), by simp⟩)
    have hprod : t.prod (c · ^ ·) = k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·) := by
      simp [← hk', Finsupp.prod_add_index' (h := (c · ^ ·)) (by grind) (by grind)]
    rw [hprod]
    refine (mul_le_mul hsum (by rfl) (mul_nonneg (c_prod_nonneg c hc k.1) (c_prod_nonneg c hc k.2))
      (vNonneg _)).trans ?_
    have : v ((coeff k.1) f * (coeff k.2) g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) <=
        (v (coeff k.1 f) * k.1.prod (c · ^ ·)) * (v (coeff k.2 g) * k.2.prod (c · ^ ·)) := by
      calc
      _ <= v (coeff k.1 f) * v (coeff k.2 g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) :=
        mul_le_mul (vMul _ _) (by rfl) (mul_nonneg (c_prod_nonneg c hc k.1)
          (c_prod_nonneg c hc k.2)) (mul_nonneg (vNonneg _) (vNonneg _))
      _ = _ := by ring
    exact this.trans (mul_le_mul (le_gaussNorm v c f hbfd k.1) (le_gaussNorm v c g hbgd k.2)
      (mul_nonneg (vNonneg _) (c_prod_nonneg c hc k.2)) (gaussNorm_nonneg v c f vNonneg))
  · exact mul_nonneg (gaussNorm_nonneg v c f vNonneg) (gaussNorm_nonneg v c g vNonneg)

end Semiring

variable [Ring R]

/--
Definition of `AchievesGaussNorm` / `AchievesGaussNorm` 的定义

English:
abbreviation AchievesGaussNorm
  signature: (i : σ ->₀ Nat)
  body: v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f

中文:
缩写 AchievesGaussNorm
  签名: (i : σ ->₀ 自然数)
  定义体: v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f

Depends on / 依赖: gaussNorm, i.prod
-/
abbrev AchievesGaussNorm (i : σ ->₀ Nat) : Prop :=
  v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f

/--
lemma `gaussNorm_neg` / 引理 `gaussNorm_neg`

English:
lemma gaussNorm_neg
  given: (vNeg : forall x, v (-x) = v x) (f : MvPowerSeries σ R)
  proof: by
  simp_rw [gaussNorm]
  have (t : σ ->₀ Nat) : (coeff t) (-f) = - (coeff t) f := by rfl
  simp_rw [this, vNeg]

中文:
引理 gaussNorm_neg
  条件: (vNeg : 对任意 x, v (-x) = v x) (f : MvPowerSeries σ R)
  证明: by
  simp_rw [gaussNorm]
  have (t : σ ->₀ Nat) : (coeff t) (-f) = - (coeff t) f := by rfl
  simp_rw [this, vNeg]

Depends on / 依赖: gaussNorm, simp_rw
-/
lemma gaussNorm_neg (vNeg : forall x, v (-x) = v x) (f : MvPowerSeries σ R) :
    gaussNorm v c (-f) = gaussNorm v c f := by
  simp_rw [gaussNorm]
  have (t : σ ->₀ Nat) : (coeff t) (-f) = - (coeff t) f := by rfl
  simp_rw [this, vNeg]

section absoluteValue

variable {α S : Type*} [LinearOrder S] [AddCommGroup α] (f : α -> S)

/--
lemma `ultrametric_strict` / 引理 `ultrametric_strict`

English:
lemma ultrametric_strict
  statement: (na : IsNonarchimedean f)
  proof: by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (na a b)
  rcases le_max_iff.mp (na (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa 

中文:
引理 ultrametric_strict
  结论: (na : IsNonarchimedean f)
  证明: by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (na a b)
  rcases le_max_iff.mp (na (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa 

Depends on / 依赖: absurd, add_comm, generalizing, hne.symm, le_antisymm, le_max_iff, le_max_iff.mp, le_of_lt, lt_of_ne, max_comm, max_eq_left, not_le, not_le.mpr, not_lt, not_lt.mp
-/
lemma ultrametric_strict (na : IsNonarchimedean f)
    (Neg : forall a, f a = f (-a)) {a b : α} (hne : f a != f b) : f (a + b) = max (f a) (f b) := by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (na a b)
  rcases le_max_iff.mp (na (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa [Neg b] using hab))

variable [Semiring S]

/--
lemma `Finset.Nonempty.map_sum_le_sup'_map` / 引理 `Finset.Nonempty.map_sum_le_sup'_map`

English:
lemma Finset.Nonempty.map_sum_le_sup'_map
  proof: by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (l

中文:
引理 Finset.Nonempty.map_sum_le_sup'_map
  证明: by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (l

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.le_sup, Finset.mem_cons, Finset.mem_singleton, Finset.sum_cons, Finset.sum_singleton, IH.choose_spec.left, IH.choose_spec.right, Nonempty, _iff, choose_spec, cons_induction, exists_eq_left, exists_eq_or_imp, le.trans, le_refl, le_sup, le_total, max_eq_left
-/
lemma Finset.Nonempty.map_sum_le_sup'_map
    {α S : Type*} [LinearOrder S] [AddCommMonoid α] (g : α -> S)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι -> α)
    (na : forall a b, g (a + b) <= max (g a) (g b)) :
    g (∑ i in s, f i) <= s.sup' hs fun x => g (f x) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total (g (∑ i in s, f i)) (g (f j))).imp ?_ ?_ <;> intro h
      · exact (na _ _).trans (max_eq_left h).le
· exact ⟨_, IH.choose_spec.left, (na _ _).trans
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

variable [DecidableEq σ] (f g : MvPowerSeries σ R)

/--
lemma `antidiagonal_dominant` / 引理 `antidiagonal_dominant`

English:
lemma antidiagonal_dominant
  statement: (i j : σ ->₀ Nat) (vna : IsNonarchimedean v)
  proof: by
  rw [← vMulEq] at hdom
  rw [coeff_mul]; rw [IsNonarchimedean.apply_sum_eq_of_lt vna (by grind) (k := (i]; rw [j))
    (s := Finset.antidiagonal (i + j)) (Finset.mem_antidiagonal.mpr rfl) hdom]

中文:
引理 antidiagonal_dominant
  结论: (i j : σ ->₀ 自然数) (vna : IsNonarchimedean v)
  证明: by
  rw [← vMulEq] at hdom
  rw [coeff_mul]; rw [IsNonarchimedean.apply_sum_eq_of_lt vna (by grind) (k := (i]; rw [j))
    (s := Finset.antidiagonal (i + j)) (Finset.mem_antidiagonal.mpr rfl) hdom]

Depends on / 依赖: Finset, Finset.antidiagonal, Finset.mem_antidiagonal.mpr, IsNonarchimedean, IsNonarchimedean.apply_sum_eq_of_lt, antidiagonal, apply_sum_eq_of_lt, coeff_mul, mem_antidiagonal, vMulEq
-/
lemma antidiagonal_dominant (i j : σ ->₀ Nat) (vna : IsNonarchimedean v)
    (vMulEq : forall a b, v (a * b) = v a * v b) (vNeg : forall a, v a = v (-a))
    (hdom : forall p in Finset.antidiagonal (i + j), p != (i, j) ->
      v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    v (coeff (i + j) (f * g)) = v (coeff i f * coeff j g) := by
  rw [← vMulEq] at hdom
  rw [coeff_mul]; rw [IsNonarchimedean.apply_sum_eq_of_lt vna (by grind) (k := (i]; rw [j))
    (s := Finset.antidiagonal (i + j)) (Finset.mem_antidiagonal.mpr rfl) hdom]

/--
lemma `gaussNorm_le_mul` / 引理 `gaussNorm_le_mul`

English:
lemma gaussNorm_le_mul
  statement: (vMulEq : forall a b, v (a * b) = v a * v b)
  proof: by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _ = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀]; rw [← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          h

中文:
引理 gaussNorm_le_mul
  结论: (vMulEq : 对任意 a b, v (a * b) = v a * v b)
  证明: by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _ = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀]; rw [← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          h

Depends on / 依赖: AchievesGaussNorm, Finsupp, Finsupp.prod_add_index, pow_add, prod_add_index, vMulEq
-/
lemma gaussNorm_le_mul (vMulEq : forall a b, v (a * b) = v a * v b)
    (vna : IsNonarchimedean v) (vNeg : forall a, v a = v (-a))
    (hbfg : HasGaussNorm v c (f * g))
    (hdom : exists i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      forall p in Finset.antidiagonal (i + j), p != (i, j) ->
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    gaussNorm v c f * gaussNorm v c g <= gaussNorm v c (f * g) := by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _ = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀]; rw [← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          have hprod : (i₀ + j₀).prod (c · ^ ·) = i₀.prod (c · ^ ·) * j₀.prod (c · ^ ·) := by
            simp [Finsupp.prod_add_index', pow_add]
          rw [hprod]; ring
    _ = v (coeff i₀ f * coeff j₀ g) * (i₀ + j₀).prod (c · ^ ·) := by rw [vMulEq]
    _ = v (coeff (i₀ + j₀) (f * g)) * (i₀ + j₀).prod (c · ^ ·) := by
      rw [antidiagonal_dominant v f g i₀ j₀ vna vMulEq vNeg hdom']
    _ <= gaussNorm v c (f * g) := le_gaussNorm v c (f * g) hbfg (i₀ + j₀)

/--
lemma `gaussNorm_mul_eq_mul` / 引理 `gaussNorm_mul_eq_mul`

English:
lemma gaussNorm_mul_eq_mul
  statement: (f g : MvPowerSeries σ R) (hf : HasGaussNorm v c f)
  proof: by
  by_cases hf' : f = 0
  · simp [hf', gaussNorm_zero v c vZero]
  by_cases hg' : g = 0
  · simp [hg', gaussNorm_zero v c vZero]
  have hf1 : gaussNorm v c f != 0 := by
    convert gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hf
    grind
  have hg1 : gaussNorm v c g != 0 := by
    conve

中文:
引理 gaussNorm_mul_eq_mul
  结论: (f g : MvPowerSeries σ R) (hf : HasGaussNorm v c f)
  证明: by
  by_cases hf' : f = 0
  · simp [hf', gaussNorm_zero v c vZero]
  by_cases hg' : g = 0
  · simp [hg', gaussNorm_zero v c vZero]
  have hf1 : gaussNorm v c f != 0 := by
    convert gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hf
    grind
  have hg1 : gaussNorm v c g != 0 := by
    conve

Depends on / 依赖: StrongLT, StrongLT.le, convert, gaussNorm, gaussNorm_eq_zero_iff, gaussNorm_le_mul, gaussNorm_mul_le, gaussNorm_zero, ge_antisymm_iff, ge_antisymm_iff.mpr, h_eq_zero, vMulEq, vNonneg
-/
lemma gaussNorm_mul_eq_mul (f g : MvPowerSeries σ R) (hf : HasGaussNorm v c f)
    (hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g))
    (vNonneg : forall a, v a >= 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v)
    (vMulEq : forall (a b : R), v (a * b) = v a * v b) (vNeg : forall (a : R), v (-a) = v a)
    (h_eq_zero : forall (x : R), v x = 0 -> x = 0) (hc : forall (i : σ), 0 < c i)
    (hdom : exists i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      forall p in Finset.antidiagonal (i + j), p != (i, j) -> v (coeff p.1 f * coeff p.2 g) <
      v (coeff i f) * v (coeff j g)) :
    gaussNorm v c (f * g) = gaussNorm v c f * gaussNorm v c g := by
  by_cases hf' : f = 0
  · simp [hf', gaussNorm_zero v c vZero]
  by_cases hg' : g = 0
  · simp [hg', gaussNorm_zero v c vZero]
  have hf1 : gaussNorm v c f != 0 := by
    convert gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hf
    grind
  have hg1 : gaussNorm v c g != 0 := by
    convert gaussNorm_eq_zero_iff v c g vZero vNonneg h_eq_zero hc hg
    grind
  apply ge_antisymm_iff.mpr
  constructor
  · exact gaussNorm_le_mul v c f g vMulEq vNA (by grind) hfg hdom
  · exact gaussNorm_mul_le v c f g (StrongLT.le hc) vNonneg (by grind) vNA vZero hf hg

end absoluteValue

end MvPowerSeries
