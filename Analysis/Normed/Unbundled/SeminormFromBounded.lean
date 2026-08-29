/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# seminormFromBounded

In this file, we prove [BGR, Proposition 1.2.1/2][bosch-guntzer-remmert] : given a nonzero
additive group seminorm on a commutative ring `R` such that for some `c : ℝ` and every `x y : R`,
the inequality `f (x * y) ≤ c * f x * f y)` is satisfied, we create a ring seminorm on `R`.

In the file comments, we will use the expression `f is multiplicatively bounded` to indicate that
this condition holds.


## Main Definitions

* `seminormFromBounded'` : the real-valued function sending `x ∈ R` to the supremum of
  `f(x*y)/f(y)`, where `y` runs over the elements of `R`.
* `seminormFromBounded` : the function `seminormFromBounded'` as a `RingSeminorm` on `R`.
* `normFromBounded` :`seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is
  nonnegative, multiplicatively bounded and subadditive, that it preserves `0` and negation, and
  that `f` has trivial kernel.


## Main Results

* `seminormFromBounded_isNonarchimedean` : if `f : R → ℝ` is a nonnegative, multiplicatively
  bounded, nonarchimedean function, then `seminormFromBounded' f` is nonarchimedean.
* `seminormFromBounded_of_mul_is_mul` : if `f : R → ℝ` is a nonnegative, multiplicatively bounded
  function and `x : R` is multiplicative for `f`, then `x` is multiplicative for
  `seminormFromBounded' f`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

seminormFromBounded, RingSeminorm, Nonarchimedean
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal

variable {R : Type _} [CommRing R] (f : R -> Real) {c : Real}

section seminormFromBounded

/--
Definition of `seminormFromBounded'` / `seminormFromBounded'` 的定义

English:
definition seminormFromBounded'
  signature: : R -> Real
  body: fun x => iSup fun y : R => f (x * y) / f y

中文:
定义 seminormFromBounded'
  签名: : R -> 实数
  定义体: fun x => iSup fun y : R => f (x * y) / f y
-/
def seminormFromBounded' : R -> Real := fun x => iSup fun y : R => f (x * y) / f y

variable {f}

/--
theorem `map_one_ne_zero` / 定理 `map_one_ne_zero`

English:
theorem map_one_ne_zero
  statement: (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
  proof: by
  intro h1
  specialize f_mul 1
  simp_rw [h1, one_mul, mul_zero, zero_mul] at f_mul
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f_ne_zero
exact hz (f_mul z).antisymm (f_nonneg z)

中文:
定理 map_one_ne_zero
  结论: (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
  证明: by
  intro h1
  specialize f_mul 1
  simp_rw [h1, one_mul, mul_zero, zero_mul] at f_mul
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f_ne_zero
exact hz (f_mul z).antisymm (f_nonneg z)

Depends on / 依赖: Function, Function.ne_iff.mp, antisymm, f_mul, f_ne_zero, f_nonneg, mul_zero, ne_iff, one_mul, simp_rw, specialize, zero_mul
-/
theorem map_one_ne_zero (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : f 1 != 0 := by
  intro h1
  specialize f_mul 1
  simp_rw [h1, one_mul, mul_zero, zero_mul] at f_mul
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f_ne_zero
exact hz (f_mul z).antisymm (f_nonneg z)

/--
theorem `map_pow_ne_zero` / 定理 `map_pow_ne_zero`

English:
theorem map_pow_ne_zero
  statement: (f_nonneg : 0 <= f) {x : R} (hx : IsUnit x) (hfx : f x != 0) (n : Nat)
  proof: by
  have h1 : f 1 != 0 := map_one_ne_zero (Function.ne_iff.mpr ⟨x, hfx⟩) f_nonneg f_mul
  intro hxn
  have : f 1 <= 0 := by simpa [← mul_pow, hxn] using f_mul (x ^ n) (hx.unit⁻¹ ^ n)
exact h1 this.antisymm (f_nonneg 1)

中文:
定理 map_pow_ne_zero
  结论: (f_nonneg : 0 <= f) {x : R} (hx : 是单位 x) (hfx : f x != 0) (n : 自然数)
  证明: by
  have h1 : f 1 != 0 := map_one_ne_zero (Function.ne_iff.mpr ⟨x, hfx⟩) f_nonneg f_mul
  intro hxn
  have : f 1 <= 0 := by simpa [← mul_pow, hxn] using f_mul (x ^ n) (hx.unit⁻¹ ^ n)
exact h1 this.antisymm (f_nonneg 1)

Depends on / 依赖: Function, Function.ne_iff.mpr, antisymm, f_mul, f_nonneg, hx.unit, map_one_ne_zero, mul_pow, ne_iff, this.antisymm
-/
theorem map_pow_ne_zero (f_nonneg : 0 <= f) {x : R} (hx : IsUnit x) (hfx : f x != 0) (n : Nat)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : f (x ^ n) != 0 := by
  have h1 : f 1 != 0 := map_one_ne_zero (Function.ne_iff.mpr ⟨x, hfx⟩) f_nonneg f_mul
  intro hxn
  have : f 1 <= 0 := by simpa [← mul_pow, hxn] using f_mul (x ^ n) (hx.unit⁻¹ ^ n)
exact h1 this.antisymm (f_nonneg 1)

/--
theorem `map_mul_zero_of_map_zero` / 定理 `map_mul_zero_of_map_zero`

English:
theorem map_mul_zero_of_map_zero
  statement: (f_nonneg : 0 <= f)
  proof: by
  replace f_mul : f (x * y) <= 0 := by simpa [hx] using f_mul x y
  exact le_antisymm f_mul (f_nonneg _)

中文:
定理 map_mul_zero_of_map_zero
  结论: (f_nonneg : 0 <= f)
  证明: by
  replace f_mul : f (x * y) <= 0 := by simpa [hx] using f_mul x y
  exact le_antisymm f_mul (f_nonneg _)

Depends on / 依赖: f_mul, f_nonneg, le_antisymm, replace
-/
theorem map_mul_zero_of_map_zero (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) {x : R} (hx : f x = 0)
    (y : R) : f (x * y) = 0 := by
  replace f_mul : f (x * y) <= 0 := by simpa [hx] using f_mul x y
  exact le_antisymm f_mul (f_nonneg _)

/--
theorem `seminormFromBounded_zero` / 定理 `seminormFromBounded_zero`

English:
theorem seminormFromBounded_zero
  given: (f_zero : f 0 = 0)
  statement: seminormFromBounded' f (0 : R) = 0
  proof: by
  simp_rw [seminormFromBounded', zero_mul, f_zero, zero_div, ciSup_const]

中文:
定理 seminormFromBounded_zero
  条件: (f_zero : f 0 = 0)
  结论: seminormFromBounded' f (0 : R) = 0
  证明: by
  simp_rw [seminormFromBounded', zero_mul, f_zero, zero_div, ciSup_const]

Depends on / 依赖: ciSup_const, f_zero, seminormFromBounded, simp_rw, zero_div, zero_mul
-/
theorem seminormFromBounded_zero (f_zero : f 0 = 0) : seminormFromBounded' f (0 : R) = 0 := by
  simp_rw [seminormFromBounded', zero_mul, f_zero, zero_div, ciSup_const]

/--
theorem `seminormFromBounded_aux` / 定理 `seminormFromBounded_aux`

English:
theorem seminormFromBounded_aux
  statement: (f_nonneg : 0 <= f)
  proof: by
  rcases (f_nonneg x).eq_or_lt' with hx | hx
  · simp [hx]
  · change 0 < f x at hx
    have hc : 0 <= c := by
      specialize f_mul x 1
      rw [mul_one]; rw [show c * f x * f 1 = c * f 1 * f x by ring]; rw [le_mul_iff_one_le_left hx] at f_mul
      replace f_nonneg : 0 <= f 1 := f_nonneg 1
      rcases f_nonneg.eq_or_lt' with h1 | h1
      · linarith [show (1 : Real) <= 0 by simpa [h1] using f_mul]
      · rw [← div_le_iff₀ h1] at f_mul
        linarith [one_div_pos.mpr h1]
    positivity

中文:
定理 seminormFromBounded_aux
  结论: (f_nonneg : 0 <= f)
  证明: by
  rcases (f_nonneg x).eq_or_lt' with hx | hx
  · simp [hx]
  · change 0 < f x at hx
    have hc : 0 <= c := by
      specialize f_mul x 1
      rw [mul_one]; rw [show c * f x * f 1 = c * f 1 * f x by ring]; rw [le_mul_iff_one_le_left hx] at f_mul
      replace f_nonneg : 0 <= f 1 := f_nonneg 1
      rcases f_nonneg.eq_or_lt' with h1 | h1
      · linarith [show (1 : Real) <= 0 by simpa [h1] using f_mul]
      · rw [← div_le_iff₀ h1] at f_mul
        linarith [one_div_pos.mpr h1]
    positivity

Depends on / 依赖: eq_or_lt, f_mul, f_nonneg, f_nonneg.eq_or_lt, le_mul_iff_one_le_left, mul_one, one_div_pos, one_div_pos.mpr, replace, specialize
-/
theorem seminormFromBounded_aux (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) : 0 <= c * f x := by
  rcases (f_nonneg x).eq_or_lt' with hx | hx
  · simp [hx]
  · change 0 < f x at hx
    have hc : 0 <= c := by
      specialize f_mul x 1
      rw [mul_one]; rw [show c * f x * f 1 = c * f 1 * f x by ring]; rw [le_mul_iff_one_le_left hx] at f_mul
      replace f_nonneg : 0 <= f 1 := f_nonneg 1
      rcases f_nonneg.eq_or_lt' with h1 | h1
      · linarith [show (1 : Real) <= 0 by simpa [h1] using f_mul]
      · rw [← div_le_iff₀ h1] at f_mul
        linarith [one_div_pos.mpr h1]
    positivity

/--
theorem `seminormFromBounded_bddAbove_range` / 定理 `seminormFromBounded_bddAbove_range`

English:
theorem seminormFromBounded_bddAbove_range
  statement: (f_nonneg : 0 <= f)
  proof: by
  use c * f x
  rintro r ⟨y, rfl⟩
  rcases (f_nonneg y).eq_or_lt' with hy0 | hy0
  · simpa [hy0] using seminormFromBounded_aux f_nonneg f_mul x
  · simpa [div_le_iff₀ hy0] using f_mul x y

中文:
定理 seminormFromBounded_bddAbove_range
  结论: (f_nonneg : 0 <= f)
  证明: by
  use c * f x
  rintro r ⟨y, rfl⟩
  rcases (f_nonneg y).eq_or_lt' with hy0 | hy0
  · simpa [hy0] using seminormFromBounded_aux f_nonneg f_mul x
  · simpa [div_le_iff₀ hy0] using f_mul x y

Depends on / 依赖: eq_or_lt, f_mul, f_nonneg, seminormFromBounded_aux
-/
theorem seminormFromBounded_bddAbove_range (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) :
    BddAbove (Set.range fun y => f (x * y) / f y) := by
  use c * f x
  rintro r ⟨y, rfl⟩
  rcases (f_nonneg y).eq_or_lt' with hy0 | hy0
  · simpa [hy0] using seminormFromBounded_aux f_nonneg f_mul x
  · simpa [div_le_iff₀ hy0] using f_mul x y

/--
theorem `seminormFromBounded_le` / 定理 `seminormFromBounded_le`

English:
theorem seminormFromBounded_le
  statement: (f_nonneg : 0 <= f)
  proof: by
  refine ciSup_le (fun y => ?_)
  rcases (f_nonneg y).eq_or_lt' with hy | hy
  · simpa [hy] using seminormFromBounded_aux f_nonneg f_mul x
  · rw [div_le_iff₀ hy]
    apply f_mul

中文:
定理 seminormFromBounded_le
  结论: (f_nonneg : 0 <= f)
  证明: by
  refine ciSup_le (fun y => ?_)
  rcases (f_nonneg y).eq_or_lt' with hy | hy
  · simpa [hy] using seminormFromBounded_aux f_nonneg f_mul x
  · rw [div_le_iff₀ hy]
    apply f_mul

Depends on / 依赖: ciSup_le, eq_or_lt, f_mul, f_nonneg, seminormFromBounded_aux
-/
theorem seminormFromBounded_le (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) :
    seminormFromBounded' f x <= c * f x := by
  refine ciSup_le (fun y => ?_)
  rcases (f_nonneg y).eq_or_lt' with hy | hy
  · simpa [hy] using seminormFromBounded_aux f_nonneg f_mul x
  · rw [div_le_iff₀ hy]
    apply f_mul

/--
theorem `seminormFromBounded_ge` / 定理 `seminormFromBounded_ge`

English:
theorem seminormFromBounded_ge
  statement: (f_nonneg : 0 <= f)
  proof: by
  by_cases h1 : f 1 = 0
  · specialize f_mul x 1
    rw [mul_one]; rw [h1]; rw [mul_zero] at f_mul
    have hx0 : f x = 0 := f_mul.antisymm (f_nonneg _)
    rw [hx0]; rw [h1]; rw [zero_mul]
  · rw [mul_comm, ← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) h1)]
    conv_lhs => rw [← mul_one x]
    exact le_ciSup (seminormFromBounded_bddAbove_range f_nonneg f_mul x) (1 : R)

中文:
定理 seminormFromBounded_ge
  结论: (f_nonneg : 0 <= f)
  证明: by
  by_cases h1 : f 1 = 0
  · specialize f_mul x 1
    rw [mul_one]; rw [h1]; rw [mul_zero] at f_mul
    have hx0 : f x = 0 := f_mul.antisymm (f_nonneg _)
    rw [hx0]; rw [h1]; rw [zero_mul]
  · rw [mul_comm, ← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) h1)]
    conv_lhs => rw [← mul_one x]
    exact le_ciSup (seminormFromBounded_bddAbove_range f_nonneg f_mul x) (1 : R)

Depends on / 依赖: antisymm, conv_lhs, f_mul, f_mul.antisymm, f_nonneg, le_ciSup, lt_of_le_of_ne, mul_comm, mul_one, mul_zero, seminormFromBounded_bddAbove_range, specialize, zero_mul
-/
theorem seminormFromBounded_ge (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) :
    f x <= f 1 * seminormFromBounded' f x := by
  by_cases h1 : f 1 = 0
  · specialize f_mul x 1
    rw [mul_one]; rw [h1]; rw [mul_zero] at f_mul
    have hx0 : f x = 0 := f_mul.antisymm (f_nonneg _)
    rw [hx0]; rw [h1]; rw [zero_mul]
  · rw [mul_comm, ← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) h1)]
    conv_lhs => rw [← mul_one x]
    exact le_ciSup (seminormFromBounded_bddAbove_range f_nonneg f_mul x) (1 : R)

/--
theorem `seminormFromBounded_nonneg` / 定理 `seminormFromBounded_nonneg`

English:
theorem seminormFromBounded_nonneg
  statement: (f_nonneg : 0 <= f)
  proof: fun x =>
  le_csSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) ⟨1, rfl⟩
    (div_nonneg (f_nonneg _) (f_nonneg _))

中文:
定理 seminormFromBounded_nonneg
  结论: (f_nonneg : 0 <= f)
  证明: fun x =>
  le_csSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) ⟨1, rfl⟩
    (div_nonneg (f_nonneg _) (f_nonneg _))
-/
theorem seminormFromBounded_nonneg (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) :
    0 <= seminormFromBounded' f := fun x =>
  le_csSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) ⟨1, rfl⟩
    (div_nonneg (f_nonneg _) (f_nonneg _))

/--
theorem `seminormFromBounded_eq_zero_iff` / 定理 `seminormFromBounded_eq_zero_iff`

English:
theorem seminormFromBounded_eq_zero_iff
  statement: (f_nonneg : 0 <= f)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hf := seminormFromBounded_ge f_nonneg f_mul x
    rw [h]; rw [mul_zero] at hf
    exact hf.antisymm (f_nonneg _)
  · have hf : seminormFromBounded' f x <= c * f x :=
      seminormFromBounded_le f_nonneg f_mul x
    rw [h]; rw [mul_zero] at hf
    exact hf.antisymm (seminormFromBounded_nonneg f_nonneg f_mul x)

中文:
定理 seminormFromBounded_eq_zero_iff
  结论: (f_nonneg : 0 <= f)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hf := seminormFromBounded_ge f_nonneg f_mul x
    rw [h]; rw [mul_zero] at hf
    exact hf.antisymm (f_nonneg _)
  · have hf : seminormFromBounded' f x <= c * f x :=
      seminormFromBounded_le f_nonneg f_mul x
    rw [h]; rw [mul_zero] at hf
    exact hf.antisymm (seminormFromBounded_nonneg f_nonneg f_mul x)

Depends on / 依赖: antisymm, f_mul, f_nonneg, hf.antisymm, mul_zero, seminormFromBounded, seminormFromBounded_ge, seminormFromBounded_le, seminormFromBounded_nonneg
-/
theorem seminormFromBounded_eq_zero_iff (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x : R) :
    seminormFromBounded' f x = 0 ↔ f x = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hf := seminormFromBounded_ge f_nonneg f_mul x
    rw [h]; rw [mul_zero] at hf
    exact hf.antisymm (f_nonneg _)
  · have hf : seminormFromBounded' f x <= c * f x :=
      seminormFromBounded_le f_nonneg f_mul x
    rw [h]; rw [mul_zero] at hf
    exact hf.antisymm (seminormFromBounded_nonneg f_nonneg f_mul x)

/--
theorem `seminormFromBounded_neg` / 定理 `seminormFromBounded_neg`

English:
theorem seminormFromBounded_neg
  given: (f_neg : forall x : R, f (-x) = f x) (x : R)
  proof: by
  suffices ⨆ y, f (-x * y) / f y = ⨆ y, f (x * y) / f y by simpa only [seminormFromBounded']
  congr
  ext y
  rw [neg_mul]; rw [f_neg]

中文:
定理 seminormFromBounded_neg
  条件: (f_neg : 对任意 x : R, f (-x) = f x) (x : R)
  证明: by
  suffices ⨆ y, f (-x * y) / f y = ⨆ y, f (x * y) / f y by simpa only [seminormFromBounded']
  congr
  ext y
  rw [neg_mul]; rw [f_neg]

Depends on / 依赖: f_neg, neg_mul, seminormFromBounded
-/
theorem seminormFromBounded_neg (f_neg : forall x : R, f (-x) = f x) (x : R) :
    seminormFromBounded' f (-x) = seminormFromBounded' f x := by
  suffices ⨆ y, f (-x * y) / f y = ⨆ y, f (x * y) / f y by simpa only [seminormFromBounded']
  congr
  ext y
  rw [neg_mul]; rw [f_neg]

/--
theorem `seminormFromBounded_mul` / 定理 `seminormFromBounded_mul`

English:
theorem seminormFromBounded_mul
  statement: (f_nonneg : 0 <= f)
  proof: by
  apply ciSup_le
  by_cases hy : seminormFromBounded' f y = 0
  · rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul] at hy
    intro z
    rw [mul_comm x y]; rw [mul_assoc]; rw [map_mul_zero_of_map_zero f_nonneg f_mul hy (x * z)]; rw [zero_div]
    exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul x)
      (seminormFromBounded_nonneg f_nonneg f_mul y)
  · intro z
    rw [← div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]
    apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z
    rw [div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]; rw [div_mul_eq_mul_div]
    by_cases hz : f z = 0
    · have hxyz : f (z * (x * y)) = 0 := map_mul_zero_of_map_zero f_nonneg f_mul hz _
      simp_rw [mul_comm, hxyz, zero_div]
      exact div_nonneg (mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _))
        (f_nonneg _)
    · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))]
      by_cases hxz : f (x * z) = 0
      · rw [mul_comm x y, mul_assoc, mul_comm y, map_mul_zero_of_map_zero f_nonneg f_mul hxz y]
        exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _)
      · rw [← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hxz)]
        apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) (x * z)
        rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hxz)]; rw [mul_comm x y]; rw [mul_assoc]

中文:
定理 seminormFromBounded_mul
  结论: (f_nonneg : 0 <= f)
  证明: by
  apply ciSup_le
  by_cases hy : seminormFromBounded' f y = 0
  · rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul] at hy
    intro z
    rw [mul_comm x y]; rw [mul_assoc]; rw [map_mul_zero_of_map_zero f_nonneg f_mul hy (x * z)]; rw [zero_div]
    exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul x)
      (seminormFromBounded_nonneg f_nonneg f_mul y)
  · intro z
    rw [← div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]
    apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z
    rw [div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]; rw [div_mul_eq_mul_div]
    by_cases hz : f z = 0
    · have hxyz : f (z * (x * y)) = 0 := map_mul_zero_of_map_zero f_nonneg f_mul hz _
      simp_rw [mul_comm, hxyz, zero_div]
      exact div_nonneg (mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _))
        (f_nonneg _)
    · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))]
      by_cases hxz : f (x * z) = 0
      · rw [mul_comm x y, mul_assoc, mul_comm y, map_mul_zero_of_map_zero f_nonneg f_mul hxz y]
        exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _)
      · rw [← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hxz)]
        apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) (x * z)
        rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hxz)]; rw [mul_comm x y]; rw [mul_assoc]

Depends on / 依赖: ciSup_le, f_mul, f_nonneg, le_ciSup_of_le, lt_of_le_of_ne, map_mul_zero_of_map_zero, mul_assoc, mul_comm, mul_nonneg, seminormFromBounded, seminormFromBounded_bddAbove_range, seminormFromBounded_eq_zero_iff, seminormFromBounded_nonneg, zero_div
-/
theorem seminormFromBounded_mul (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (x y : R) :
    seminormFromBounded' f (x * y) <= seminormFromBounded' f x * seminormFromBounded' f y := by
  apply ciSup_le
  by_cases hy : seminormFromBounded' f y = 0
  · rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul] at hy
    intro z
    rw [mul_comm x y]; rw [mul_assoc]; rw [map_mul_zero_of_map_zero f_nonneg f_mul hy (x * z)]; rw [zero_div]
    exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul x)
      (seminormFromBounded_nonneg f_nonneg f_mul y)
  · intro z
    rw [← div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]
    apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z
    rw [div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]; rw [div_mul_eq_mul_div]
    by_cases hz : f z = 0
    · have hxyz : f (z * (x * y)) = 0 := map_mul_zero_of_map_zero f_nonneg f_mul hz _
      simp_rw [mul_comm, hxyz, zero_div]
      exact div_nonneg (mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _))
        (f_nonneg _)
    · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))]
      by_cases hxz : f (x * z) = 0
      · rw [mul_comm x y, mul_assoc, mul_comm y, map_mul_zero_of_map_zero f_nonneg f_mul hxz y]
        exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _)
      · rw [← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hxz)]
        apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) (x * z)
        rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hxz)]; rw [mul_comm x y]; rw [mul_assoc]

/--
theorem `seminormFromBounded_one` / 定理 `seminormFromBounded_one`

English:
theorem seminormFromBounded_one
  statement: (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
  proof: by
  simp_rw [seminormFromBounded', one_mul]
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero]; exact zero_le_one
    · rw [div_self hx]
  · rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
    have h_bdd : BddAbove (Set.range fun y => f y / f y) := by
      use (1 : Real)
      rintro r ⟨y, rfl⟩
      by_cases hy : f y = 0
      · simp only [hy, div_zero, zero_le_one]
      · simp only [div_self hy, le_refl]
    exact le_ciSup h_bdd (1 : R)

中文:
定理 seminormFromBounded_one
  结论: (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
  证明: by
  simp_rw [seminormFromBounded', one_mul]
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero]; exact zero_le_one
    · rw [div_self hx]
  · rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
    have h_bdd : BddAbove (Set.range fun y => f y / f y) := by
      use (1 : Real)
      rintro r ⟨y, rfl⟩
      by_cases hy : f y = 0
      · simp only [hy, div_zero, zero_le_one]
      · simp only [div_self hy, le_refl]
    exact le_ciSup h_bdd (1 : R)

Depends on / 依赖: BddAbove, Set.range, ciSup_le, div_self, div_zero, f_mul, f_ne_zero, f_nonneg, h_bdd, le_antisymm, le_ciSup, le_refl, map_one_ne_zero, one_mul, seminormFromBounded, simp_rw, zero_le_one
-/
theorem seminormFromBounded_one (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) :
    seminormFromBounded' f 1 = 1 := by
  simp_rw [seminormFromBounded', one_mul]
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero]; exact zero_le_one
    · rw [div_self hx]
  · rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
    have h_bdd : BddAbove (Set.range fun y => f y / f y) := by
      use (1 : Real)
      rintro r ⟨y, rfl⟩
      by_cases hy : f y = 0
      · simp only [hy, div_zero, zero_le_one]
      · simp only [div_self hy, le_refl]
    exact le_ciSup h_bdd (1 : R)

/--
theorem `seminormFromBounded_one_le` / 定理 `seminormFromBounded_one_le`

English:
theorem seminormFromBounded_one_le
  statement: (f_nonneg : 0 <= f)
  proof: by
  by_cases! f_ne_zero : f != 0
  · exact le_of_eq (seminormFromBounded_one f_ne_zero f_nonneg f_mul)
  · simp_rw [seminormFromBounded', one_mul]
    refine ciSup_le (fun _ => ?_)
    simp only [f_ne_zero, Pi.zero_apply, div_zero, zero_le_one]

中文:
定理 seminormFromBounded_one_le
  结论: (f_nonneg : 0 <= f)
  证明: by
  by_cases! f_ne_zero : f != 0
  · exact le_of_eq (seminormFromBounded_one f_ne_zero f_nonneg f_mul)
  · simp_rw [seminormFromBounded', one_mul]
    refine ciSup_le (fun _ => ?_)
    simp only [f_ne_zero, Pi.zero_apply, div_zero, zero_le_one]

Depends on / 依赖: Pi.zero_apply, ciSup_le, div_zero, f_mul, f_ne_zero, f_nonneg, le_of_eq, one_mul, seminormFromBounded, seminormFromBounded_one, simp_rw, zero_apply, zero_le_one
-/
theorem seminormFromBounded_one_le (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) :
    seminormFromBounded' f 1 <= 1 := by
  by_cases! f_ne_zero : f != 0
  · exact le_of_eq (seminormFromBounded_one f_ne_zero f_nonneg f_mul)
  · simp_rw [seminormFromBounded', one_mul]
    refine ciSup_le (fun _ => ?_)
    simp only [f_ne_zero, Pi.zero_apply, div_zero, zero_le_one]

/--
theorem `seminormFromBounded_add` / 定理 `seminormFromBounded_add`

English:
theorem seminormFromBounded_add
  statement: (f_nonneg : 0 <= f)
  proof: by
  refine ciSup_le (fun z => ?_)
  suffices hf : f ((x + y) * z) / f z <= f (x * z) / f z + f (y * z) / f z by
    exact le_trans hf (add_le_add
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z (le_refl _))
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z (le_refl _)))
  by_cases hz : f z = 0
  · simp only [hz, div_zero, zero_add, le_refl]
  · rw [← add_div, div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul]
    exact f_add _ _

中文:
定理 seminormFromBounded_add
  结论: (f_nonneg : 0 <= f)
  证明: by
  refine ciSup_le (fun z => ?_)
  suffices hf : f ((x + y) * z) / f z <= f (x * z) / f z + f (y * z) / f z by
    exact le_trans hf (add_le_add
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z (le_refl _))
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z (le_refl _)))
  by_cases hz : f z = 0
  · simp only [hz, div_zero, zero_add, le_refl]
  · rw [← add_div, div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul]
    exact f_add _ _

Depends on / 依赖: add_div, add_le_add, add_mul, ciSup_le, div_le_div_iff_of_pos_right, div_zero, f_add, f_mul, f_nonneg, le_ciSup_of_le, le_refl, le_trans, lt_of_le_of_ne, seminormFromBounded_bddAbove_range, zero_add
-/
theorem seminormFromBounded_add (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y)
    (f_add : forall a b, f (a + b) <= f a + f b) (x y : R) :
    seminormFromBounded' f (x + y) <= seminormFromBounded' f x + seminormFromBounded' f y := by
  refine ciSup_le (fun z => ?_)
  suffices hf : f ((x + y) * z) / f z <= f (x * z) / f z + f (y * z) / f z by
    exact le_trans hf (add_le_add
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z (le_refl _))
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z (le_refl _)))
  by_cases hz : f z = 0
  · simp only [hz, div_zero, zero_add, le_refl]
  · rw [← add_div, div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul]
    exact f_add _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `seminormFromBounded` / `seminormFromBounded` 的定义

English:
definition seminormFromBounded
  signature: (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
  body: seminormFromBounded' f
  map_zero' := seminormFromBounded_zero f_zero
  add_le' := seminormFromBounded_add f_nonneg f_mul f_add
  mul_le' := seminormFromBounded_mul f_nonneg f_mul
  neg' := seminormFromBounded_neg f_neg

中文:
定义 seminormFromBounded
  签名: (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
  定义体: seminormFromBounded' f
  map_zero' := seminormFromBounded_zero f_zero
  add_le' := seminormFromBounded_add f_nonneg f_mul f_add
  mul_le' := seminormFromBounded_mul f_nonneg f_mul
  neg' := seminormFromBounded_neg f_neg

Depends on / 依赖: seminormFromBounded
-/
def seminormFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y)
    (f_add : forall a b, f (a + b) <= f a + f b) (f_neg : forall x : R, f (-x) = f x) : RingSeminorm R where
  toFun := seminormFromBounded' f
  map_zero' := seminormFromBounded_zero f_zero
  add_le' := seminormFromBounded_add f_nonneg f_mul f_add
  mul_le' := seminormFromBounded_mul f_nonneg f_mul
  neg' := seminormFromBounded_neg f_neg

/--
theorem `seminormFromBounded_isNonarchimedean` / 定理 `seminormFromBounded_isNonarchimedean`

English:
theorem seminormFromBounded_isNonarchimedean
  statement: (f_nonneg : 0 <= f)
  proof: by
  refine fun x y => ciSup_le (fun z => ?_)
  rw [le_max_iff]
  suffices hf : f ((x + y) * z) / f z <= f (x * z) / f z ∨ f ((x + y) * z) / f z <= f (y * z) / f z by
    rcases hf with hfx | hfy
· exact Or.inl le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z hfx
· exact Or.inr le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z hfy
  by_cases hz : f z = 0
  · simp only [hz, div_zero, le_refl, or_self_iff]
  · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz),
      div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff]
    exact hna _ _

中文:
定理 seminormFromBounded_isNonarchimedean
  结论: (f_nonneg : 0 <= f)
  证明: by
  refine fun x y => ciSup_le (fun z => ?_)
  rw [le_max_iff]
  suffices hf : f ((x + y) * z) / f z <= f (x * z) / f z ∨ f ((x + y) * z) / f z <= f (y * z) / f z by
    rcases hf with hfx | hfy
· exact Or.inl le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z hfx
· exact Or.inr le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z hfy
  by_cases hz : f z = 0
  · simp only [hz, div_zero, le_refl, or_self_iff]
  · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz),
      div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff]
    exact hna _ _

Depends on / 依赖: Or.inl, Or.inr, ciSup_le, div_le_div_iff_of_pos_right, div_zero, f_mul, f_nonneg, le_ciSup_of_le, le_max_iff, le_refl, lt_of_le_of_ne, or_self_iff, seminormFromBounded_bddAbove_range
-/
theorem seminormFromBounded_isNonarchimedean (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y)
    (hna : IsNonarchimedean f) : IsNonarchimedean (seminormFromBounded' f) := by
  refine fun x y => ciSup_le (fun z => ?_)
  rw [le_max_iff]
  suffices hf : f ((x + y) * z) / f z <= f (x * z) / f z ∨ f ((x + y) * z) / f z <= f (y * z) / f z by
    rcases hf with hfx | hfy
· exact Or.inl le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z hfx
· exact Or.inr le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z hfy
  by_cases hz : f z = 0
  · simp only [hz, div_zero, le_refl, or_self_iff]
  · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz),
      div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff]
    exact hna _ _

/--
theorem `seminormFromBounded_of_mul_apply` / 定理 `seminormFromBounded_of_mul_apply`

English:
theorem seminormFromBounded_of_mul_apply
  statement: (f_nonneg : 0 <= f)
  proof: by
  simp_rw [seminormFromBounded', hx, ← mul_div_assoc']
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero, mul_zero]; exact f_nonneg _
    · rw [div_self hx, mul_one]
  · by_cases! f_ne_zero : f != 0
    · conv_lhs => rw [← mul_one (f x)]
      rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
      have h_bdd : BddAbove (Set.range fun y => f x * (f y / f y)) := by
        use f x
        rintro r ⟨y, rfl⟩
        by_cases hy0 : f y = 0
        · simp only [hy0, div_zero, mul_zero]; exact f_nonneg _
        · simp only [div_self hy0, mul_one, le_refl]
      exact le_ciSup h_bdd (1 : R)
    · simp_rw [f_ne_zero, Pi.zero_apply, zero_div, zero_mul, ciSup_const]; rfl

中文:
定理 seminormFromBounded_of_mul_apply
  结论: (f_nonneg : 0 <= f)
  证明: by
  simp_rw [seminormFromBounded', hx, ← mul_div_assoc']
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero, mul_zero]; exact f_nonneg _
    · rw [div_self hx, mul_one]
  · by_cases! f_ne_zero : f != 0
    · conv_lhs => rw [← mul_one (f x)]
      rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
      have h_bdd : BddAbove (Set.range fun y => f x * (f y / f y)) := by
        use f x
        rintro r ⟨y, rfl⟩
        by_cases hy0 : f y = 0
        · simp only [hy0, div_zero, mul_zero]; exact f_nonneg _
        · simp only [div_self hy0, mul_one, le_refl]
      exact le_ciSup h_bdd (1 : R)
    · simp_rw [f_ne_zero, Pi.zero_apply, zero_div, zero_mul, ciSup_const]; rfl

Depends on / 依赖: BddAbove, Set.range, ciSup_le, conv_lhs, div_self, div_zero, f_mul, f_ne_zero, f_nonneg, h_bdd, le_antisymm, map_one_ne_zero, mul_div_assoc, mul_one, mul_zero, seminormFromBounded, simp_rw
-/
theorem seminormFromBounded_of_mul_apply (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) {x : R}
    (hx : forall y : R, f (x * y) = f x * f y) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded', hx, ← mul_div_assoc']
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero, mul_zero]; exact f_nonneg _
    · rw [div_self hx, mul_one]
  · by_cases! f_ne_zero : f != 0
    · conv_lhs => rw [← mul_one (f x)]
      rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
      have h_bdd : BddAbove (Set.range fun y => f x * (f y / f y)) := by
        use f x
        rintro r ⟨y, rfl⟩
        by_cases hy0 : f y = 0
        · simp only [hy0, div_zero, mul_zero]; exact f_nonneg _
        · simp only [div_self hy0, mul_one, le_refl]
      exact le_ciSup h_bdd (1 : R)
    · simp_rw [f_ne_zero, Pi.zero_apply, zero_div, zero_mul, ciSup_const]; rfl

/--
theorem `seminormFromBounded_of_mul_le` / 定理 `seminormFromBounded_of_mul_le`

English:
theorem seminormFromBounded_of_mul_le
  statement: (f_nonneg : 0 <= f) {x : R}
  proof: by
  simp_rw [seminormFromBounded']
  apply le_antisymm
  · refine ciSup_le (fun y => ?_)
    by_cases hy : f y = 0
    · rw [hy, div_zero]; exact f_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy)]; exact hx _
  · have h_bdd : BddAbove (Set.range fun y => f (x * y) / f y) := by
      use f x
      rintro r ⟨y, rfl⟩
      by_cases hy0 : f y = 0
      · simp only [hy0, div_zero]
        exact f_nonneg _
      · rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc,
          div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one]
        exact hx y
    convert! le_ciSup h_bdd (1 : R)
    by_cases h0 : f x = 0
    · rw [mul_one, h0, zero_div]
    · have heq : f 1 = 1 := by
        apply h_one.antisymm
        specialize hx 1
        rw [mul_one]; rw [le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (Ne.symm h0))] at hx
        exact hx
      rw [heq]; rw [mul_one]; rw [div_one]

中文:
定理 seminormFromBounded_of_mul_le
  结论: (f_nonneg : 0 <= f) {x : R}
  证明: by
  simp_rw [seminormFromBounded']
  apply le_antisymm
  · refine ciSup_le (fun y => ?_)
    by_cases hy : f y = 0
    · rw [hy, div_zero]; exact f_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy)]; exact hx _
  · have h_bdd : BddAbove (Set.range fun y => f (x * y) / f y) := by
      use f x
      rintro r ⟨y, rfl⟩
      by_cases hy0 : f y = 0
      · simp only [hy0, div_zero]
        exact f_nonneg _
      · rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc,
          div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one]
        exact hx y
    convert! le_ciSup h_bdd (1 : R)
    by_cases h0 : f x = 0
    · rw [mul_one, h0, zero_div]
    · have heq : f 1 = 1 := by
        apply h_one.antisymm
        specialize hx 1
        rw [mul_one]; rw [le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (Ne.symm h0))] at hx
        exact hx
      rw [heq]; rw [mul_one]; rw [div_one]

Depends on / 依赖: BddAbove, Set.range, ciSup_le, div_self, div_zero, f_nonneg, h_bdd, le_antisymm, lt_of_le_of_ne, mul_div_assoc, mul_one, seminormFromBounded, simp_rw
-/
theorem seminormFromBounded_of_mul_le (f_nonneg : 0 <= f) {x : R}
    (hx : forall y : R, f (x * y) <= f x * f y) (h_one : f 1 <= 1) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded']
  apply le_antisymm
  · refine ciSup_le (fun y => ?_)
    by_cases hy : f y = 0
    · rw [hy, div_zero]; exact f_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy)]; exact hx _
  · have h_bdd : BddAbove (Set.range fun y => f (x * y) / f y) := by
      use f x
      rintro r ⟨y, rfl⟩
      by_cases hy0 : f y = 0
      · simp only [hy0, div_zero]
        exact f_nonneg _
      · rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc,
          div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one]
        exact hx y
    convert! le_ciSup h_bdd (1 : R)
    by_cases h0 : f x = 0
    · rw [mul_one, h0, zero_div]
    · have heq : f 1 = 1 := by
        apply h_one.antisymm
        specialize hx 1
        rw [mul_one]; rw [le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (Ne.symm h0))] at hx
        exact hx
      rw [heq]; rw [mul_one]; rw [div_one]

/--
theorem `seminormFromBounded_nonzero` / 定理 `seminormFromBounded_nonzero`

English:
theorem seminormFromBounded_nonzero
  statement: (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
  proof: by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp f_ne_zero
  rw [Function.ne_iff]
  use x
  rw [ne_eq]; rw [Pi.zero_apply]; rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

中文:
定理 seminormFromBounded_nonzero
  结论: (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
  证明: by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp f_ne_zero
  rw [Function.ne_iff]
  use x
  rw [ne_eq]; rw [Pi.zero_apply]; rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

Depends on / 依赖: Function, Function.ne_iff, Function.ne_iff.mp, Pi.zero_apply, f_mul, f_ne_zero, f_nonneg, ne_eq, ne_iff, seminormFromBounded_eq_zero_iff, zero_apply
-/
theorem seminormFromBounded_nonzero (f_ne_zero : f != 0) (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) :
    seminormFromBounded' f != 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp f_ne_zero
  rw [Function.ne_iff]
  use x
  rw [ne_eq]; rw [Pi.zero_apply]; rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

/--
theorem `seminormFromBounded_ker` / 定理 `seminormFromBounded_ker`

English:
theorem seminormFromBounded_ker
  statement: (f_nonneg : 0 <= f)
  proof: by
  ext x
  exact seminormFromBounded_eq_zero_iff f_nonneg f_mul x

中文:
定理 seminormFromBounded_ker
  结论: (f_nonneg : 0 <= f)
  证明: by
  ext x
  exact seminormFromBounded_eq_zero_iff f_nonneg f_mul x

Depends on / 依赖: f_mul, f_nonneg, seminormFromBounded_eq_zero_iff
-/
theorem seminormFromBounded_ker (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) :
    seminormFromBounded' f ⁻¹' {0} = f ⁻¹' {0} := by
  ext x
  exact seminormFromBounded_eq_zero_iff f_nonneg f_mul x

/--
theorem `seminormFromBounded_is_norm_iff` / 定理 `seminormFromBounded_is_norm_iff`

English:
theorem seminormFromBounded_is_norm_iff
  statement: (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
  proof: by
  refine ⟨fun h0 => ?_, fun h_ker x hx => ?_⟩
  · rw [← seminormFromBounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h0 x h, fun h => by rw [h]; exact seminormFromBounded_zero f_zero⟩
  · rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff,
      ← seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

中文:
定理 seminormFromBounded_is_norm_iff
  结论: (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
  证明: by
  refine ⟨fun h0 => ?_, fun h_ker x hx => ?_⟩
  · rw [← seminormFromBounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h0 x h, fun h => by rw [h]; exact seminormFromBounded_zero f_zero⟩
  · rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff,
      ← seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

Depends on / 依赖: Set.mem_preimage, Set.mem_singleton_iff, f_mul, f_nonneg, f_zero, h_ker, mem_preimage, mem_singleton_iff, seminormFromBounded_eq_zero_iff, seminormFromBounded_ker, seminormFromBounded_zero
-/
theorem seminormFromBounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y)
    (f_add : forall a b, f (a + b) <= f a + f b) (f_neg : forall x : R, f (-x) = f x) :
    (forall x : R, (seminormFromBounded f_zero f_nonneg f_mul f_add f_neg).toFun x = 0 -> x = 0) ↔
      f ⁻¹' {0} = {0} := by
  refine ⟨fun h0 => ?_, fun h_ker x hx => ?_⟩
  · rw [← seminormFromBounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h0 x h, fun h => by rw [h]; exact seminormFromBounded_zero f_zero⟩
  · rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff,
      ← seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

/--
Definition of `normFromBounded` / `normFromBounded` 的定义

English:
definition normFromBounded
  signature: (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
  body: { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

中文:
定义 normFromBounded
  签名: (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
  定义体: { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

Depends on / 依赖: eq_zero_of_map_eq_zero, f_add, f_ker, f_mul, f_neg, f_nonneg, f_zero, seminormFromBounded, seminormFromBounded_is_norm_iff
-/
def normFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y)
    (f_add : forall a b, f (a + b) <= f a + f b) (f_neg : forall x : R, f (-x) = f x)
    (f_ker : f ⁻¹' {0} = {0}) : RingNorm R :=
  { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

/--
theorem `seminormFromBounded_of_mul_is_mul` / 定理 `seminormFromBounded_of_mul_is_mul`

English:
theorem seminormFromBounded_of_mul_is_mul
  statement: (f_nonneg : 0 <= f)
  proof: by
  rw [seminormFromBounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

中文:
定理 seminormFromBounded_of_mul_is_mul
  结论: (f_nonneg : 0 <= f)
  证明: by
  rw [seminormFromBounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

Depends on / 依赖: Real.mul_iSup_of_nonneg, f_mul, f_nonneg, mul_assoc, mul_div_assoc, mul_iSup_of_nonneg, seminormFromBounded, seminormFromBounded_of_mul_apply
-/
theorem seminormFromBounded_of_mul_is_mul (f_nonneg : 0 <= f)
    (f_mul : forall x y : R, f (x * y) <= c * f x * f y) {x : R}
    (hx : forall y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromBounded' f (x * y) = seminormFromBounded' f x * seminormFromBounded' f y := by
  rw [seminormFromBounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

end seminormFromBounded
