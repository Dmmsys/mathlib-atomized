/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Dirichlet convolution of sequences and products of L-series

We define the *Dirichlet convolution* `f ⍟ g` of two sequences `f g : ℕ → R` with values in a
semiring `R` by `(f ⍟ g) n = ∑ (k * m = n), f k * g m` when `n ≠ 0` and `(f ⍟ g) 0 = 0`.
Technically, this is done by transporting the existing definition for `ArithmeticFunction R`;
see `LSeries.convolution`. We show that these definitions agree (`LSeries.convolution_def`).

We then consider the case `R = ℂ` and show that `L (f ⍟ g) = L f * L g` on the common domain
of convergence of the L-series `L f` and `L g` of `f` and `g`; see `LSeries_convolution`
and `LSeries_convolution'`.
-/

@[expose] public section

open scoped LSeries.notation

open Complex LSeries

/-!
### Dirichlet convolution of two functions
-/

open Nat

/--
Definition of `toArithmeticFunction` / `toArithmeticFunction` 的定义

English:
definition toArithmeticFunction
  signature: {R : Type*} [Zero R] (f : Nat -> R)
  body: if n = 0 then 0 else f n
  map_zero' := rfl

中文:
定义 toArithmeticFunction
  签名: {R : 类型} [零 R] (f : 自然数 -> R)
  定义体: if n = 0 then 0 else f n
  map_zero' := rfl
-/
def toArithmeticFunction {R : Type*} [Zero R] (f : Nat -> R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else f n
  map_zero' := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toArithmeticFunction_congr` / 引理 `toArithmeticFunction_congr`

English:
lemma toArithmeticFunction_congr
  statement: {R : Type*} [Zero R] {f f' : Nat -> R}
  proof: by
  ext
  simp_all [toArithmeticFunction]

中文:
引理 toArithmeticFunction_congr
  结论: {R : 类型} [零 R] {f f' : 自然数 -> R}
  证明: by
  ext
  simp_all [toArithmeticFunction]

Depends on / 依赖: toArithmeticFunction
-/
lemma toArithmeticFunction_congr {R : Type*} [Zero R] {f f' : Nat -> R}
    (h : forall {n}, n != 0 -> f n = f' n) :
    toArithmeticFunction f = toArithmeticFunction f' := by
  ext
  simp_all [toArithmeticFunction]

set_option backward.isDefEq.respectTransparency false in
/-- If we consider an arithmetic function just as a function and turn it back into an
arithmetic function, it is the same as before. -/
@[simp]
/--
lemma `ArithmeticFunction.toArithmeticFunction_eq_self` / 引理 `ArithmeticFunction.toArithmeticFunction_eq_self`

English:
lemma ArithmeticFunction.toArithmeticFunction_eq_self
  statement: {R : Type*} [Zero R]
  proof: by
  ext n
  simp +contextual [toArithmeticFunction]

中文:
引理 ArithmeticFunction.toArithmeticFunction_eq_self
  结论: {R : 类型} [零 R]
  证明: by
  ext n
  simp +contextual [toArithmeticFunction]

Depends on / 依赖: contextual, toArithmeticFunction
-/
lemma ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R]
    (f : ArithmeticFunction R) :
    toArithmeticFunction f = f := by
  ext n
  simp +contextual [toArithmeticFunction]

/--
Definition of `LSeries.convolution` / `LSeries.convolution` 的定义

English:
definition LSeries.convolution
  signature: {R : Type*} [Semiring R] (f g : Nat -> R)
  body: ⇑(toArithmeticFunction f * toArithmeticFunction g)

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution

中文:
定义 LSeries.convolution
  签名: {R : 类型} [半环 R] (f g : 自然数 -> R)
  定义体: ⇑(toArithmeticFunction f * toArithmeticFunction g)

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution

Depends on / 依赖: toArithmeticFunction
-/
noncomputable def LSeries.convolution {R : Type*} [Semiring R] (f g : Nat -> R) : Nat -> R :=
  ⇑(toArithmeticFunction f * toArithmeticFunction g)

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution

/--
lemma `LSeries.convolution_congr` / 引理 `LSeries.convolution_congr`

English:
lemma LSeries.convolution_congr
  statement: {R : Type*} [Semiring R] {f f' g g' : Nat -> R}
  proof: by
  simp [convolution, toArithmeticFunction_congr hf, toArithmeticFunction_congr hg]

中文:
引理 LSeries.convolution_congr
  结论: {R : 类型} [半环 R] {f f' g g' : 自然数 -> R}
  证明: by
  simp [convolution, toArithmeticFunction_congr hf, toArithmeticFunction_congr hg]

Depends on / 依赖: convolution, toArithmeticFunction_congr
-/
lemma LSeries.convolution_congr {R : Type*} [Semiring R] {f f' g g' : Nat -> R}
    (hf : forall {n}, n != 0 -> f n = f' n) (hg : forall {n}, n != 0 -> g n = g' n) :
    f ⍟ g = f' ⍟ g' := by
  simp [convolution, toArithmeticFunction_congr hf, toArithmeticFunction_congr hg]

/--
lemma `ArithmeticFunction.coe_mul` / 引理 `ArithmeticFunction.coe_mul`

English:
lemma ArithmeticFunction.coe_mul
  given: {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
  proof: by
  simp [convolution]

中文:
引理 ArithmeticFunction.coe_mul
  条件: {R : 类型} [半环 R] (f g : ArithmeticFunction R)
  证明: by
  simp [convolution]

Depends on / 依赖: convolution
-/
lemma ArithmeticFunction.coe_mul {R : Type*} [Semiring R] (f g : ArithmeticFunction R) :
    f ⍟ g = ⇑(f * g) := by
  simp [convolution]

namespace LSeries

set_option backward.isDefEq.respectTransparency false in
/--
lemma `convolution_def` / 引理 `convolution_def`

English:
lemma convolution_def
  given: {R : Type*} [Semiring R] (f g : Nat -> R)
  proof: by
  ext n
  simpa [convolution, toArithmeticFunction] using
    Finset.sum_congr rfl fun p hp => by simp [ne_zero_of_mem_divisorsAntidiagonal hp]

@[simp]

中文:
引理 convolution_def
  条件: {R : 类型} [半环 R] (f g : 自然数 -> R)
  证明: by
  ext n
  simpa [convolution, toArithmeticFunction] using
    Finset.sum_congr rfl fun p hp => by simp [ne_zero_of_mem_divisorsAntidiagonal hp]

@[simp]

Depends on / 依赖: Finset, Finset.sum_congr, convolution, ne_zero_of_mem_divisorsAntidiagonal, sum_congr, toArithmeticFunction
-/
lemma convolution_def {R : Type*} [Semiring R] (f g : Nat -> R) :
    f ⍟ g = fun n => ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2 := by
  ext n
  simpa [convolution, toArithmeticFunction] using
    Finset.sum_congr rfl fun p hp => by simp [ne_zero_of_mem_divisorsAntidiagonal hp]

@[simp]
/--
lemma `convolution_map_zero` / 引理 `convolution_map_zero`

English:
lemma convolution_map_zero
  given: {R : Type*} [Semiring R] (f g : Nat -> R)
  statement: (f ⍟ g) 0 = 0
  proof: by
  simp [convolution_def]

中文:
引理 convolution_map_zero
  条件: {R : 类型} [半环 R] (f g : 自然数 -> R)
  结论: (f ⍟ g) 0 = 0
  证明: by
  simp [convolution_def]

Depends on / 依赖: convolution_def
-/
lemma convolution_map_zero {R : Type*} [Semiring R] (f g : Nat -> R) : (f ⍟ g) 0 = 0 := by
  simp [convolution_def]


/-!
### Multiplication of L-series
-/

/--
lemma `term_convolution` / 引理 `term_convolution`

English:
lemma term_convolution
  given: (f g : Nat -> Complex) (s : Complex) (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- now `n ≠ 0`
  rw [term_of_ne_zero hn]; rw [convolution_def]; rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have ⟨hp₁, hp₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  rw [term_of_ne_zero hp₁]; rw [term_of_ne_zero hp₂]; rw [mul

中文:
引理 term_convolution
  条件: (f g : 自然数 -> 复形) (s : 复形) (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- now `n ≠ 0`
  rw [term_of_ne_zero hn]; rw [convolution_def]; rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have ⟨hp₁, hp₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  rw [term_of_ne_zero hp₁]; rw [term_of_ne_zero hp₂]; rw [mul

Depends on / 依赖: eq_or_ne
-/
lemma term_convolution (f g : Nat -> Complex) (s : Complex) (n : Nat) :
    term (f ⍟ g) s n = ∑ p in n.divisorsAntidiagonal, term f s p.1 * term g s p.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- now `n ≠ 0`
  rw [term_of_ne_zero hn]; rw [convolution_def]; rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have ⟨hp₁, hp₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  rw [term_of_ne_zero hp₁]; rw [term_of_ne_zero hp₂]; rw [mul_comm_div]; rw [div_div]; rw [← mul_div_assoc]; rw [← natCast_mul_natCast_cpow]; rw [← cast_mul]; rw [mul_comm p.2]; rw [(mem_divisorsAntidiagonal.mp hp).1]

open Set in
/--
lemma `term_convolution'` / 引理 `term_convolution'`

English:
lemma term_convolution'
  given: (f g : Nat -> Complex) (s : Complex)
  proof: by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · -- show that both sides vanish when `n = 0`; this is the hardest part of the proof!
    refine (term_zero ..).trans ?_
    -- the right-hand sum is over the union below, but in each term, one factor is always zero
    have hS : (fun p => p.1 * p.2) 

中文:
引理 term_convolution'
  条件: (f g : 自然数 -> 复形) (s : 复形)
  证明: by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · -- show that both sides vanish when `n = 0`; this is the hardest part of the proof!
    refine (term_zero ..).trans ?_
    -- the right-hand sum is over the union below, but in each term, one factor is always zero
    have hS : (fun p => p.1 * p.2) 

Depends on / 依赖: eq_or_ne, hardest, term_zero, vanish
-/
lemma term_convolution' (f g : Nat -> Complex) (s : Complex) :
    term (f ⍟ g) s = fun n =>
      ∑' (b : (fun p : Nat × Nat => p.1 * p.2) ⁻¹' {n}), term f s b.val.1 * term g s b.val.2 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · -- show that both sides vanish when `n = 0`; this is the hardest part of the proof!
    refine (term_zero ..).trans ?_
    -- the right-hand sum is over the union below, but in each term, one factor is always zero
    have hS : (fun p => p.1 * p.2) ⁻¹' {0} = {0} ×ˢ univ union univ ×ˢ {0} := by
      ext
      simp
    have : forall p : (fun p : Nat × Nat => p.1 * p.2) ⁻¹' {0}, term f s p.val.1 * term g s p.val.2 = 0 := by
      rintro ⟨⟨_, _⟩, hp⟩
      rcases hS ▸ hp with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp
    simp [this]
  -- now `n ≠ 0`
  rw [show (fun p : Nat × Nat => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
    Finset.tsum_subtype' n.divisorsAntidiagonal fun p => term f s p.1 * term g s p.2,
    term_convolution f g s n]

end LSeries

open Set in
/--
lemma `LSeriesHasSum.convolution` / 引理 `LSeriesHasSum.convolution`

English:
lemma LSeriesHasSum.convolution
  statement: {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHasSum f s a)
  proof: by
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  -- NB: this `simpa` is quite slow if un-squeezed
  simpa only [LSeriesHasSum, term_convolution'] using (hf.mul hg hsum).tsum_fiberwise _

中文:
引理 LSeriesHasSum.convolution
  结论: {f g : 自然数 -> 复形} {s a b : 复形} (hf : LSeriesHasSum f s a)
  证明: by
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  -- NB: this `simpa` is quite slow if un-squeezed
  simpa only [LSeriesHasSum, term_convolution'] using (hf.mul hg hsum).tsum_fiberwise _

Depends on / 依赖: hf.summable.norm, hg.summable.norm, summable, summable_mul_of_summable_norm
-/
lemma LSeriesHasSum.convolution {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  -- NB: this `simpa` is quite slow if un-squeezed
  simpa only [LSeriesHasSum, term_convolution'] using (hf.mul hg hsum).tsum_fiberwise _

/--
lemma `LSeries_convolution'` / 引理 `LSeries_convolution'`

English:
lemma LSeries_convolution'
  statement: {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
  proof: (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

中文:
引理 LSeries_convolution'
  结论: {f g : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s)
  证明: (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

Depends on / 依赖: LSeriesHasSum, LSeriesHasSum.convolution, LSeries_eq, convolution, hf.LSeriesHasSum, hg.LSeriesHasSum
-/
lemma LSeries_convolution' {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/--
lemma `LSeries_convolution` / 引理 `LSeries_convolution`

English:
lemma LSeries_convolution
  statement: {f g : Nat -> Complex} {s : Complex}
  proof: LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

中文:
引理 LSeries_convolution
  结论: {f g : 自然数 -> 复形} {s : 复形}
  证明: LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

Depends on / 依赖: LSeriesSummable_of_abscissaOfAbsConv_lt_re, LSeries_convolution
-/
lemma LSeries_convolution {f g : Nat -> Complex} {s : Complex}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/--
lemma `LSeriesSummable.convolution` / 引理 `LSeriesSummable.convolution`

English:
lemma LSeriesSummable.convolution
  statement: {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
  proof: (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

中文:
引理 LSeriesSummable.convolution
  结论: {f g : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s)
  证明: (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

Depends on / 依赖: LSeriesHasSum, LSeriesHasSum.convolution, LSeriesSummable, convolution, hf.LSeriesHasSum, hg.LSeriesHasSum
-/
lemma LSeriesSummable.convolution {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

/--
lemma `LSeries.abscissaOfAbsConv_convolution_le` / 引理 `LSeries.abscissaOfAbsConv_convolution_le`

English:
lemma LSeries.abscissaOfAbsConv_convolution_le
  given: (f g : Nat -> Complex)
  proof: abscissaOfAbsConv_binop_le LSeriesSummable.convolution f g

中文:
引理 LSeries.abscissaOfAbsConv_convolution_le
  条件: (f g : 自然数 -> 复形)
  证明: abscissaOfAbsConv_binop_le LSeriesSummable.convolution f g

Depends on / 依赖: LSeriesSummable, LSeriesSummable.convolution, abscissaOfAbsConv_binop_le, convolution
-/
lemma LSeries.abscissaOfAbsConv_convolution_le (f g : Nat -> Complex) :
    abscissaOfAbsConv (f ⍟ g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.convolution f g

namespace ArithmeticFunction

/-!
### Versions for arithmetic functions
-/

/--
lemma `LSeriesHasSum_mul` / 引理 `LSeriesHasSum_mul`

English:
lemma LSeriesHasSum_mul
  statement: {f g : ArithmeticFunction Complex} {s a b : Complex} (hf : LSeriesHasSum ↗f s a)
  proof: coe_mul f g ▸ hf.convolution hg

中文:
引理 LSeriesHasSum_mul
  结论: {f g : ArithmeticFunction 复形} {s a b : 复形} (hf : LSeriesHasSum ↗f s a)
  证明: coe_mul f g ▸ hf.convolution hg

Depends on / 依赖: coe_mul, convolution, hf.convolution
-/
lemma LSeriesHasSum_mul {f g : ArithmeticFunction Complex} {s a b : Complex} (hf : LSeriesHasSum ↗f s a)
    (hg : LSeriesHasSum ↗g s b) :
    LSeriesHasSum ↗(f * g) s (a * b) :=
  coe_mul f g ▸ hf.convolution hg

/--
lemma `LSeries_mul'` / 引理 `LSeries_mul'`

English:
lemma LSeries_mul'
  statement: {f g : ArithmeticFunction Complex} {s : Complex} (hf : LSeriesSummable ↗f s)
  proof: coe_mul f g ▸ LSeries_convolution' hf hg

中文:
引理 LSeries_mul'
  结论: {f g : ArithmeticFunction 复形} {s : 复形} (hf : LSeriesSummable ↗f s)
  证明: coe_mul f g ▸ LSeries_convolution' hf hg

Depends on / 依赖: LSeries_convolution, coe_mul
-/
lemma LSeries_mul' {f g : ArithmeticFunction Complex} {s : Complex} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution' hf hg

/--
lemma `LSeries_mul` / 引理 `LSeries_mul`

English:
lemma LSeries_mul
  statement: {f g : ArithmeticFunction Complex} {s : Complex}
  proof: coe_mul f g ▸ LSeries_convolution hf hg

中文:
引理 LSeries_mul
  结论: {f g : ArithmeticFunction 复形} {s : 复形}
  证明: coe_mul f g ▸ LSeries_convolution hf hg

Depends on / 依赖: LSeries_convolution, coe_mul
-/
lemma LSeries_mul {f g : ArithmeticFunction Complex} {s : Complex}
    (hf : abscissaOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution hf hg

/--
lemma `LSeriesSummable_mul` / 引理 `LSeriesSummable_mul`

English:
lemma LSeriesSummable_mul
  statement: {f g : ArithmeticFunction Complex} {s : Complex} (hf : LSeriesSummable ↗f s)
  proof: coe_mul f g ▸ hf.convolution hg

中文:
引理 LSeriesSummable_mul
  结论: {f g : ArithmeticFunction 复形} {s : 复形} (hf : LSeriesSummable ↗f s)
  证明: coe_mul f g ▸ hf.convolution hg

Depends on / 依赖: coe_mul, convolution, hf.convolution
-/
lemma LSeriesSummable_mul {f g : ArithmeticFunction Complex} {s : Complex} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeriesSummable ↗(f * g) s :=
  coe_mul f g ▸ hf.convolution hg

end ArithmeticFunction
