/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.CauSeq.BigOperators
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Exponential Function

This file contains the definitions of the real and complex exponential function.

## Main definitions

* `Complex.exp`: The complex exponential function, defined via its Taylor series

* `Real.exp`: The real exponential function, defined as the real part of the complex exponential

-/

@[expose] public section

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

/--
theorem `isCauSeq_norm_exp` / 定理 `isCauSeq_norm_exp`

English:
theorem isCauSeq_norm_exp
  given: (z : Complex)
  proof: let ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hn0 : (0 : Real) < n := lt_of_le_of_lt (norm_nonneg _) hn
  IsCauSeq.series_ratio_test n (‖z‖ / n) (div_nonneg (norm_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_norm]; rw [abs_norm]; rw [Nat.factorial_succ]; r

中文:
定理 isCauSeq_norm_exp
  条件: (z : 复形)
  证明: let ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hn0 : (0 : Real) < n := lt_of_le_of_lt (norm_nonneg _) hn
  IsCauSeq.series_ratio_test n (‖z‖ / n) (div_nonneg (norm_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_norm]; rw [abs_norm]; rw [Nat.factorial_succ]; r

Depends on / 依赖: Complex.norm_div, Complex.norm_mul, IsCauSeq, IsCauSeq.series_ratio_test, Nat.cast_mul, Nat.factorial_succ, Nat.le_, abs_norm, cast_mul, div_div, div_nonneg, exists_nat_gt, factorial_succ, le_of_lt, le_trans, lt_of_le_of_lt, m.succ, mul_comm, mul_div_assoc, mul_div_right_comm
-/
theorem isCauSeq_norm_exp (z : Complex) :
    IsCauSeq abs fun n => ∑ m in range n, ‖z ^ m / m.factorial‖ :=
  let ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hn0 : (0 : Real) < n := lt_of_le_of_lt (norm_nonneg _) hn
  IsCauSeq.series_ratio_test n (‖z‖ / n) (div_nonneg (norm_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_norm]; rw [abs_norm]; rw [Nat.factorial_succ]; rw [pow_succ']; rw [mul_comm m.succ]; rw [Nat.cast_mul]; rw [← div_div]; rw [mul_div_assoc]; rw [mul_div_right_comm]; rw [Complex.norm_mul]; rw [Complex.norm_div]; rw [norm_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)

noncomputable section

/--
theorem `isCauSeq_exp` / 定理 `isCauSeq_exp`

English:
theorem isCauSeq_exp
  given: (z : Complex)
  statement: IsCauSeq (‖·‖) fun n => ∑ m in range n, z ^ m / m.factorial
  proof: (isCauSeq_norm_exp z).of_abv

中文:
定理 isCauSeq_exp
  条件: (z : 复形)
  结论: IsCauSeq (‖·‖) fun n => ∑ m in range n, z ^ m / m.factorial
  证明: (isCauSeq_norm_exp z).of_abv

Depends on / 依赖: isCauSeq_norm_exp, of_abv
-/
theorem isCauSeq_exp (z : Complex) : IsCauSeq (‖·‖) fun n => ∑ m in range n, z ^ m / m.factorial :=
  (isCauSeq_norm_exp z).of_abv

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
/--
Definition of `exp'` / `exp'` 的定义

English:
definition exp'
  signature: (z : Complex)
  body: ⟨fun n => ∑ m in range n, z ^ m / m.factorial, isCauSeq_exp z⟩

中文:
定义 exp'
  签名: (z : 复形)
  定义体: ⟨fun n => ∑ m in range n, z ^ m / m.factorial, isCauSeq_exp z⟩

Depends on / 依赖: factorial, isCauSeq_exp, m.factorial
-/
def exp' (z : Complex) : CauSeq Complex (‖·‖) :=
  ⟨fun n => ∑ m in range n, z ^ m / m.factorial, isCauSeq_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
@[pp_nodot]
irreducible_def exp (z : Complex) : Complex :=
  CauSeq.lim (exp' z)

/-- scoped notation for the complex exponential function -/
scoped notation "cexp" => Complex.exp

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot, wikidata Q168698]
nonrec def exp (x : Real) : Real :=
  (exp x).re

/-- scoped notation for the real exponential function -/
scoped notation "rexp" => Real.exp

end

end Real

namespace Complex

variable (x y : Complex)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `exp_zero` / 定理 `exp_zero`

English:
theorem exp_zero
  statement: exp 0 = 1
  proof: by
  rw [exp]
  refine lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => ?_⟩
  convert ε0.lt
  rcases j with - | j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← ih (by simp)]
      simp only [sum_range_succ, pow

中文:
定理 exp_zero
  结论: exp 0 = 1
  证明: by
  rw [exp]
  refine lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => ?_⟩
  convert ε0.lt
  rcases j with - | j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← ih (by simp)]
      simp only [sum_range_succ, pow

Depends on / 依赖: absurd, convert, lim_eq_of_equiv_const, not_le_of_gt, pow_succ, sum_range_succ, zero_lt_one
-/
theorem exp_zero : exp 0 = 1 := by
  rw [exp]
  refine lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => ?_⟩
  convert ε0.lt
  rcases j with - | j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← ih (by simp)]
      simp only [sum_range_succ, pow_succ]
      simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exp_add` / 定理 `exp_add`

English:
theorem exp_add
  statement: exp (x + y) = exp x * exp y
  proof: by
  have hj : forall j : Nat, (∑ m in range j, (x + y) ^ m / m.factorial) =
        ∑ i in range j, ∑ k in range (i + 1), x ^ k / k.factorial *
          (y ^ (i - k) / (i - k).factorial) := by
    intro j
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_pow]; rw [div_eq_mul_inv]; rw [sum_

中文:
定理 exp_add
  结论: exp (x + y) = exp x * exp y
  证明: by
  have hj : forall j : Nat, (∑ m in range j, (x + y) ^ m / m.factorial) =
        ∑ i in range j, ∑ k in range (i + 1), x ^ k / k.factorial *
          (y ^ (i - k) / (i - k).factorial) := by
    intro j
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_pow]; rw [div_eq_mul_inv]; rw [sum_

Depends on / 依赖: Finset, Finset.sum_congr, Nat.cast_ne_zero, Nat.choose_mul_factorial_mul_factorial, Nat.choose_pos, Nat.le_of_lt_succ, add_pow, cast_ne_zero, choose_mul_factorial_mul_factorial, choose_pos, div_eq_mul_inv, factorial, k.factorial, le_of_lt_succ, m.choose, m.factorial, mem_range, pos_iff_ne_zero, sum_congr, sum_mul
-/
theorem exp_add : exp (x + y) = exp x * exp y := by
  have hj : forall j : Nat, (∑ m in range j, (x + y) ^ m / m.factorial) =
        ∑ i in range j, ∑ k in range (i + 1), x ^ k / k.factorial *
          (y ^ (i - k) / (i - k).factorial) := by
    intro j
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_pow]; rw [div_eq_mul_inv]; rw [sum_mul]
    refine Finset.sum_congr rfl fun I hi => ?_
    have h₁ : (m.choose I : Complex) != 0 :=
      Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.1 hi))))
    have h₂ := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ <| Finset.mem_range.1 hi)
    rw [← h₂]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [mul_inv]; rw [mul_inv]
    simp only [mul_left_comm (m.choose I : Complex), mul_assoc, mul_left_comm (m.choose I : Complex)⁻¹,
      mul_comm (m.choose I : Complex)]
    rw [inv_mul_cancel₀ h₁]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm]
  simp_rw [exp, exp', lim_mul_lim]
  apply (lim_eq_lim_of_equiv _).symm
  simp only [hj]
  exact cauchy_product (isCauSeq_norm_exp x) (isCauSeq_exp y)

/-- the exponential function as a monoid hom from `Multiplicative ℂ` to `ℂ` -/
@[simps]
/--
Definition of `expMonoidHom` / `expMonoidHom` 的定义

English:
definition expMonoidHom
  signature: : MonoidHom (Multiplicative Complex) Complex
  body: { toFun := fun z => exp z.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

中文:
定义 expMonoidHom
  签名: : 幺半群态射 (Multiplicative 复形) 复形
  定义体: { toFun := fun z => exp z.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

Depends on / 依赖: exp_add, map_mul, map_one, z.toAdd
-/
noncomputable def expMonoidHom : MonoidHom (Multiplicative Complex) Complex :=
  { toFun := fun z => exp z.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

/--
theorem `exp_list_sum` / 定理 `exp_list_sum`

English:
theorem exp_list_sum
  given: (l : List Complex)
  statement: exp l.sum = (l.map exp).prod
  proof: map_list_prod (M := Multiplicative Complex) expMonoidHom l

中文:
定理 exp_list_sum
  条件: (l : 列表 复形)
  结论: exp l.求和 = (l.map exp).乘积
  证明: map_list_prod (M := Multiplicative Complex) expMonoidHom l

Depends on / 依赖: Multiplicative, expMonoidHom, map_list_prod
-/
theorem exp_list_sum (l : List Complex) : exp l.sum = (l.map exp).prod :=
  map_list_prod (M := Multiplicative Complex) expMonoidHom l

/--
theorem `exp_multiset_sum` / 定理 `exp_multiset_sum`

English:
theorem exp_multiset_sum
  given: (s : Multiset Complex)
  statement: exp s.sum = (s.map exp).prod
  proof: @MonoidHom.map_multiset_prod (Multiplicative Complex) Complex _ _ expMonoidHom s

中文:
定理 exp_multiset_sum
  条件: (s : Multiset 复形)
  结论: exp s.求和 = (s.map exp).乘积
  证明: @MonoidHom.map_multiset_prod (Multiplicative Complex) Complex _ _ expMonoidHom s

Depends on / 依赖: MonoidHom, MonoidHom.map_multiset_prod, Multiplicative, expMonoidHom, map_multiset_prod
-/
theorem exp_multiset_sum (s : Multiset Complex) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative Complex) Complex _ _ expMonoidHom s

/--
theorem `exp_sum` / 定理 `exp_sum`

English:
theorem exp_sum
  given: {α : Type*} (s : Finset α) (f : α -> Complex)
  proof: map_prod (M := Multiplicative Complex) expMonoidHom f s

中文:
定理 exp_sum
  条件: {α : 类型} (s : 有限集 α) (f : α -> 复形)
  证明: map_prod (M := Multiplicative Complex) expMonoidHom f s

Depends on / 依赖: Multiplicative, expMonoidHom, map_prod
-/
theorem exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
    exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
  map_prod (M := Multiplicative Complex) expMonoidHom f s

/--
lemma `exp_nsmul` / 引理 `exp_nsmul`

English:
lemma exp_nsmul
  given: (x : Complex) (n : Nat)
  statement: exp (n • x) = exp x ^ n
  proof: @MonoidHom.map_pow (Multiplicative Complex) Complex _ _ expMonoidHom _ _

中文:
引理 exp_nsmul
  条件: (x : 复形) (n : 自然数)
  结论: exp (n • x) = exp x ^ n
  证明: @MonoidHom.map_pow (Multiplicative Complex) Complex _ _ expMonoidHom _ _

Depends on / 依赖: MonoidHom, MonoidHom.map_pow, Multiplicative, expMonoidHom, map_pow
-/
lemma exp_nsmul (x : Complex) (n : Nat) : exp (n • x) = exp x ^ n :=
  @MonoidHom.map_pow (Multiplicative Complex) Complex _ _ expMonoidHom _ _

/--
lemma `exp_nsmul'` / 引理 `exp_nsmul'`

English:
lemma exp_nsmul'
  given: (x a p : Complex) (n : Nat)
  statement: exp (a * n * x / p) = exp (a * x / p) ^ n
  proof: by
  rw [← Complex.exp_nsmul]
  ring_nf

中文:
引理 exp_nsmul'
  条件: (x a p : 复形) (n : 自然数)
  结论: exp (a * n * x / p) = exp (a * x / p) ^ n
  证明: by
  rw [← Complex.exp_nsmul]
  ring_nf

Depends on / 依赖: Complex.exp_nsmul, exp_nsmul, ring_nf
-/
lemma exp_nsmul' (x a p : Complex) (n : Nat) : exp (a * n * x / p) = exp (a * x / p) ^ n := by
  rw [← Complex.exp_nsmul]
  ring_nf

/--
theorem `exp_nat_mul` / 定理 `exp_nat_mul`

English:
theorem exp_nat_mul
  given: (x : Complex)
  statement: forall n : Nat, exp (n * x) = exp x ^ n

中文:
定理 exp_nat_mul
  条件: (x : 复形)
  结论: 对任意 n : 自然数, exp (n * x) = exp x ^ n
-/
theorem exp_nat_mul (x : Complex) : forall n : Nat, exp (n * x) = exp x ^ n
  | 0 => by rw [Nat.cast_zero, zero_mul, exp_zero, pow_zero]
  | Nat.succ n => by rw [pow_succ, Nat.cast_add_one, add_mul, exp_add, ← exp_nat_mul _ n, one_mul]

@[simp]
/--
theorem `exp_ne_zero` / 定理 `exp_ne_zero`

English:
theorem exp_ne_zero
  statement: exp x != 0
  proof: fun h =>
zero_ne_one (α := Complex) by rw [← exp_zero, ← add_neg_cancel x, exp_add, h]; simp

中文:
定理 exp_ne_zero
  结论: exp x != 0
  证明: fun h =>
zero_ne_one (α := Complex) by rw [← exp_zero, ← add_neg_cancel x, exp_add, h]; simp
-/
theorem exp_ne_zero : exp x != 0 := fun h =>
zero_ne_one (α := Complex) by rw [← exp_zero, ← add_neg_cancel x, exp_add, h]; simp

/--
theorem `exp_neg` / 定理 `exp_neg`

English:
theorem exp_neg
  statement: exp (-x) = (exp x)⁻¹
  proof: by
  rw [← mul_right_inj' (exp_ne_zero x)]; rw [← exp_add]; simp

中文:
定理 exp_neg
  结论: exp (-x) = (exp x)⁻¹
  证明: by
  rw [← mul_right_inj' (exp_ne_zero x)]; rw [← exp_add]; simp

Depends on / 依赖: exp_add, exp_ne_zero, mul_right_inj
-/
theorem exp_neg : exp (-x) = (exp x)⁻¹ := by
  rw [← mul_right_inj' (exp_ne_zero x)]; rw [← exp_add]; simp

/--
theorem `exp_sub` / 定理 `exp_sub`

English:
theorem exp_sub
  statement: exp (x - y) = exp x / exp y
  proof: by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

中文:
定理 exp_sub
  结论: exp (x - y) = exp x / exp y
  证明: by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, exp_add, exp_neg, sub_eq_add_neg
-/
theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

/--
theorem `exp_int_mul` / 定理 `exp_int_mul`

English:
theorem exp_int_mul
  given: (z : Complex) (n : Int)
  statement: Complex.exp (n * z) = Complex.exp z ^ n
  proof: by
  cases n
  · simp [exp_nat_mul]
  · simp [exp_add, add_mul, pow_add, exp_neg, exp_nat_mul]

@[simp]

中文:
定理 exp_int_mul
  条件: (z : 复形) (n : 整数)
  结论: 复形.exp (n * z) = 复形.exp z ^ n
  证明: by
  cases n
  · simp [exp_nat_mul]
  · simp [exp_add, add_mul, pow_add, exp_neg, exp_nat_mul]

@[simp]

Depends on / 依赖: add_mul, exp_add, exp_nat_mul, exp_neg, pow_add
-/
theorem exp_int_mul (z : Complex) (n : Int) : Complex.exp (n * z) = Complex.exp z ^ n := by
  cases n
  · simp [exp_nat_mul]
  · simp [exp_add, add_mul, pow_add, exp_neg, exp_nat_mul]

@[simp]
/--
theorem `exp_conj` / 定理 `exp_conj`

English:
theorem exp_conj
  statement: exp (conj x) = conj (exp x)
  proof: by
  simp only [exp]
  rw [← lim_conj]
  refine congr_arg CauSeq.lim (CauSeq.ext fun _ => ?_)
  dsimp [exp', Function.comp_def, cauSeqConj]
  rw [map_sum (starRingEnd _)]
  refine sum_congr rfl fun n _ => ?_
  rw [map_div₀]; rw [map_pow]; rw [← ofReal_natCast]; rw [conj_ofReal]

@[simp]

中文:
定理 exp_conj
  结论: exp (conj x) = conj (exp x)
  证明: by
  simp only [exp]
  rw [← lim_conj]
  refine congr_arg CauSeq.lim (CauSeq.ext fun _ => ?_)
  dsimp [exp', Function.comp_def, cauSeqConj]
  rw [map_sum (starRingEnd _)]
  refine sum_congr rfl fun n _ => ?_
  rw [map_div₀]; rw [map_pow]; rw [← ofReal_natCast]; rw [conj_ofReal]

@[simp]

Depends on / 依赖: CauSeq, CauSeq.ext, CauSeq.lim, Function, Function.comp_def, cauSeqConj, comp_def, congr_arg, conj_ofReal, lim_conj, map_pow, map_sum, ofReal_natCast, starRingEnd, sum_congr
-/
theorem exp_conj : exp (conj x) = conj (exp x) := by
  simp only [exp]
  rw [← lim_conj]
  refine congr_arg CauSeq.lim (CauSeq.ext fun _ => ?_)
  dsimp [exp', Function.comp_def, cauSeqConj]
  rw [map_sum (starRingEnd _)]
  refine sum_congr rfl fun n _ => ?_
  rw [map_div₀]; rw [map_pow]; rw [← ofReal_natCast]; rw [conj_ofReal]

@[simp]
/--
theorem `ofReal_exp_ofReal_re` / 定理 `ofReal_exp_ofReal_re`

English:
theorem ofReal_exp_ofReal_re
  given: (x : Real)
  statement: ((exp x).re : Complex) = exp x
  proof: conj_eq_iff_re.1 by rw [← exp_conj, conj_ofReal]

@[simp, norm_cast]

中文:
定理 of实数_exp_of实数_re
  条件: (x : 实数)
  结论: ((exp x).re : 复形) = exp x
  证明: conj_eq_iff_re.1 by rw [← exp_conj, conj_ofReal]

@[simp, norm_cast]

Depends on / 依赖: conj_eq_iff_re, conj_ofReal, exp_conj
-/
theorem ofReal_exp_ofReal_re (x : Real) : ((exp x).re : Complex) = exp x :=
conj_eq_iff_re.1 by rw [← exp_conj, conj_ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_exp` / 定理 `ofReal_exp`

English:
theorem ofReal_exp
  given: (x : Real)
  statement: (Real.exp x : Complex) = exp x
  proof: ofReal_exp_ofReal_re _

@[simp]

中文:
定理 of实数_exp
  条件: (x : 实数)
  结论: (实数.exp x : 复形) = exp x
  证明: ofReal_exp_ofReal_re _

@[simp]

Depends on / 依赖: ofReal_exp_ofReal_re
-/
theorem ofReal_exp (x : Real) : (Real.exp x : Complex) = exp x :=
  ofReal_exp_ofReal_re _

@[simp]
/--
theorem `exp_ofReal_im` / 定理 `exp_ofReal_im`

English:
theorem exp_ofReal_im
  given: (x : Real)
  statement: (exp x).im = 0
  proof: by rw [← ofReal_exp_ofReal_re, ofReal_im]

中文:
定理 exp_of实数_im
  条件: (x : 实数)
  结论: (exp x).im = 0
  证明: by rw [← ofReal_exp_ofReal_re, ofReal_im]

Depends on / 依赖: ofReal_exp_ofReal_re, ofReal_im
-/
theorem exp_ofReal_im (x : Real) : (exp x).im = 0 := by rw [← ofReal_exp_ofReal_re, ofReal_im]

/--
theorem `exp_ofReal_re` / 定理 `exp_ofReal_re`

English:
theorem exp_ofReal_re
  given: (x : Real)
  statement: (exp x).re = Real.exp x
  proof: rfl

中文:
定理 exp_of实数_re
  条件: (x : 实数)
  结论: (exp x).re = 实数.exp x
  证明: rfl
-/
theorem exp_ofReal_re (x : Real) : (exp x).re = Real.exp x :=
  rfl

end Complex

namespace Real

open Complex

variable (x y : Real)

@[simp]
/--
theorem `exp_zero` / 定理 `exp_zero`

English:
theorem exp_zero
  statement: exp 0 = 1
  proof: by simp [Real.exp]

nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]

中文:
定理 exp_zero
  结论: exp 0 = 1
  证明: by simp [Real.exp]

nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]

Depends on / 依赖: Real.exp
-/
theorem exp_zero : exp 0 = 1 := by simp [Real.exp]

nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]

/-- the exponential function as a monoid hom from `Multiplicative ℝ` to `ℝ` -/
@[simps]
/--
Definition of `expMonoidHom` / `expMonoidHom` 的定义

English:
definition expMonoidHom
  signature: : MonoidHom (Multiplicative Real) Real
  body: { toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

中文:
定义 expMonoidHom
  签名: : 幺半群态射 (Multiplicative 实数) 实数
  定义体: { toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

Depends on / 依赖: exp_add, map_mul, map_one, x.toAdd
-/
noncomputable def expMonoidHom : MonoidHom (Multiplicative Real) Real :=
  { toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

/--
theorem `exp_list_sum` / 定理 `exp_list_sum`

English:
theorem exp_list_sum
  given: (l : List Real)
  statement: exp l.sum = (l.map exp).prod
  proof: map_list_prod (M := Multiplicative Real) expMonoidHom l

中文:
定理 exp_list_sum
  条件: (l : 列表 实数)
  结论: exp l.求和 = (l.map exp).乘积
  证明: map_list_prod (M := Multiplicative Real) expMonoidHom l

Depends on / 依赖: Multiplicative, expMonoidHom, map_list_prod
-/
theorem exp_list_sum (l : List Real) : exp l.sum = (l.map exp).prod :=
  map_list_prod (M := Multiplicative Real) expMonoidHom l

/--
theorem `exp_multiset_sum` / 定理 `exp_multiset_sum`

English:
theorem exp_multiset_sum
  given: (s : Multiset Real)
  statement: exp s.sum = (s.map exp).prod
  proof: @MonoidHom.map_multiset_prod (Multiplicative Real) Real _ _ expMonoidHom s

中文:
定理 exp_multiset_sum
  条件: (s : Multiset 实数)
  结论: exp s.求和 = (s.map exp).乘积
  证明: @MonoidHom.map_multiset_prod (Multiplicative Real) Real _ _ expMonoidHom s

Depends on / 依赖: MonoidHom, MonoidHom.map_multiset_prod, Multiplicative, expMonoidHom, map_multiset_prod
-/
theorem exp_multiset_sum (s : Multiset Real) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative Real) Real _ _ expMonoidHom s

/--
theorem `exp_sum` / 定理 `exp_sum`

English:
theorem exp_sum
  given: {α : Type*} (s : Finset α) (f : α -> Real)
  proof: map_prod (M := Multiplicative Real) expMonoidHom f s

中文:
定理 exp_sum
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数)
  证明: map_prod (M := Multiplicative Real) expMonoidHom f s

Depends on / 依赖: Multiplicative, expMonoidHom, map_prod
-/
theorem exp_sum {α : Type*} (s : Finset α) (f : α -> Real) :
    exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
  map_prod (M := Multiplicative Real) expMonoidHom f s

/--
lemma `exp_nsmul` / 引理 `exp_nsmul`

English:
lemma exp_nsmul
  given: (x : Real) (n : Nat)
  statement: exp (n • x) = exp x ^ n
  proof: @MonoidHom.map_pow (Multiplicative Real) Real _ _ expMonoidHom _ _

nonrec theorem exp_nat_mul (x : Real) (n : Nat) : exp (n * x) = exp x ^ n :=
  ofReal_injective (by simp [exp_nat_mul])

@[simp]
nonrec theorem exp_ne_zero : exp x != 0 := fun h =>
exp_ne_zero x by rw [exp, ← ofReal_inj] at h; simp_

中文:
引理 exp_nsmul
  条件: (x : 实数) (n : 自然数)
  结论: exp (n • x) = exp x ^ n
  证明: @MonoidHom.map_pow (Multiplicative Real) Real _ _ expMonoidHom _ _

nonrec theorem exp_nat_mul (x : Real) (n : Nat) : exp (n * x) = exp x ^ n :=
  ofReal_injective (by simp [exp_nat_mul])

@[simp]
nonrec theorem exp_ne_zero : exp x != 0 := fun h =>
exp_ne_zero x by rw [exp, ← ofReal_inj] at h; simp_

Depends on / 依赖: MonoidHom, MonoidHom.map_pow, Multiplicative, expMonoidHom, map_pow
-/
lemma exp_nsmul (x : Real) (n : Nat) : exp (n • x) = exp x ^ n :=
  @MonoidHom.map_pow (Multiplicative Real) Real _ _ expMonoidHom _ _

nonrec theorem exp_nat_mul (x : Real) (n : Nat) : exp (n * x) = exp x ^ n :=
  ofReal_injective (by simp [exp_nat_mul])

@[simp]
nonrec theorem exp_ne_zero : exp x != 0 := fun h =>
exp_ne_zero x by rw [exp, ← ofReal_inj] at h; simp_all

nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹ :=
ofReal_injective by simp [exp_neg]

/--
theorem `exp_sub` / 定理 `exp_sub`

English:
theorem exp_sub
  statement: exp (x - y) = exp x / exp y
  proof: by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

中文:
定理 exp_sub
  结论: exp (x - y) = exp x / exp y
  证明: by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, exp_add, exp_neg, sub_eq_add_neg
-/
theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

open IsAbsoluteValue Nat

/--
theorem `sum_le_exp_of_nonneg` / 定理 `sum_le_exp_of_nonneg`

English:
theorem sum_le_exp_of_nonneg
  given: {x : Real} (hx : 0 <= x) (n : Nat)
  statement: ∑ i in range n, x ^ i / i ! <= exp x
  proof: calc
    ∑ i in range n, x ^ i / i ! <= lim (⟨_, isCauSeq_re (exp' x)⟩ : CauSeq Real abs) := by
      refine le_lim (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
      simp only [exp', const_apply, re_sum]
      norm_cast
      refine sum_le_sum_of_subset_of_nonneg (range_mono hj) fun _ _ _ => ?_
      

中文:
定理 sum_le_exp_of_nonneg
  条件: {x : 实数} (hx : 0 <= x) (n : 自然数)
  结论: ∑ i in range n, x ^ i / i ! <= exp x
  证明: calc
    ∑ i in range n, x ^ i / i ! <= lim (⟨_, isCauSeq_re (exp' x)⟩ : CauSeq Real abs) := by
      refine le_lim (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
      simp only [exp', const_apply, re_sum]
      norm_cast
      refine sum_le_sum_of_subset_of_nonneg (range_mono hj) fun _ _ _ => ?_
      

Depends on / 依赖: CauSeq, CauSeq.le_of_exists, Complex.exp, cauSeqRe, const_apply, isCauSeq_re, le_lim, le_of_exists, lim_re, range_mono, re_sum, sum_le_sum_of_subset_of_nonneg
-/
theorem sum_le_exp_of_nonneg {x : Real} (hx : 0 <= x) (n : Nat) : ∑ i in range n, x ^ i / i ! <= exp x :=
  calc
    ∑ i in range n, x ^ i / i ! <= lim (⟨_, isCauSeq_re (exp' x)⟩ : CauSeq Real abs) := by
      refine le_lim (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
      simp only [exp', const_apply, re_sum]
      norm_cast
      refine sum_le_sum_of_subset_of_nonneg (range_mono hj) fun _ _ _ => ?_
      positivity
    _ = exp x := by rw [exp, Complex.exp, ← cauSeqRe, lim_re]

/--
lemma `pow_div_factorial_le_exp` / 引理 `pow_div_factorial_le_exp`

English:
lemma pow_div_factorial_le_exp
  given: (hx : 0 <= x) (n : Nat)
  statement: x ^ n / n ! <= exp x
  proof: calc
    x ^ n / n ! <= ∑ k in range (n + 1), x ^ k / k ! :=
        single_le_sum (f := fun k => x ^ k / k !) (fun k _ => by positivity) (self_mem_range_succ n)
    _ <= exp x := sum_le_exp_of_nonneg hx _

中文:
引理 pow_div_factorial_le_exp
  条件: (hx : 0 <= x) (n : 自然数)
  结论: x ^ n / n ! <= exp x
  证明: calc
    x ^ n / n ! <= ∑ k in range (n + 1), x ^ k / k ! :=
        single_le_sum (f := fun k => x ^ k / k !) (fun k _ => by positivity) (self_mem_range_succ n)
    _ <= exp x := sum_le_exp_of_nonneg hx _

Depends on / 依赖: self_mem_range_succ, single_le_sum, sum_le_exp_of_nonneg
-/
lemma pow_div_factorial_le_exp (hx : 0 <= x) (n : Nat) : x ^ n / n ! <= exp x :=
  calc
    x ^ n / n ! <= ∑ k in range (n + 1), x ^ k / k ! :=
        single_le_sum (f := fun k => x ^ k / k !) (fun k _ => by positivity) (self_mem_range_succ n)
    _ <= exp x := sum_le_exp_of_nonneg hx _

/--
theorem `quadratic_le_exp_of_nonneg` / 定理 `quadratic_le_exp_of_nonneg`

English:
theorem quadratic_le_exp_of_nonneg
  given: {x : Real} (hx : 0 <= x)
  statement: 1 + x + x ^ 2 / 2 <= exp x
  proof: calc
    1 + x + x ^ 2 / 2 = ∑ i in range 3, x ^ i / i ! := by
        simp only [sum_range_succ, range_one, sum_singleton, _root_.pow_zero, factorial,
          pow_one, mul_one, Nat.mul_one,
          cast_succ]
        ring_nf
    _ <= exp x := sum_le_exp_of_nonneg hx 3

中文:
定理 quadratic_le_exp_of_nonneg
  条件: {x : 实数} (hx : 0 <= x)
  结论: 1 + x + x ^ 2 / 2 <= exp x
  证明: calc
    1 + x + x ^ 2 / 2 = ∑ i in range 3, x ^ i / i ! := by
        simp only [sum_range_succ, range_one, sum_singleton, _root_.pow_zero, factorial,
          pow_one, mul_one, Nat.mul_one,
          cast_succ]
        ring_nf
    _ <= exp x := sum_le_exp_of_nonneg hx 3

Depends on / 依赖: Nat.mul_one, _root_, _root_.pow_zero, cast_succ, factorial, mul_one, pow_one, pow_zero, range_one, ring_nf, sum_le_exp_of_nonneg, sum_range_succ, sum_singleton
-/
theorem quadratic_le_exp_of_nonneg {x : Real} (hx : 0 <= x) : 1 + x + x ^ 2 / 2 <= exp x :=
  calc
    1 + x + x ^ 2 / 2 = ∑ i in range 3, x ^ i / i ! := by
        simp only [sum_range_succ, range_one, sum_singleton, _root_.pow_zero, factorial,
          pow_one, mul_one, Nat.mul_one,
          cast_succ]
        ring_nf
    _ <= exp x := sum_le_exp_of_nonneg hx 3

/--
theorem `add_one_lt_exp_of_pos` / 定理 `add_one_lt_exp_of_pos`

English:
theorem add_one_lt_exp_of_pos
  given: {x : Real} (hx : 0 < x)
  statement: x + 1 < exp x
  proof: (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

中文:
定理 add_one_lt_exp_of_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: x + 1 < exp x
  证明: (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)
-/
private theorem add_one_lt_exp_of_pos {x : Real} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

/--
theorem `add_one_le_exp_of_nonneg` / 定理 `add_one_le_exp_of_nonneg`

English:
theorem add_one_le_exp_of_nonneg
  given: {x : Real} (hx : 0 <= x)
  statement: x + 1 <= exp x
  proof: by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

中文:
定理 add_one_le_exp_of_nonneg
  条件: {x : 实数} (hx : 0 <= x)
  结论: x + 1 <= exp x
  证明: by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le
-/
private theorem add_one_le_exp_of_nonneg {x : Real} (hx : 0 <= x) : x + 1 <= exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

/--
theorem `one_le_exp` / 定理 `one_le_exp`

English:
theorem one_le_exp
  given: {x : Real} (hx : 0 <= x)
  statement: 1 <= exp x
  proof: by linarith [add_one_le_exp_of_nonneg hx]

@[bound]

中文:
定理 one_le_exp
  条件: {x : 实数} (hx : 0 <= x)
  结论: 1 <= exp x
  证明: by linarith [add_one_le_exp_of_nonneg hx]

@[bound]

Depends on / 依赖: add_one_le_exp_of_nonneg
-/
theorem one_le_exp {x : Real} (hx : 0 <= x) : 1 <= exp x := by linarith [add_one_le_exp_of_nonneg hx]

@[bound]
/--
theorem `exp_pos` / 定理 `exp_pos`

English:
theorem exp_pos
  given: (x : Real)
  statement: 0 < exp x
  proof: (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x]; rw [Real.exp_neg]
    exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))

@[bound]

中文:
定理 exp_pos
  条件: (x : 实数)
  结论: 0 < exp x
  证明: (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x]; rw [Real.exp_neg]
    exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))

@[bound]

Depends on / 依赖: Real.exp_neg, exp_neg, inv_pos, le_total, lt_of_lt_of_le, neg_neg, neg_nonneg, one_le_exp, zero_lt_one
-/
theorem exp_pos (x : Real) : 0 < exp x :=
  (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x]; rw [Real.exp_neg]
    exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))

@[bound]
/--
lemma `exp_nonneg` / 引理 `exp_nonneg`

English:
lemma exp_nonneg
  given: (x : Real)
  statement: 0 <= exp x
  proof: x.exp_pos.le

@[simp]

中文:
引理 exp_nonneg
  条件: (x : 实数)
  结论: 0 <= exp x
  证明: x.exp_pos.le

@[simp]

Depends on / 依赖: exp_pos, x.exp_pos.le
-/
lemma exp_nonneg (x : Real) : 0 <= exp x := x.exp_pos.le

@[simp]
/--
theorem `abs_exp` / 定理 `abs_exp`

English:
theorem abs_exp
  given: (x : Real)
  statement: |exp x| = exp x
  proof: abs_of_pos (exp_pos _)

中文:
定理 abs_exp
  条件: (x : 实数)
  结论: |exp x| = exp x
  证明: abs_of_pos (exp_pos _)

Depends on / 依赖: abs_of_pos, exp_pos
-/
theorem abs_exp (x : Real) : |exp x| = exp x :=
  abs_of_pos (exp_pos _)

/--
lemma `exp_abs_le` / 引理 `exp_abs_le`

English:
lemma exp_abs_le
  given: (x : Real)
  statement: exp |x| <= exp x + exp (-x)
  proof: by
  cases le_total x 0 <;> simp [abs_of_nonpos, abs_of_nonneg, exp_nonneg, *]

@[mono, gcongr]

中文:
引理 exp_abs_le
  条件: (x : 实数)
  结论: exp |x| <= exp x + exp (-x)
  证明: by
  cases le_total x 0 <;> simp [abs_of_nonpos, abs_of_nonneg, exp_nonneg, *]

@[mono, gcongr]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, exp_nonneg, le_total
-/
lemma exp_abs_le (x : Real) : exp |x| <= exp x + exp (-x) := by
  cases le_total x 0 <;> simp [abs_of_nonpos, abs_of_nonneg, exp_nonneg, *]

@[mono, gcongr]
/--
theorem `exp_strictMono` / 定理 `exp_strictMono`

English:
theorem exp_strictMono
  statement: StrictMono exp
  proof: fun x y h => by
  rw [← sub_add_cancel y x]; rw [Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

@[gcongr, mono]

中文:
定理 exp_strictMono
  结论: 严格递增 exp
  证明: fun x y h => by
  rw [← sub_add_cancel y x]; rw [Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

@[gcongr, mono]

Depends on / 依赖: Real.exp_add, add_one_le_exp_of_nonneg, exp_add, exp_pos, lt_mul_iff_one_lt_left, lt_of_lt_of_le, sub_add_cancel
-/
theorem exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x]; rw [Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

@[gcongr, mono]
/--
theorem `exp_monotone` / 定理 `exp_monotone`

English:
theorem exp_monotone
  statement: Monotone exp
  proof: exp_strictMono.monotone

@[bound] -- temporary lemma for the `bound` tactic

中文:
定理 exp_monotone
  结论: 递增 exp
  证明: exp_strictMono.monotone

@[bound] -- temporary lemma for the `bound` tactic

Depends on / 依赖: exp_strictMono, exp_strictMono.monotone, monotone
-/
theorem exp_monotone : Monotone exp :=
  exp_strictMono.monotone

@[bound] -- temporary lemma for the `bound` tactic
/--
theorem `exp_le_exp_of_le` / 定理 `exp_le_exp_of_le`

English:
theorem exp_le_exp_of_le
  given: {x y : Real} (h : x <= y)
  statement: exp x <= exp y
  proof: exp_monotone h

@[simp]

中文:
定理 exp_le_exp_of_le
  条件: {x y : 实数} (h : x <= y)
  结论: exp x <= exp y
  证明: exp_monotone h

@[simp]

Depends on / 依赖: exp_monotone
-/
theorem exp_le_exp_of_le {x y : Real} (h : x <= y) : exp x <= exp y := exp_monotone h

@[simp]
/--
theorem `exp_lt_exp` / 定理 `exp_lt_exp`

English:
theorem exp_lt_exp
  given: {x y : Real}
  statement: exp x < exp y ↔ x < y
  proof: exp_strictMono.lt_iff_lt

@[simp]

中文:
定理 exp_lt_exp
  条件: {x y : 实数}
  结论: exp x < exp y ↔ x < y
  证明: exp_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: exp_strictMono, exp_strictMono.lt_iff_lt, lt_iff_lt
-/
theorem exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y :=
  exp_strictMono.lt_iff_lt

@[simp]
/--
theorem `exp_le_exp` / 定理 `exp_le_exp`

English:
theorem exp_le_exp
  given: {x y : Real}
  statement: exp x <= exp y ↔ x <= y
  proof: exp_strictMono.le_iff_le

中文:
定理 exp_le_exp
  条件: {x y : 实数}
  结论: exp x <= exp y ↔ x <= y
  证明: exp_strictMono.le_iff_le

Depends on / 依赖: exp_strictMono, exp_strictMono.le_iff_le, le_iff_le
-/
theorem exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y :=
  exp_strictMono.le_iff_le

/--
theorem `exp_injective` / 定理 `exp_injective`

English:
theorem exp_injective
  statement: Function.Injective exp
  proof: exp_strictMono.injective

@[simp]

中文:
定理 exp_injective
  结论: 函数.单射 exp
  证明: exp_strictMono.injective

@[simp]

Depends on / 依赖: exp_strictMono, exp_strictMono.injective, injective
-/
theorem exp_injective : Function.Injective exp :=
  exp_strictMono.injective

@[simp]
/--
theorem `exp_eq_exp` / 定理 `exp_eq_exp`

English:
theorem exp_eq_exp
  given: {x y : Real}
  statement: exp x = exp y ↔ x = y
  proof: exp_injective.eq_iff

@[simp]

中文:
定理 exp_eq_exp
  条件: {x y : 实数}
  结论: exp x = exp y ↔ x = y
  证明: exp_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, exp_injective, exp_injective.eq_iff
-/
theorem exp_eq_exp {x y : Real} : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff

@[simp]
/--
theorem `exp_eq_one_iff` / 定理 `exp_eq_one_iff`

English:
theorem exp_eq_one_iff
  statement: exp x = 1 ↔ x = 0
  proof: exp_injective.eq_iff' exp_zero

@[simp]

中文:
定理 exp_eq_one_iff
  结论: exp x = 1 ↔ x = 0
  证明: exp_injective.eq_iff' exp_zero

@[simp]

Depends on / 依赖: eq_iff, exp_injective, exp_injective.eq_iff, exp_zero
-/
theorem exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
  exp_injective.eq_iff' exp_zero

@[simp]
/--
theorem `one_lt_exp_iff` / 定理 `one_lt_exp_iff`

English:
theorem one_lt_exp_iff
  given: {x : Real}
  statement: 1 < exp x ↔ 0 < x
  proof: by rw [← exp_zero, exp_lt_exp]

@[bound] private alias ⟨_, Bound.one_lt_exp_of_pos⟩ := one_lt_exp_iff

@[simp]

中文:
定理 one_lt_exp_iff
  条件: {x : 实数}
  结论: 1 < exp x ↔ 0 < x
  证明: by rw [← exp_zero, exp_lt_exp]

@[bound] private alias ⟨_, Bound.one_lt_exp_of_pos⟩ := one_lt_exp_iff

@[simp]

Depends on / 依赖: exp_lt_exp, exp_zero
-/
theorem one_lt_exp_iff {x : Real} : 1 < exp x ↔ 0 < x := by rw [← exp_zero, exp_lt_exp]

@[bound] private alias ⟨_, Bound.one_lt_exp_of_pos⟩ := one_lt_exp_iff

@[simp]
/--
theorem `exp_lt_one_iff` / 定理 `exp_lt_one_iff`

English:
theorem exp_lt_one_iff
  given: {x : Real}
  statement: exp x < 1 ↔ x < 0
  proof: by rw [← exp_zero, exp_lt_exp]

@[simp]

中文:
定理 exp_lt_one_iff
  条件: {x : 实数}
  结论: exp x < 1 ↔ x < 0
  证明: by rw [← exp_zero, exp_lt_exp]

@[simp]

Depends on / 依赖: exp_lt_exp, exp_zero
-/
theorem exp_lt_one_iff {x : Real} : exp x < 1 ↔ x < 0 := by rw [← exp_zero, exp_lt_exp]

@[simp]
/--
theorem `exp_le_one_iff` / 定理 `exp_le_one_iff`

English:
theorem exp_le_one_iff
  given: {x : Real}
  statement: exp x <= 1 ↔ x <= 0
  proof: exp_zero ▸ exp_le_exp

@[simp]

中文:
定理 exp_le_one_iff
  条件: {x : 实数}
  结论: exp x <= 1 ↔ x <= 0
  证明: exp_zero ▸ exp_le_exp

@[simp]

Depends on / 依赖: exp_le_exp, exp_zero
-/
theorem exp_le_one_iff {x : Real} : exp x <= 1 ↔ x <= 0 :=
  exp_zero ▸ exp_le_exp

@[simp]
/--
theorem `one_le_exp_iff` / 定理 `one_le_exp_iff`

English:
theorem one_le_exp_iff
  given: {x : Real}
  statement: 1 <= exp x ↔ 0 <= x
  proof: exp_zero ▸ exp_le_exp

中文:
定理 one_le_exp_iff
  条件: {x : 实数}
  结论: 1 <= exp x ↔ 0 <= x
  证明: exp_zero ▸ exp_le_exp

Depends on / 依赖: exp_le_exp, exp_zero
-/
theorem one_le_exp_iff {x : Real} : 1 <= exp x ↔ 0 <= x :=
  exp_zero ▸ exp_le_exp

end Real

namespace Complex

/--
theorem `sum_div_factorial_le` / 定理 `sum_div_factorial_le`

English:
theorem sum_div_factorial_le
  statement: {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: calc
    (∑ m in range j with n <= m, (1 / m.factorial : α)) =
        ∑ m in range (j - n), (1 / ((m + n).factorial : α)) := by
        refine sum_nbij' (· - n) (· + n) ?_ ?_ ?_ ?_ ?_ <;>
          simp +contextual [lt_tsub_iff_right, tsub_add_cancel_of_le]
    _ <= ∑ m in range (j - n), ((n.factor

中文:
定理 sum_div_factorial_le
  结论: {α : 类型} [域 α] [线性序 α] [是StrictOrdered环 α]
  证明: calc
    (∑ m in range j with n <= m, (1 / m.factorial : α)) =
        ∑ m in range (j - n), (1 / ((m + n).factorial : α)) := by
        refine sum_nbij' (· - n) (· + n) ?_ ?_ ?_ ?_ ?_ <;>
          simp +contextual [lt_tsub_iff_right, tsub_add_cancel_of_le]
    _ <= ∑ m in range (j - n), ((n.factor

Depends on / 依赖: Nat.cast_le, Nat.cast_mul, Nat.cast_pow, Nat.factorial_mul_pow_le_factorial, add_comm, cast_le, cast_mul, cast_pow, contextual, factorial, factorial_mul_pow_le_factorial, lt_tsub_iff_right, m.factorial, n.factorial, n.succ, one_div, simp_rw, sum_nbij, tsub_add_cancel_of_le
-/
theorem sum_div_factorial_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (n j : Nat) (hn : 0 < n) :
    (∑ m in range j with n <= m, (1 / m.factorial : α)) <= n.succ / (n.factorial * n) :=
  calc
    (∑ m in range j with n <= m, (1 / m.factorial : α)) =
        ∑ m in range (j - n), (1 / ((m + n).factorial : α)) := by
        refine sum_nbij' (· - n) (· + n) ?_ ?_ ?_ ?_ ?_ <;>
          simp +contextual [lt_tsub_iff_right, tsub_add_cancel_of_le]
    _ <= ∑ m in range (j - n), ((n.factorial : α) * (n.succ : α) ^ m)⁻¹ := by
      simp_rw [one_div]
      gcongr
      rw [← Nat.cast_pow]; rw [← Nat.cast_mul]; rw [Nat.cast_le]; rw [add_comm]
      exact Nat.factorial_mul_pow_le_factorial
    _ = (n.factorial : α)⁻¹ * ∑ m in range (j - n), (n.succ : α)⁻¹ ^ m := by
      simp [← mul_sum, mul_comm, inv_pow]
    _ = ((n.succ : α) - n.succ * (n.succ : α)⁻¹ ^ (j - n)) / (n.factorial * n) := by
      have h₁ : (n.succ : α) != 1 :=
        @Nat.cast_one α _ ▸ mt Nat.cast_inj.1 (mt Nat.succ.inj (pos_iff_ne_zero.1 hn))
      have h₂ : (n.succ : α) != 0 := by positivity
      have h₃ : (n.factorial * n : α) != 0 := by positivity
      have h₄ : (n.succ - 1 : α) = n := by simp
      rw [geom_sum_inv h₁ h₂]; rw [eq_div_iff_mul_eq h₃]; rw [mul_comm _ (n.factorial * n : α)]; rw [← mul_assoc (n.factorial⁻¹ : α)]; rw [← mul_inv_rev]; rw [h₄]; rw [← mul_assoc (n.factorial * n : α)]; rw [mul_comm (n : α) n.factorial]; rw [mul_inv_cancel₀ h₃]; rw [one_mul]; rw [mul_comm]
    _ <= n.succ / (n.factorial * n : α) := by gcongr; apply sub_le_self; positivity

/--
theorem `exp_bound` / 定理 `exp_bound`

English:
theorem exp_bound
  given: {x : Complex} (hx : ‖x‖ <= 1) {n : Nat} (hn : 0 < n)
  proof: by
  rw [← lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [exp]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add]; rw [← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change
    ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ 

中文:
定理 exp_bound
  条件: {x : 复形} (hx : ‖x‖ <= 1) {n : 自然数} (hn : 0 < n)
  证明: by
  rw [← lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [exp]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add]; rw [← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change
    ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ 

Depends on / 依赖: CauSeq, CauSeq.le_of_exists, factorial, le_of_exists, lim_add, lim_const, lim_le, lim_neg, lim_norm, m.factorial, n.factorial, n.succ, simp_rw, sub_eq_add_neg, sum_range_sub_sum_range
-/
theorem exp_bound {x : Complex} (hx : ‖x‖ <= 1) {n : Nat} (hn : 0 < n) :
    ‖exp x - ∑ m in range n, x ^ m / m.factorial‖ <=
      ‖x‖ ^ n * ((n.succ : Real) * (n.factorial * n : Real)⁻¹) := by
  rw [← lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [exp]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add]; rw [← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change
    ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / m.factorial‖ <=
      ‖x‖ ^ n * ((n.succ : Real) * (n.factorial * n : Real)⁻¹)
  rw [sum_range_sub_sum_range hj]
  calc
    ‖∑ m in range j with n <= m, (x ^ m / m.factorial : Complex)‖
      = ‖∑ m in range j with n <= m, (x ^ n * (x ^ (m - n) / m.factorial) : Complex)‖ := by
      refine congr_arg norm (sum_congr rfl fun m hm => ?_)
      rw [mem_filter]; rw [mem_range] at hm
      rw [← mul_div_assoc]; rw [← pow_add]; rw [add_tsub_cancel_of_le hm.2]
    _ <= ∑ m in range j with n <= m, ‖x ^ n * (x ^ (m - n) / m.factorial)‖ :=
      IsAbsoluteValue.abv_sum norm ..
    _ <= ∑ m in range j with n <= m, ‖x‖ ^ n * (1 / m.factorial) := by
      simp_rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, norm_natCast]
      gcongr
      rw [Complex.norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖x‖ ^ n * ∑ m in range j with n <= m, (1 / m.factorial : Real) := by
      simp [← mul_sum]
    _ <= ‖x‖ ^ n * (n.succ * (n.factorial * n : Real)⁻¹) := by
      gcongr
      exact sum_div_factorial_le _ _ hn

/--
theorem `exp_bound'` / 定理 `exp_bound'`

English:
theorem exp_bound'
  given: {x : Complex} {n : Nat} (hx : ‖x‖ / n.succ <= 1 / 2)
  proof: by
  rw [← lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [exp]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add]; rw [← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / 

中文:
定理 exp_bound'
  条件: {x : 复形} {n : 自然数} (hx : ‖x‖ / n.succ <= 1 / 2)
  证明: by
  rw [← lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [exp]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add]; rw [← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / 

Depends on / 依赖: CauSeq, CauSeq.le_of_exists, add_tsub_cancel_of_le, factorial, le_of_exists, lim_add, lim_const, lim_le, lim_neg, lim_norm, m.factorial, n.factorial, simp_rw, sub_eq_add_neg, sum_range_add_sub_sum_range
-/
theorem exp_bound' {x : Complex} {n : Nat} (hx : ‖x‖ / n.succ <= 1 / 2) :
    ‖exp x - ∑ m in range n, x ^ m / m.factorial‖ <= ‖x‖ ^ n / n.factorial * 2 := by
  rw [← lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [exp]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add]; rw [← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  change ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / m.factorial‖ <=
    ‖x‖ ^ n / n.factorial * 2
  let k := j - n
  have hj : j = n + k := (add_tsub_cancel_of_le hj).symm
  rw [hj]; rw [sum_range_add_sub_sum_range]
  calc
    ‖∑ i in range k, x ^ (n + i) / ((n + i).factorial : Complex)‖ <=
        ∑ i in range k, ‖x ^ (n + i) / ((n + i).factorial : Complex)‖ :=
      IsAbsoluteValue.abv_sum _ _ _
    _ <= ∑ i in range k, ‖x‖ ^ (n + i) / (n + i).factorial := by
      simp [norm_natCast, Complex.norm_pow]
    _ <= ∑ i in range k, ‖x‖ ^ (n + i) / ((n.factorial : Real) * (n.succ : Real) ^ i) := ?_
    _ = ∑ i in range k, ‖x‖ ^ n / n.factorial * (‖x‖ ^ i / (n.succ : Real) ^ i) := ?_
    _ <= ‖x‖ ^ n / ↑n.factorial * 2 := ?_
  · gcongr
    exact mod_cast Nat.factorial_mul_pow_le_factorial
  · simp only [pow_add, div_eq_inv_mul, mul_inv, mul_left_comm, mul_assoc]
  · rw [← mul_sum]
    gcongr
    simp_rw [← div_pow]
    rw [geom_sum_eq]; rw [div_le_iff_of_neg]
    · trans (-1 : Real)
      · linarith
      · simp only [neg_le_sub_iff_le_add, div_pow, Nat.cast_succ, le_add_iff_nonneg_left]
        positivity
    · linarith
    · linarith

/--
theorem `norm_exp_sub_one_le` / 定理 `norm_exp_sub_one_le`

English:
theorem norm_exp_sub_one_le
  given: {x : Complex} (hx : ‖x‖ <= 1)
  statement: ‖exp x - 1‖ <= 2 * ‖x‖
  proof: calc
    ‖exp x - 1‖ = ‖exp x - ∑ m in range 1, x ^ m / m.factorial‖ := by simp
    _ <= ‖x‖ ^ 1 * ((Nat.succ 1 : Real) * ((Nat.factorial 1) * (1 : Nat) : Real)⁻¹) :=
      (exp_bound hx (by decide))
    _ = 2 * ‖x‖ := by simp [mul_two, mul_add, mul_comm, Nat.factorial]

中文:
定理 norm_exp_sub_one_le
  条件: {x : 复形} (hx : ‖x‖ <= 1)
  结论: ‖exp x - 1‖ <= 2 * ‖x‖
  证明: calc
    ‖exp x - 1‖ = ‖exp x - ∑ m in range 1, x ^ m / m.factorial‖ := by simp
    _ <= ‖x‖ ^ 1 * ((Nat.succ 1 : Real) * ((Nat.factorial 1) * (1 : Nat) : Real)⁻¹) :=
      (exp_bound hx (by decide))
    _ = 2 * ‖x‖ := by simp [mul_two, mul_add, mul_comm, Nat.factorial]

Depends on / 依赖: Nat.factorial, Nat.succ, exp_bound, factorial, m.factorial, mul_add, mul_comm, mul_two
-/
theorem norm_exp_sub_one_le {x : Complex} (hx : ‖x‖ <= 1) : ‖exp x - 1‖ <= 2 * ‖x‖ :=
  calc
    ‖exp x - 1‖ = ‖exp x - ∑ m in range 1, x ^ m / m.factorial‖ := by simp
    _ <= ‖x‖ ^ 1 * ((Nat.succ 1 : Real) * ((Nat.factorial 1) * (1 : Nat) : Real)⁻¹) :=
      (exp_bound hx (by decide))
    _ = 2 * ‖x‖ := by simp [mul_two, mul_add, mul_comm, Nat.factorial]

/--
theorem `norm_exp_sub_one_sub_id_le` / 定理 `norm_exp_sub_one_sub_id_le`

English:
theorem norm_exp_sub_one_sub_id_le
  given: {x : Complex} (hx : ‖x‖ <= 1)
  statement: ‖exp x - 1 - x‖ <= ‖x‖ ^ 2
  proof: calc
    ‖exp x - 1 - x‖ = ‖exp x - ∑ m in range 2, x ^ m / m.factorial‖ := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc, Nat.factorial]
    _ <= ‖x‖ ^ 2 * ((Nat.succ 2 : Real) * (Nat.factorial 2 * (2 : Nat) : Real)⁻¹) :=
      (exp_bound hx (by decide))
    _ <= ‖x‖ ^ 2 * 1 := by g

中文:
定理 norm_exp_sub_one_sub_id_le
  条件: {x : 复形} (hx : ‖x‖ <= 1)
  结论: ‖exp x - 1 - x‖ <= ‖x‖ ^ 2
  证明: calc
    ‖exp x - 1 - x‖ = ‖exp x - ∑ m in range 2, x ^ m / m.factorial‖ := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc, Nat.factorial]
    _ <= ‖x‖ ^ 2 * ((Nat.succ 2 : Real) * (Nat.factorial 2 * (2 : Nat) : Real)⁻¹) :=
      (exp_bound hx (by decide))
    _ <= ‖x‖ ^ 2 * 1 := by g

Depends on / 依赖: Nat.factorial, Nat.succ, add_assoc, exp_bound, factorial, m.factorial, mul_one, sub_eq_add_neg, sum_range_succ_comm
-/
theorem norm_exp_sub_one_sub_id_le {x : Complex} (hx : ‖x‖ <= 1) : ‖exp x - 1 - x‖ <= ‖x‖ ^ 2 :=
  calc
    ‖exp x - 1 - x‖ = ‖exp x - ∑ m in range 2, x ^ m / m.factorial‖ := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc, Nat.factorial]
    _ <= ‖x‖ ^ 2 * ((Nat.succ 2 : Real) * (Nat.factorial 2 * (2 : Nat) : Real)⁻¹) :=
      (exp_bound hx (by decide))
    _ <= ‖x‖ ^ 2 * 1 := by gcongr; norm_num [Nat.factorial]
    _ = ‖x‖ ^ 2 := by rw [mul_one]

/--
theorem `_root_.Real.norm_exp_sub_one_sub_id_le` / 定理 `_root_.Real.norm_exp_sub_one_sub_id_le`

English:
theorem _root_.Real.norm_exp_sub_one_sub_id_le
  given: {x : Real} (hx : ‖x‖ <= 1)
  proof: calc
  _ = ‖((Real.exp x - 1 - x) : Complex)‖ := by exact_mod_cast Complex.norm_real _
  _ = ‖Complex.exp x - 1 - (x : Complex)‖ := by simp
  _ <= ‖(x : Complex)‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le (by exact_mod_cast hx)
  _ = ‖x‖ ^ 2 := by simp

中文:
定理 _root_.实数.norm_exp_sub_one_sub_id_le
  条件: {x : 实数} (hx : ‖x‖ <= 1)
  证明: calc
  _ = ‖((Real.exp x - 1 - x) : Complex)‖ := by exact_mod_cast Complex.norm_real _
  _ = ‖Complex.exp x - 1 - (x : Complex)‖ := by simp
  _ <= ‖(x : Complex)‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le (by exact_mod_cast hx)
  _ = ‖x‖ ^ 2 := by simp
-/
theorem _root_.Real.norm_exp_sub_one_sub_id_le {x : Real} (hx : ‖x‖ <= 1) :
    ‖Real.exp x - 1 - x‖ <= ‖x‖ ^ 2 := calc
  _ = ‖((Real.exp x - 1 - x) : Complex)‖ := by exact_mod_cast Complex.norm_real _
  _ = ‖Complex.exp x - 1 - (x : Complex)‖ := by simp
  _ <= ‖(x : Complex)‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le (by exact_mod_cast hx)
  _ = ‖x‖ ^ 2 := by simp

/--
lemma `norm_exp_sub_sum_le_exp_norm_sub_sum` / 引理 `norm_exp_sub_sum_le_exp_norm_sub_sum`

English:
lemma norm_exp_sub_sum_le_exp_norm_sub_sum
  given: (x : Complex) (n : Nat)
  proof: by
  rw [← CauSeq.lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [Complex.exp]; rw [sub_eq_add_neg]; rw [← CauSeq.lim_neg]; rw [CauSeq.lim_add]; rw [← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  calc ‖(∑ m in range j, x ^ m / m.fac

中文:
引理 norm_exp_sub_sum_le_exp_norm_sub_sum
  条件: (x : 复形) (n : 自然数)
  证明: by
  rw [← CauSeq.lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [Complex.exp]; rw [sub_eq_add_neg]; rw [← CauSeq.lim_neg]; rw [CauSeq.lim_add]; rw [← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  calc ‖(∑ m in range j, x ^ m / m.fac

Depends on / 依赖: CStarModule, CauSeq, CauSeq.le_of_exists, CauSeq.lim_add, CauSeq.lim_const, CauSeq.lim_le, CauSeq.lim_neg, Complex.exp, algebra, factorial, inherits, instance, le_of_exists, lim_add, lim_const, lim_le, lim_neg, lim_norm, m.factorial, simp_rw
-/
lemma norm_exp_sub_sum_le_exp_norm_sub_sum (x : Complex) (n : Nat) :
    ‖exp x - ∑ m in range n, x ^ m / m.factorial‖
      <= Real.exp ‖x‖ - ∑ m in range n, ‖x‖ ^ m / m.factorial := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [Complex.exp]; rw [sub_eq_add_neg]; rw [← CauSeq.lim_neg]; rw [CauSeq.lim_add]; rw [← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  calc ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / m.factorial‖
  _ <= (∑ m in range j, ‖x‖ ^ m / m.factorial) - ∑ m in range n, ‖x‖ ^ m / m.factorial := by
    rw [sum_range_sub_sum_range hj]; rw [sum_range_sub_sum_range hj]
    refine (IsAbsoluteValue.abv_sum norm ..).trans_eq ?_
    congr with i
    simp [Complex.norm_pow, Complex.norm_natCast]
  _ <= Real.exp ‖x‖ - ∑ m in range n, ‖x‖ ^ m / m.factorial := by
    gcongr
    exact Real.sum_le_exp_of_nonneg (norm_nonneg _) _

/--
lemma `norm_exp_le_exp_norm` / 引理 `norm_exp_le_exp_norm`

English:
lemma norm_exp_le_exp_norm
  given: (x : Complex)
  statement: ‖exp x‖ <= Real.exp ‖x‖
  proof: by
  convert norm_exp_sub_sum_le_exp_norm_sub_sum x 0 <;> simp

中文:
引理 norm_exp_le_exp_norm
  条件: (x : 复形)
  结论: ‖exp x‖ <= 实数.exp ‖x‖
  证明: by
  convert norm_exp_sub_sum_le_exp_norm_sub_sum x 0 <;> simp

Depends on / 依赖: convert, norm_exp_sub_sum_le_exp_norm_sub_sum
-/
lemma norm_exp_le_exp_norm (x : Complex) : ‖exp x‖ <= Real.exp ‖x‖ := by
  convert norm_exp_sub_sum_le_exp_norm_sub_sum x 0 <;> simp

/--
lemma `norm_exp_sub_sum_le_norm_mul_exp` / 引理 `norm_exp_sub_sum_le_norm_mul_exp`

English:
lemma norm_exp_sub_sum_le_norm_mul_exp
  given: (x : Complex) (n : Nat)
  proof: by
  rw [← CauSeq.lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [Complex.exp]; rw [sub_eq_add_neg]; rw [← CauSeq.lim_neg]; rw [CauSeq.lim_add]; rw [← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  change ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x

中文:
引理 norm_exp_sub_sum_le_norm_mul_exp
  条件: (x : 复形) (n : 自然数)
  证明: by
  rw [← CauSeq.lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [Complex.exp]; rw [sub_eq_add_neg]; rw [← CauSeq.lim_neg]; rw [CauSeq.lim_add]; rw [← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  change ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x

Depends on / 依赖: CauSeq, CauSeq.le_of_exists, CauSeq.lim_add, CauSeq.lim_const, CauSeq.lim_le, CauSeq.lim_neg, Complex.exp, congr_arg, factorial, le_of_exists, lim_add, lim_const, lim_le, lim_neg, lim_norm, m.factorial, sub_eq_add_neg, sum_Ico_eq_sub
-/
lemma norm_exp_sub_sum_le_norm_mul_exp (x : Complex) (n : Nat) :
    ‖exp x - ∑ m in range n, x ^ m / m.factorial‖ <= ‖x‖ ^ n * Real.exp ‖x‖ := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m in range n]; rw [_)]; rw [Complex.exp]; rw [sub_eq_add_neg]; rw [← CauSeq.lim_neg]; rw [CauSeq.lim_add]; rw [← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  change ‖(∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / m.factorial‖ <= _
  rw [← sum_Ico_eq_sub _ hj]
  calc
    ‖∑ m in Ico n j, (x ^ m / m.factorial : Complex)‖
      = ‖∑ m in Ico n j, (x ^ n * (x ^ (m - n) / m.factorial) : Complex)‖ := by
      refine congr_arg norm (sum_congr rfl fun m hm => ?_)
      rw [mem_Ico] at hm
      rw [← mul_div_assoc]; rw [← pow_add]; rw [add_tsub_cancel_of_le hm.1]
    _ <= ∑ m in Ico n j, ‖x ^ n * (x ^ (m - n) / m.factorial)‖ :=
      IsAbsoluteValue.abv_sum norm ..
    _ <= ∑ m in Ico n j, ‖x‖ ^ n * (‖x‖ ^ (m - n) / (m - n).factorial) := by
      simp_rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, norm_natCast]
      gcongr with i hi
      · rw [Complex.norm_pow]
      · simp
    _ = ‖x‖ ^ n * ∑ m in range (j - n), (‖x‖ ^ m / m.factorial) := by
      simp [← mul_sum, sum_Ico_eq_sum_range]
    _ <= ‖x‖ ^ n * Real.exp ‖x‖ := by
      gcongr
      refine Real.sum_le_exp_of_nonneg ?_ _
      exact norm_nonneg _

end Complex

namespace Real

open Complex Finset

nonrec theorem exp_bound {x : Real} (hx : |x| <= 1) {n : Nat} (hn : 0 < n) :
    |exp x - ∑ m in range n, x ^ m / m.factorial| <= |x| ^ n * (n.succ / (n.factorial * n)) := by
  have hxc : ‖(x : Complex)‖ <= 1 := mod_cast hx
  convert exp_bound hxc hn <;>
  norm_cast

/--
theorem `exp_bound'` / 定理 `exp_bound'`

English:
theorem exp_bound'
  given: {x : Real} (h1 : 0 <= x) (h2 : x <= 1) {n : Nat} (hn : 0 < n)
  proof: by
  have h3 : |x| = x := by simpa
  have h4 : |x| <= 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t

中文:
定理 exp_bound'
  条件: {x : 实数} (h1 : 0 <= x) (h2 : x <= 1) {n : 自然数} (hn : 0 < n)
  证明: by
  have h3 : |x| = x := by simpa
  have h4 : |x| <= 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t

Depends on / 依赖: Real.exp_bound, abs_sub_le_iff, exp_bound, mul_div_assoc, sub_le_iff_le_add
-/
theorem exp_bound' {x : Real} (h1 : 0 <= x) (h2 : x <= 1) {n : Nat} (hn : 0 < n) :
    Real.exp x <= (∑ m in Finset.range n, x ^ m / m.factorial) +
      x ^ n * (n + 1) / (n.factorial * n) := by
  have h3 : |x| = x := by simpa
  have h4 : |x| <= 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t

/--
theorem `abs_exp_sub_one_le` / 定理 `abs_exp_sub_one_le`

English:
theorem abs_exp_sub_one_le
  given: {x : Real} (hx : |x| <= 1)
  statement: |exp x - 1| <= 2 * |x|
  proof: by
  have : ‖(x : Complex)‖ <= 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_le (x := x) this

中文:
定理 abs_exp_sub_one_le
  条件: {x : 实数} (hx : |x| <= 1)
  结论: |exp x - 1| <= 2 * |x|
  证明: by
  have : ‖(x : Complex)‖ <= 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_le (x := x) this

Depends on / 依赖: Complex.norm_exp_sub_one_le, mod_cast, norm_exp_sub_one_le
-/
theorem abs_exp_sub_one_le {x : Real} (hx : |x| <= 1) : |exp x - 1| <= 2 * |x| := by
  have : ‖(x : Complex)‖ <= 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_le (x := x) this

/--
theorem `abs_exp_sub_one_sub_id_le` / 定理 `abs_exp_sub_one_sub_id_le`

English:
theorem abs_exp_sub_one_sub_id_le
  given: {x : Real} (hx : |x| <= 1)
  statement: |exp x - 1 - x| <= x ^ 2
  proof: by
  rw [← sq_abs]
  have : ‖(x : Complex)‖ <= 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_sub_id_le this

中文:
定理 abs_exp_sub_one_sub_id_le
  条件: {x : 实数} (hx : |x| <= 1)
  结论: |exp x - 1 - x| <= x ^ 2
  证明: by
  rw [← sq_abs]
  have : ‖(x : Complex)‖ <= 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_sub_id_le this

Depends on / 依赖: Complex.norm_exp_sub_one_sub_id_le, mod_cast, norm_exp_sub_one_sub_id_le, sq_abs
-/
theorem abs_exp_sub_one_sub_id_le {x : Real} (hx : |x| <= 1) : |exp x - 1 - x| <= x ^ 2 := by
  rw [← sq_abs]
  have : ‖(x : Complex)‖ <= 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_sub_id_le this

/--
Definition of `expNear` / `expNear` 的定义

English:
definition expNear
  signature: (n : Nat) (x r : Real)
  body: (∑ m in range n, x ^ m / m.factorial) + x ^ n / n.factorial * r

@[simp]

中文:
定义 expNear
  签名: (n : 自然数) (x r : 实数)
  定义体: (∑ m in range n, x ^ m / m.factorial) + x ^ n / n.factorial * r

@[simp]

Depends on / 依赖: factorial, m.factorial, n.factorial
-/
noncomputable def expNear (n : Nat) (x r : Real) : Real :=
  (∑ m in range n, x ^ m / m.factorial) + x ^ n / n.factorial * r

@[simp]
/--
theorem `expNear_zero` / 定理 `expNear_zero`

English:
theorem expNear_zero
  given: (x r)
  statement: expNear 0 x r = r
  proof: by simp [expNear]

@[simp]

中文:
定理 expNear_zero
  条件: (x r)
  结论: expNear 0 x r = r
  证明: by simp [expNear]

@[simp]

Depends on / 依赖: expNear
-/
theorem expNear_zero (x r) : expNear 0 x r = r := by simp [expNear]

@[simp]
/--
theorem `expNear_succ` / 定理 `expNear_succ`

English:
theorem expNear_succ
  given: (n x r)
  statement: expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r)
  proof: by
  simp [expNear, range_add_one, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
    Nat.factorial]
  ac_rfl

中文:
定理 expNear_succ
  条件: (n x r)
  结论: expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r)
  证明: by
  simp [expNear, range_add_one, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
    Nat.factorial]
  ac_rfl

Depends on / 依赖: Nat.factorial, add_assoc, add_left_comm, div_eq_mul_inv, expNear, factorial, mul_add, pow_succ, range_add_one
-/
theorem expNear_succ (n x r) : expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r) := by
  simp [expNear, range_add_one, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
    Nat.factorial]
  ac_rfl

/--
theorem `expNear_sub` / 定理 `expNear_sub`

English:
theorem expNear_sub
  given: (n x r₁ r₂)
  statement: expNear n x r₁ -
  proof: by
  simp [expNear, mul_sub]

中文:
定理 expNear_sub
  条件: (n x r₁ r₂)
  结论: expNear n x r₁ -
  证明: by
  simp [expNear, mul_sub]

Depends on / 依赖: expNear, mul_sub
-/
theorem expNear_sub (n x r₁ r₂) : expNear n x r₁ -
    expNear n x r₂ = x ^ n / n.factorial * (r₁ - r₂) := by
  simp [expNear, mul_sub]

/--
theorem `exp_approx_end` / 定理 `exp_approx_end`

English:
theorem exp_approx_end
  given: (n m : Nat) (x : Real) (e₁ : n + 1 = m) (h : |x| <= 1)
  proof: by
  simp only [expNear, mul_zero, add_zero]
  convert! exp_bound (n := m) h ?_ using 1
  · simp [field]
  · lia

中文:
定理 exp_approx_end
  条件: (n m : 自然数) (x : 实数) (e₁ : n + 1 = m) (h : |x| <= 1)
  证明: by
  simp only [expNear, mul_zero, add_zero]
  convert! exp_bound (n := m) h ?_ using 1
  · simp [field]
  · lia

Depends on / 依赖: add_zero, convert, expNear, exp_bound, mul_zero
-/
theorem exp_approx_end (n m : Nat) (x : Real) (e₁ : n + 1 = m) (h : |x| <= 1) :
    |exp x - expNear m x 0| <= |x| ^ m / m.factorial * ((m + 1) / m) := by
  simp only [expNear, mul_zero, add_zero]
  convert! exp_bound (n := m) h ?_ using 1
  · simp [field]
  · lia

/--
theorem `exp_approx_succ` / 定理 `exp_approx_succ`

English:
theorem exp_approx_succ
  statement: {n} {x a₁ b₁ : Real} (m : Nat) (e₁ : n + 1 = m) (a₂ b₂ : Real)
  proof: by
  grw [abs_sub_le, h]
  subst e₁; rw [expNear_succ, expNear_sub, abs_mul]
  convert!
    mul_le_mul_of_nonneg_left (a := |x| ^ n / ↑(Nat.factorial n)) (le_sub_iff_add_le'.1 e) ?_
      using 1
  · simp [mul_add, pow_succ', div_eq_mul_inv, abs_mul, abs_inv, Nat.factorial]
    ac_rfl
  · simp [div_

中文:
定理 exp_approx_succ
  结论: {n} {x a₁ b₁ : 实数} (m : 自然数) (e₁ : n + 1 = m) (a₂ b₂ : 实数)
  证明: by
  grw [abs_sub_le, h]
  subst e₁; rw [expNear_succ, expNear_sub, abs_mul]
  convert!
    mul_le_mul_of_nonneg_left (a := |x| ^ n / ↑(Nat.factorial n)) (le_sub_iff_add_le'.1 e) ?_
      using 1
  · simp [mul_add, pow_succ', div_eq_mul_inv, abs_mul, abs_inv, Nat.factorial]
    ac_rfl
  · simp [div_

Depends on / 依赖: Nat.factorial, abs_inv, abs_mul, abs_nonneg, abs_sub_le, convert, div_eq_mul_inv, div_nonneg, expNear_sub, expNear_succ, factorial, le_sub_iff_add_le, mul_add, mul_le_mul_of_nonneg_left, pow_succ
-/
theorem exp_approx_succ {n} {x a₁ b₁ : Real} (m : Nat) (e₁ : n + 1 = m) (a₂ b₂ : Real)
    (e : |1 + x / m * a₂ - a₁| <= b₁ - |x| / m * b₂)
    (h : |exp x - expNear m x a₂| <= |x| ^ m / m.factorial * b₂) :
    |exp x - expNear n x a₁| <= |x| ^ n / n.factorial * b₁ := by
  grw [abs_sub_le, h]
  subst e₁; rw [expNear_succ, expNear_sub, abs_mul]
  convert!
    mul_le_mul_of_nonneg_left (a := |x| ^ n / ↑(Nat.factorial n)) (le_sub_iff_add_le'.1 e) ?_
      using 1
  · simp [mul_add, pow_succ', div_eq_mul_inv, abs_mul, abs_inv, Nat.factorial]
    ac_rfl
  · simp [div_nonneg, abs_nonneg]

/--
theorem `exp_approx_end'` / 定理 `exp_approx_end'`

English:
theorem exp_approx_end'
  statement: {n} {x a b : Real} (m : Nat) (e₁ : n + 1 = m) (rm : Real) (er : ↑m = rm)
  proof: by
  subst er
  exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)

中文:
定理 exp_approx_end'
  结论: {n} {x a b : 实数} (m : 自然数) (e₁ : n + 1 = m) (rm : 实数) (er : ↑m = rm)
  证明: by
  subst er
  exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)

Depends on / 依赖: exp_approx_end, exp_approx_succ
-/
theorem exp_approx_end' {n} {x a b : Real} (m : Nat) (e₁ : n + 1 = m) (rm : Real) (er : ↑m = rm)
    (h : |x| <= 1) (e : |1 - a| <= b - |x| / rm * ((rm + 1) / rm)) :
    |exp x - expNear n x a| <= |x| ^ n / n.factorial * b := by
  subst er
  exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)

/--
theorem `exp_1_approx_succ_eq` / 定理 `exp_1_approx_succ_eq`

English:
theorem exp_1_approx_succ_eq
  statement: {n} {a₁ b₁ : Real} {m : Nat} (en : n + 1 = m) {rm : Real} (er : ↑m = rm)
  proof: by
  subst er
  refine exp_approx_succ _ en _ _ ?_ h
  simp
  field_simp [show (m : Real) != 0 by norm_cast; lia]
  simp

中文:
定理 exp_1_approx_succ_eq
  结论: {n} {a₁ b₁ : 实数} {m : 自然数} (en : n + 1 = m) {rm : 实数} (er : ↑m = rm)
  证明: by
  subst er
  refine exp_approx_succ _ en _ _ ?_ h
  simp
  field_simp [show (m : Real) != 0 by norm_cast; lia]
  simp

Depends on / 依赖: exp_approx_succ
-/
theorem exp_1_approx_succ_eq {n} {a₁ b₁ : Real} {m : Nat} (en : n + 1 = m) {rm : Real} (er : ↑m = rm)
    (h : |exp 1 - expNear m 1 ((a₁ - 1) * rm)| <= |1| ^ m / m.factorial * (b₁ * rm)) :
    |exp 1 - expNear n 1 a₁| <= |1| ^ n / n.factorial * b₁ := by
  subst er
  refine exp_approx_succ _ en _ _ ?_ h
  simp
  field_simp [show (m : Real) != 0 by norm_cast; lia]
  simp

/--
theorem `exp_approx_start` / 定理 `exp_approx_start`

English:
theorem exp_approx_start
  given: (x a b : Real) (h : |exp x - expNear 0 x a| <= |x| ^ 0 / Nat.factorial 0 * b)
  proof: by simpa using h

中文:
定理 exp_approx_start
  条件: (x a b : 实数) (h : |exp x - expNear 0 x a| <= |x| ^ 0 / 自然数.factorial 0 * b)
  证明: by simpa using h
-/
theorem exp_approx_start (x a b : Real) (h : |exp x - expNear 0 x a| <= |x| ^ 0 / Nat.factorial 0 * b) :
    |exp x - a| <= b := by simpa using h

/--
theorem `exp_bound_div_one_sub_of_interval'` / 定理 `exp_bound_div_one_sub_of_interval'`

English:
theorem exp_bound_div_one_sub_of_interval'
  given: {x : Real} (h1 : 0 < x) (h2 : x < 1)
  proof: by
  have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x) := calc
    0 < x ^ 3 := by positivity
    _ = 1 - (1 + x + x ^ 2) * (1 - x) := by ring
  calc
    exp x <= _ := exp_bound' h1.le h2.le zero_lt_three
    _ <= 1 + x + x ^ 2 := by
      -- Porting note: was `norm_num [Finset.sum] <;> nlinarith`
      --

中文:
定理 exp_bound_div_one_sub_of_interval'
  条件: {x : 实数} (h1 : 0 < x) (h2 : x < 1)
  证明: by
  have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x) := calc
    0 < x ^ 3 := by positivity
    _ = 1 - (1 + x + x ^ 2) * (1 - x) := by ring
  calc
    exp x <= _ := exp_bound' h1.le h2.le zero_lt_three
    _ <= 1 + x + x ^ 2 := by
      -- Porting note: was `norm_num [Finset.sum] <;> nlinarith`
      --

Depends on / 依赖: exp_bound, h1.le, h2.le, zero_lt_three
-/
theorem exp_bound_div_one_sub_of_interval' {x : Real} (h1 : 0 < x) (h2 : x < 1) :
    Real.exp x < 1 / (1 - x) := by
  have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x) := calc
    0 < x ^ 3 := by positivity
    _ = 1 - (1 + x + x ^ 2) * (1 - x) := by ring
  calc
    exp x <= _ := exp_bound' h1.le h2.le zero_lt_three
    _ <= 1 + x + x ^ 2 := by
      -- Porting note: was `norm_num [Finset.sum] <;> nlinarith`
      -- This proof should be restored after the norm_num plugin for big operators is ported.
      -- (It may also need the positivity extensions in https://github.com/leanprover-community/mathlib4/pull/3907.)
      rw [show 3 = 1 + 1 + 1 from rfl]
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
      nlinarith
    _ < 1 / (1 - x) := by rw [lt_div_iff₀] <;> nlinarith

/--
theorem `exp_bound_div_one_sub_of_interval` / 定理 `exp_bound_div_one_sub_of_interval`

English:
theorem exp_bound_div_one_sub_of_interval
  given: {x : Real} (h1 : 0 <= x) (h2 : x < 1)
  proof: by
  rcases eq_or_lt_of_le h1 with (rfl | h1)
  · simp
  · exact (exp_bound_div_one_sub_of_interval' h1 h2).le

中文:
定理 exp_bound_div_one_sub_of_interval
  条件: {x : 实数} (h1 : 0 <= x) (h2 : x < 1)
  证明: by
  rcases eq_or_lt_of_le h1 with (rfl | h1)
  · simp
  · exact (exp_bound_div_one_sub_of_interval' h1 h2).le

Depends on / 依赖: eq_or_lt_of_le, exp_bound_div_one_sub_of_interval
-/
theorem exp_bound_div_one_sub_of_interval {x : Real} (h1 : 0 <= x) (h2 : x < 1) :
    Real.exp x <= 1 / (1 - x) := by
  rcases eq_or_lt_of_le h1 with (rfl | h1)
  · simp
  · exact (exp_bound_div_one_sub_of_interval' h1 h2).le

/--
theorem `add_one_lt_exp` / 定理 `add_one_lt_exp`

English:
theorem add_one_lt_exp
  given: {x : Real} (hx : x != 0)
  statement: x + 1 < Real.exp x
  proof: by
  obtain hx | hx := hx.symm.lt_or_gt
  · exact add_one_lt_exp_of_pos hx
  obtain h' | h' := le_or_gt 1 (-x)
  · linarith [x.exp_pos]
  have hx' : 0 < x + 1 := by linarith
  simpa [add_comm, exp_neg, inv_lt_inv₀ (exp_pos _) hx']
    using exp_bound_div_one_sub_of_interval' (neg_pos.2 hx) h'

中文:
定理 add_one_lt_exp
  条件: {x : 实数} (hx : x != 0)
  结论: x + 1 < 实数.exp x
  证明: by
  obtain hx | hx := hx.symm.lt_or_gt
  · exact add_one_lt_exp_of_pos hx
  obtain h' | h' := le_or_gt 1 (-x)
  · linarith [x.exp_pos]
  have hx' : 0 < x + 1 := by linarith
  simpa [add_comm, exp_neg, inv_lt_inv₀ (exp_pos _) hx']
    using exp_bound_div_one_sub_of_interval' (neg_pos.2 hx) h'

Depends on / 依赖: add_comm, add_one_lt_exp_of_pos, exp_bound_div_one_sub_of_interval, exp_neg, exp_pos, hx.symm.lt_or_gt, le_or_gt, lt_or_gt, neg_pos, x.exp_pos
-/
theorem add_one_lt_exp {x : Real} (hx : x != 0) : x + 1 < Real.exp x := by
  obtain hx | hx := hx.symm.lt_or_gt
  · exact add_one_lt_exp_of_pos hx
  obtain h' | h' := le_or_gt 1 (-x)
  · linarith [x.exp_pos]
  have hx' : 0 < x + 1 := by linarith
  simpa [add_comm, exp_neg, inv_lt_inv₀ (exp_pos _) hx']
    using exp_bound_div_one_sub_of_interval' (neg_pos.2 hx) h'

/--
theorem `add_one_le_exp` / 定理 `add_one_le_exp`

English:
theorem add_one_le_exp
  given: (x : Real)
  statement: x + 1 <= Real.exp x
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (add_one_lt_exp hx).le

中文:
定理 add_one_le_exp
  条件: (x : 实数)
  结论: x + 1 <= 实数.exp x
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (add_one_lt_exp hx).le

Depends on / 依赖: add_one_lt_exp, eq_or_ne
-/
theorem add_one_le_exp (x : Real) : x + 1 <= Real.exp x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (add_one_lt_exp hx).le

/--
lemma `one_sub_lt_exp_neg` / 引理 `one_sub_lt_exp_neg`

English:
lemma one_sub_lt_exp_neg
  given: {x : Real} (hx : x != 0)
  statement: 1 - x < exp (-x)
  proof: (sub_eq_neg_add _ _).trans_lt add_one_lt_exp neg_ne_zero.2 hx

中文:
引理 one_sub_lt_exp_neg
  条件: {x : 实数} (hx : x != 0)
  结论: 1 - x < exp (-x)
  证明: (sub_eq_neg_add _ _).trans_lt add_one_lt_exp neg_ne_zero.2 hx

Depends on / 依赖: add_one_lt_exp, neg_ne_zero, sub_eq_neg_add, trans_lt
-/
lemma one_sub_lt_exp_neg {x : Real} (hx : x != 0) : 1 - x < exp (-x) :=
(sub_eq_neg_add _ _).trans_lt add_one_lt_exp neg_ne_zero.2 hx

/--
lemma `one_sub_le_exp_neg` / 引理 `one_sub_le_exp_neg`

English:
lemma one_sub_le_exp_neg
  given: (x : Real)
  statement: 1 - x <= exp (-x)
  proof: (sub_eq_neg_add _ _).trans_le add_one_le_exp _

中文:
引理 one_sub_le_exp_neg
  条件: (x : 实数)
  结论: 1 - x <= exp (-x)
  证明: (sub_eq_neg_add _ _).trans_le add_one_le_exp _

Depends on / 依赖: add_one_le_exp, sub_eq_neg_add, trans_le
-/
lemma one_sub_le_exp_neg (x : Real) : 1 - x <= exp (-x) :=
(sub_eq_neg_add _ _).trans_le add_one_le_exp _

/--
theorem `one_sub_div_pow_le_exp_neg` / 定理 `one_sub_div_pow_le_exp_neg`

English:
theorem one_sub_div_pow_le_exp_neg
  given: {n : Nat} {t : Real} (ht' : t <= n)
  statement: (1 - t / n) ^ n <= exp (-t)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  calc
    (1 - t / n) ^ n <= rexp (-(t / n)) ^ n := by
      gcongr
· exact sub_nonneg.2 div_le_one_of_le₀ ht' n.cast_nonneg
      · exact one_sub_le_exp_neg _
    _ = rexp (-t) := by rw [← Real.exp_nat_mul, mul_neg, m

中文:
定理 one_sub_div_pow_le_exp_neg
  条件: {n : 自然数} {t : 实数} (ht' : t <= n)
  结论: (1 - t / n) ^ n <= exp (-t)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  calc
    (1 - t / n) ^ n <= rexp (-(t / n)) ^ n := by
      gcongr
· exact sub_nonneg.2 div_le_one_of_le₀ ht' n.cast_nonneg
      · exact one_sub_le_exp_neg _
    _ = rexp (-t) := by rw [← Real.exp_nat_mul, mul_neg, m

Depends on / 依赖: Nat.cast_zero, Real.exp_nat_mul, cast_nonneg, cast_zero, eq_or_ne, exp_nat_mul, mul_comm, mul_neg, n.cast_nonneg, one_sub_le_exp_neg, sub_nonneg
-/
theorem one_sub_div_pow_le_exp_neg {n : Nat} {t : Real} (ht' : t <= n) : (1 - t / n) ^ n <= exp (-t) := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  calc
    (1 - t / n) ^ n <= rexp (-(t / n)) ^ n := by
      gcongr
· exact sub_nonneg.2 div_le_one_of_le₀ ht' n.cast_nonneg
      · exact one_sub_le_exp_neg _
    _ = rexp (-t) := by rw [← Real.exp_nat_mul, mul_neg, mul_comm, div_mul_cancel₀]; positivity

/--
lemma `one_add_inv_pow_le_exp` / 引理 `one_add_inv_pow_le_exp`

English:
lemma one_add_inv_pow_le_exp
  given: {n : Nat}
  statement: (1 + (n : Real)⁻¹) ^ n <= exp 1
  proof: by
  convert one_sub_div_pow_le_exp_neg (n := n) (t := -1) (by grind) using 1
  · field
  · simp

中文:
引理 one_add_inv_pow_le_exp
  条件: {n : 自然数}
  结论: (1 + (n : 实数)⁻¹) ^ n <= exp 1
  证明: by
  convert one_sub_div_pow_le_exp_neg (n := n) (t := -1) (by grind) using 1
  · field
  · simp

Depends on / 依赖: convert, one_sub_div_pow_le_exp_neg
-/
lemma one_add_inv_pow_le_exp {n : Nat} : (1 + (n : Real)⁻¹) ^ n <= exp 1 := by
  convert one_sub_div_pow_le_exp_neg (n := n) (t := -1) (by grind) using 1
  · field
  · simp

/--
lemma `le_inv_mul_exp` / 引理 `le_inv_mul_exp`

English:
lemma le_inv_mul_exp
  given: (x : Real) {c : Real} (hc : 0 < c)
  statement: x <= c⁻¹ * exp (c * x)
  proof: by
  rw [le_inv_mul_iff₀ hc]
  calc c * x
  _ <= c * x + 1 := le_add_of_nonneg_right zero_le_one
  _ <= _ := Real.add_one_le_exp (c * x)

中文:
引理 le_inv_mul_exp
  条件: (x : 实数) {c : 实数} (hc : 0 < c)
  结论: x <= c⁻¹ * exp (c * x)
  证明: by
  rw [le_inv_mul_iff₀ hc]
  calc c * x
  _ <= c * x + 1 := le_add_of_nonneg_right zero_le_one
  _ <= _ := Real.add_one_le_exp (c * x)

Depends on / 依赖: Real.add_one_le_exp, add_one_le_exp, le_add_of_nonneg_right, zero_le_one
-/
lemma le_inv_mul_exp (x : Real) {c : Real} (hc : 0 < c) : x <= c⁻¹ * exp (c * x) := by
  rw [le_inv_mul_iff₀ hc]
  calc c * x
  _ <= c * x + 1 := le_add_of_nonneg_right zero_le_one
  _ <= _ := Real.add_one_le_exp (c * x)

/--
lemma `exp_lt_two_add_div_two_sub` / 引理 `exp_lt_two_add_div_two_sub`

English:
lemma exp_lt_two_add_div_two_sub
  given: {x : Real} (hx : 0 < x) (hx' : x < 2)
  proof: by calc
  _ = exp (x / 2) ^ 2 := by grind [Real.exp_nat_mul (x / 2) 2]
  _ <= _ := by
    grw [Real.exp_bound' (x := x / 2) (by grind) (by grind) (n := 3) (by simp)]
    apply Real.exp_nonneg
  _ < (2 + x) / (2 - x) := by
    rw [lt_div_iff₀ (by linarith)]; rw [← sub_pos]
    simp only [Finset.sum_r

中文:
引理 exp_lt_two_add_div_two_sub
  条件: {x : 实数} (hx : 0 < x) (hx' : x < 2)
  证明: by calc
  _ = exp (x / 2) ^ 2 := by grind [Real.exp_nat_mul (x / 2) 2]
  _ <= _ := by
    grw [Real.exp_bound' (x := x / 2) (by grind) (by grind) (n := 3) (by simp)]
    apply Real.exp_nonneg
  _ < (2 + x) / (2 - x) := by
    rw [lt_div_iff₀ (by linarith)]; rw [← sub_pos]
    simp only [Finset.sum_r

Depends on / 依赖: Finset, Finset.sum_range_succ, Real.exp_bound, Real.exp_nat_mul, Real.exp_nonneg, exp_bound, exp_nat_mul, exp_nonneg, ring_nf, sub_pos, sum_range_succ
-/
lemma exp_lt_two_add_div_two_sub {x : Real} (hx : 0 < x) (hx' : x < 2) :
    exp x < (2 + x) / (2 - x) := by calc
  _ = exp (x / 2) ^ 2 := by grind [Real.exp_nat_mul (x / 2) 2]
  _ <= _ := by
    grw [Real.exp_bound' (x := x / 2) (by grind) (by grind) (n := 3) (by simp)]
    apply Real.exp_nonneg
  _ < (2 + x) / (2 - x) := by
    rw [lt_div_iff₀ (by linarith)]; rw [← sub_pos]
    simp only [Finset.sum_range_succ]
    ring_nf
    positivity

/--
lemma `exp_le_two_add_div_two_sub` / 引理 `exp_le_two_add_div_two_sub`

English:
lemma exp_le_two_add_div_two_sub
  given: {x : Real} (hx : 0 <= x) (hx' : x < 2)
  proof: by
  obtain rfl | hx₀ := hx.eq_or_lt
  · simp
  · exact (exp_lt_two_add_div_two_sub hx₀ hx').le

中文:
引理 exp_le_two_add_div_two_sub
  条件: {x : 实数} (hx : 0 <= x) (hx' : x < 2)
  证明: by
  obtain rfl | hx₀ := hx.eq_or_lt
  · simp
  · exact (exp_lt_two_add_div_two_sub hx₀ hx').le

Depends on / 依赖: eq_or_lt, exp_lt_two_add_div_two_sub, hx.eq_or_lt
-/
lemma exp_le_two_add_div_two_sub {x : Real} (hx : 0 <= x) (hx' : x < 2) :
    exp x <= (2 + x) / (2 - x) := by
  obtain rfl | hx₀ := hx.eq_or_lt
  · simp
  · exact (exp_lt_two_add_div_two_sub hx₀ hx').le

/--
theorem `prod_one_add_le_exp_sum` / 定理 `prod_one_add_le_exp_sum`

English:
theorem prod_one_add_le_exp_sum
  statement: {ι : Type*} (s : Finset ι) {f : ι -> Real}
  proof: (Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one (hf i))
    fun i _ => (add_comm 1 (f i)).le.trans (add_one_le_exp _)).trans
    (exp_sum s f).symm.le

中文:
定理 prod_one_add_le_exp_sum
  结论: {ι : 类型} (s : 有限集 ι) {f : ι -> 实数}
  证明: (Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one (hf i))
    fun i _ => (add_comm 1 (f i)).le.trans (add_one_le_exp _)).trans
    (exp_sum s f).symm.le

Depends on / 依赖: Finset, Finset.prod_le_prod, add_comm, add_nonneg, add_one_le_exp, exp_sum, le.trans, prod_le_prod, symm.le, zero_le_one
-/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) {f : ι -> Real}
    (hf : forall i, 0 <= f i) : ∏ i in s, (1 + f i) <= exp (∑ i in s, f i) :=
  (Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one (hf i))
    fun i _ => (add_comm 1 (f i)).le.trans (add_one_le_exp _)).trans
    (exp_sum s f).symm.le

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.exp` is always positive. -/
@[positivity Real.exp _]
meta def evalExp : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.exp $a) =>
    assertInstancesCommute
    pure (.positive q(Real.exp_pos $a))
  | _, _, _ => throwError "not Real.exp"

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
/--
theorem `norm_exp_ofReal` / 定理 `norm_exp_ofReal`

English:
theorem norm_exp_ofReal
  given: (x : Real)
  statement: ‖exp x‖ = Real.exp x
  proof: by
  rw [← ofReal_exp]
  exact Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))

中文:
定理 norm_exp_of实数
  条件: (x : 实数)
  结论: ‖exp x‖ = 实数.exp x
  证明: by
  rw [← ofReal_exp]
  exact Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))

Depends on / 依赖: Complex.norm_of_nonneg, Real.exp_pos, exp_pos, le_of_lt, norm_of_nonneg, ofReal_exp
-/
theorem norm_exp_ofReal (x : Real) : ‖exp x‖ = Real.exp x := by
  rw [← ofReal_exp]
  exact Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))

end Complex
