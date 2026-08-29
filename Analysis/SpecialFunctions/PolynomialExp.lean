/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Limits of `P(x) / e ^ x` for a polynomial `P`

In this file we prove that $\lim_{x\to\infty}\frac{P(x)}{e^x}=0$ for any polynomial `P`.

## TODO

Add more similar lemmas: limit at `-∞`, versions with $e^{cx}$ etc.

## Keywords

polynomial, limit, exponential
-/

public section

open Filter Topology Real

namespace Polynomial

/--
theorem `tendsto_div_exp_atTop` / 定理 `tendsto_div_exp_atTop`

English:
theorem tendsto_div_exp_atTop
  given: (p : Real[X])
  statement: Tendsto (fun x => p.eval x / exp x) atTop (𝓝 0)
  proof: by
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa [exp_neg, div_eq_mul_inv, mul_assoc]
    using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  | add p q hp hq => simpa [add_div] using hp.add hq

中文:
定理 tendsto_div_exp_atTop
  条件: (p : 实数[X])
  结论: 收敛 (fun x => p.eval x / exp x) atTop (𝓝 0)
  证明: by
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa [exp_neg, div_eq_mul_inv, mul_assoc]
    using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  | add p q hp hq => simpa [add_div] using hp.add hq

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_div, div_eq_mul_inv, exp_neg, hp.add, induction_on, monomial, mul_assoc, tendsto_const_nhds, tendsto_const_nhds.mul, tendsto_pow_mul_exp_neg_atTop_nhds_zero
-/
theorem tendsto_div_exp_atTop (p : Real[X]) : Tendsto (fun x => p.eval x / exp x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c => simpa [exp_neg, div_eq_mul_inv, mul_assoc]
    using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  | add p q hp hq => simpa [add_div] using hp.add hq

end Polynomial
