/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne, Jireh Loreaux
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Real.ConjExponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
HM-GM inequality, Young's inequality, Hölder inequality, and Minkowski inequality. Versions for
integrals of some of these inequalities are available in
`Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `Real` namespace, and a version for
`NNReal`-valued functions is in the `NNReal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `Finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.


### HM-GM inequality:

The inequality says that the harmonic mean of a tuple of positive numbers is less than or equal
to their geometric mean. We prove the weighted version of this inequality: if $w$ and $z$
are two positive vectors and $\sum_{i\in s} w_i=1$, then
$$
1/(\sum_{i\in s} w_i/z_i) ≤ \prod_{i\in s} z_i^{w_i}
$$
The classical version is proven as a special case of this inequality for $w_i=\frac{1}{n}$.

The inequalities are proven only for real-valued positive functions on `Finset`s, and namespaced in
`Real`. The weighted version follows as a corollary of the weighted AM-GM inequality.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `Real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

public section


universe u v

open Finset NNReal ENNReal
open scoped BigOperators

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLEArithMean

/-! ### AM-GM inequality -/


namespace Real

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for real-valued nonnegative functions. -/
/-
**Real.geom_mean_le_arith_mean_weighted** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：geom_mean_le_arith_mean_weighted (w z : ι -> Real) (hw : forall i in s, 0 
<= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) : ∏ i in s, z i
 ^ w i <= ∑ i in s, w i * z i
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `convexOn_exp`：convexOn_exp : ConvexOn Real univ exp
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**AM-GM inequality**: The geometric mean is less than or equal to the arithmetic
 mean, weighted
version for real-valued nonnegative functions.
-/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases! A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
      exact zero_rpow hwi
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  · have := convexOn_exp.map_sum_le hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert! this using 1 <;> [apply prod_congr rfl; apply sum_congr rfl] <;> intro i hi
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · exact rpow_def_of_pos hz _
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · rw [exp_log hz]

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean. -/
/-
**Real.geom_mean_le_arith_mean** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι -> Real) (z : ι 
-> Real) (hw : forall i in s, 0 <= w i) (hw' : 0 < ∑ i in s, w i) (hz : forall i
 in s, 0 <= z i) : (∏ i in s, z i ^ w i) ^ (∑ i in s, w i)⁻¹ <= (∑ i in s, w i *
 z i) / (∑ i in s, w i)
参数：s : Finset ι；w : ι -> Real；z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : 0
 < ∑ i in s, w i；hz : forall i in s, 0 <= z i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.finsetProd_rpow`：∀ {ι : Type u_1} (s : Finset ι) (f : ι → ℝ), (∀ i 
∈ s, 0 ≤ f i) → ∀ (r : ℝ), ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighted 
(w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz :
 forall i in s, 0 <= z i) :…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
**AM-GM inequality**: The geometric mean is less than or equal to the arithmetic
 mean.
-/
theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / (∑ i ∈ s, w i) := by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i ∈ s, w i) z ?_ ?_ hz
  · rw [← finsetProd_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv, rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc, ← Finset.sum_mul, mul_comm]
  · exact fun _ hi => div_nonneg (hw _ hi) (le_of_lt hw')
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (by linarith)
/-
**Real.geom_mean_weighted_of_constant** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：geom_mean_weighted_of_constant (w z : ι -> Real) (x : Real) (hw : forall i
 in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) (hx : 
forall i in s, w i != 0 -> z i = x) : ∏ i in s, z i ^ w i = x
参数：w z : ι -> Real；x : Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1
；hz : forall i in s, 0 <= z i；hx : forall i in s, w i != 0 -> z i = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_sum_of_nonneg`：rpow_sum_of_nonneg {ι : Type*} {a : Real} (ha :
 0 <= a) {s : Finset ι} {f : ι -> Real} (h : forall x in s, 0 <= f x) : (a ^ ∑ x
 in s, f x) =…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
theorem geom_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i ∈ s, z i ^ w i = x :=
  calc
    ∏ i ∈ s, z i ^ w i = ∏ i ∈ s, x ^ w i := by
      refine prod_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with h₀ | h₀
      · rw [h₀, rpow_zero, rpow_zero]
      · rw [hx i hi h₀]
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw, hw', rpow_one]
      have : (∑ i ∈ s, w i) ≠ 0 := by
        rw [hw']
        exact one_ne_zero
      obtain ⟨i, his, hi⟩ := exists_ne_zero_of_sum_ne_zero this
      rw [← hx i his hi]
      exact hz i his
/-
**Real.arith_mean_weighted_of_constant** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arith_mean_weighted_of_constant (w z : ι -> Real) (x : Real) (hw' : ∑ i in
 s, w i = 1) (hx : forall i in s, w i != 0 -> z i = x) : ∑ i in s, w i * z i = x
参数：w z : ι -> Real；x : Real；hw' : ∑ i in s, w i = 1；hx : forall i in s, w i != 0
 -> z i = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) : ∑ i ∈ s, w i * z i = x :=
  calc
    ∑ i ∈ s, w i * z i = ∑ i ∈ s, w i * x := by
      refine sum_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with hwi | hwi
      · rw [hwi, zero_mul, zero_mul]
      · rw [hx i hi hwi]
    _ = x := by rw [← sum_mul, hw', one_mul]
/-
**Real.geom_mean_eq_arith_mean_weighted_of_constant** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：geom_mean_eq_arith_mean_weighted_of_constant (w z : ι -> Real) (x : Real) 
(hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 
<= z i) (hx : forall i in s, w i != 0 -> z i = x) : ∏ i in s, z i ^ w i = ∑ i in
 s, w i * z i
参数：w z : ι -> Real；x : Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1
；hz : forall i in s, 0 <= z i；hx : forall i in s, w i != 0 -> z i = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.geom_mean_weighted_of_constant`：geom_mean_weighted_of_constant (w z
 : ι -> Real) (x : Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1
) (hz : forall i in s, 0 …
· 使用定理 `Real.arith_mean_weighted_of_constant`：arith_mean_weighted_of_constant (w
 z : ι -> Real) (x : Real) (hw' : ∑ i in s, w i = 1) (hx : forall i in s, w i !=
 0 -> z i = x) : ∑ i in s,…
-/
theorem geom_mean_eq_arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i := by
  rw [geom_mean_weighted_of_constant, arith_mean_weighted_of_constant] <;> assumption

/-- **AM-GM inequality - equality condition**: This theorem provides the equality condition for the
*positive* weighted version of the AM-GM inequality for real-valued nonnegative functions.

The condition is that all elements of `z` are equal to their center of mass `∑ i ∈ s, w i * z i`;
see `geom_mean_eq_arith_mean_weighted_iff_of_pos` for a version that compares the elements to each
other instead. -/
/-
**Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：geom_mean_eq_arith_mean_weighted_iff_of_pos' (w z : ι -> Real) (hw : foral
l i in s, 0 < w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) : ∏ 
i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, z j = ∑ i in s, w i * z
 i
参数：w z : ι -> Real；hw : forall i in s, 0 < w i；hw' : ∑ i in s, w i = 1；hz : fora
ll i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_zero_of_ne_zero_of_mul_left_eq_zero`：eq_zero_of_ne_zero_of_mul_left_e
q_zero (hx : x != 0) (hxy : x * y = 0) : y = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_nonneg_iff_of_pos_left`：mul_nonneg_iff_of_pos_left [PosMulStrictMono
 R] (h : 0 < c) : 0 <= c * b ↔ 0 <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `StrictConvexOn.map_sum_eq_iff`：StrictConvexOn.map_sum_eq_iff {w : ι -> 𝕜
} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑
 i in t, w i = 1) (…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `strictConvexOn_exp`：strictConvexOn_exp : StrictConvexOn Real univ exp
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.congr`：∀ {α : Sort u_1} {x₁ y₁ x₂ y₂ : α}, x₁ = y₁ → x₂ = y₂ → (x₁ = 
x₂ ↔ y₁ = y₂)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
**AM-GM inequality - equality condition**: This theorem provides the equality co
ndition for the
*positive* weighted version of the AM-GM inequality for real-valued nonnegative 
functions.

The condition is that all elements of `z` are equal to their center of mass `∑ i
 ∈ s, w i * z i`;
see `geom_mean_eq_arith_mean_weighted_iff_of_pos` for a version that compares th
e elements to each
other instead.
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_pos' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, z j = ∑ i ∈ s, w i * z i := by
  by_cases! A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · constructor
      · intro h
        rw [← h]
        intro j hj
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
        apply (sum_eq_zero_iff_of_nonneg ?_).mp h.symm j hj
        exact fun i hi => (mul_nonneg_iff_of_pos_left (hw i hi)).mpr (hz i hi)
      · intro h
        convert! h i his
        exact hzi.symm
    · rw [hzi]
      exact zero_rpow hwi
  · have hz' := fun i h => lt_of_le_of_ne (hz i h) (fun a => (ne_of_gt (hw i h)) (A i h a.symm))
    have := strictConvexOn_exp.map_sum_eq_iff hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert! this using 1
    · apply Eq.congr <;>
      [apply prod_congr rfl; apply sum_congr rfl] <;>
      intro i hi <;>
      simp only [exp_mul, exp_log (hz' i hi)]
    · constructor <;> intro h j hj
      · rw [← arith_mean_weighted_of_constant s w _ (log (z j)) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [mul_comm, h j hj, h x hx]
      · rw [← arith_mean_weighted_of_constant s w _ (z j) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [log_injOn_pos (hz' j hj) (hz' x hx), h j hj, h x hx]

@[deprecated (since := "2026-06-07")]
alias geom_mean_eq_arith_mean_weighted_iff' := geom_mean_eq_arith_mean_weighted_iff_of_pos'

/-- **AM-GM inequality - equality condition**: This theorem provides the equality condition for the
weighted version of the AM-GM inequality for real-valued nonnegative functions.

The condition is that all elements of `z` with a nonzero weight are equal to their center of mass
`∑ i ∈ s, w i * z i`; see `geom_mean_eq_arith_mean_weighted_iff_of_nonneg` for a version that
compares the elements to each other instead. -/
/-
**Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间
 `Real`。
形式化陈述：geom_mean_eq_arith_mean_weighted_iff_of_nonneg' (w z : ι -> Real) (hw : fo
rall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) 
: ∏ i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, w j != 0 -> z j = ∑
 i in s, w i * z i
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'`：geom_mean_eq_arith_me
an_weighted_iff_of_pos' (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑
 i in s, w i = 1) (hz : forall i in s, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
**AM-GM inequality - equality condition**: This theorem provides the equality co
ndition for the
weighted version of the AM-GM inequality for real-valued nonnegative functions.

The condition is that all elements of `z` with a nonzero weight are equal to the
ir center of mass
`∑ i ∈ s, w i * z i`; see `geom_mean_eq_arith_mean_weighted_iff_of_nonneg` for a
 version that
compares the elements to each other instead.
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_nonneg' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, w j ≠ 0 → z j = ∑ i ∈ s, w i * z i := by
  have :
      ∏ i ∈ s with w i ≠ 0, z i ^ w i = ∑ i ∈ s with w i ≠ 0, w i * z i ↔
        ∀ j ∈ {x ∈ s | w x ≠ 0}, z j = ∑ i ∈ s with w i ≠ 0, w i * z i :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

@[deprecated (since := "2026-06-07")]
alias geom_mean_eq_arith_mean_weighted_iff := geom_mean_eq_arith_mean_weighted_iff_of_nonneg'

/-- **AM-GM inequality - equality condition**.
The condition is that all elements of `z` are equal to each other;
see `geom_mean_eq_arith_mean_weighted_iff_of_pos'` for a version that compares the elements to their
center of mass `∑ i ∈ s, w i * z i` instead. -/
/-
**Real.geom_mean_eq_arith_mean_weighted_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Re
al`。
形式化陈述：geom_mean_eq_arith_mean_weighted_iff_of_pos (w z : ι -> Real) (hw : forall
 i in s, 0 < w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) : ∏ i
 in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, forall k in s, z j = z k
参数：w z : ι -> Real；hw : forall i in s, 0 < w i；hw' : ∑ i in s, w i = 1；hz : fora
ll i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_sum_of_nonneg`：rpow_sum_of_nonneg {ι : Type*} {a : Real} (ha :
 0 <= a) {s : Finset ι} {f : ι -> Real} (h : forall x in s, 0 <= f x) : (a ^ ∑ x
 in s, f x) =…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
**AM-GM inequality - equality condition**.
The condition is that all elements of `z` are equal to each other;
see `geom_mean_eq_arith_mean_weighted_iff_of_pos'` for a version that compares t
he elements to their
center of mass `∑ i ∈ s, w i * z i` instead.
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_pos (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  refine ⟨by grind [geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz], fun h ↦ ?_⟩
  have ⟨k, hk⟩ : s.Nonempty := by grind [s.eq_empty_or_nonempty]
  suffices ∏ i ∈ s, z k ^ w i = ∑ i ∈ s, w i * z k by convert this using 3 <;> grind
  rw [← rpow_sum_of_nonneg (hz k hk) (hw · · |>.le), ← sum_mul, hw', rpow_one, one_mul]

/-- **AM-GM inequality - equality condition**.
The condition is that all elements of `z` with a nonzero weight are equal to each other;
see `geom_mean_eq_arith_mean_weighted_iff_of_nonneg'` for a version that compares the elements to
their center of mass `∑ i ∈ s, w i * z i` instead. -/
/-
**Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 
`Real`。
形式化陈述：geom_mean_eq_arith_mean_weighted_iff_of_nonneg (w z : ι -> Real) (hw : for
all i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
 ∏ i in s, z i ^ w i = ∑ i in s, w i * z i ↔ forall j in s, w j != 0 -> forall k
 in s, w k != 0 -> z j = z k
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`：geom_mean_eq_arith_mea
n_weighted_iff_of_pos (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑ i
 in s, w i = 1) (hz : forall i in s, 0…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
**AM-GM inequality - equality condition**.
The condition is that all elements of `z` with a nonzero weight are equal to eac
h other;
see `geom_mean_eq_arith_mean_weighted_iff_of_nonneg'` for a version that compare
s the elements to
their center of mass `∑ i ∈ s, w i * z i` instead.
-/
theorem geom_mean_eq_arith_mean_weighted_iff_of_nonneg (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, w j ≠ 0 → ∀ k ∈ s, w k ≠ 0 → z j = z k := by
  have :
      ∏ i ∈ s with w i ≠ 0, z i ^ w i = ∑ i ∈ s with w i ≠ 0, w i * z i ↔
        ∀ j ∈ {x ∈ s | w x ≠ 0}, ∀ k ∈ {x ∈ s | w x ≠ 0}, z j = z k :=
    geom_mean_eq_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

/-- **AM-GM inequality - strict inequality condition**.
The condition is that not all elements of `z` are equal to their center of mass
`∑ i ∈ s, w i * z i`; see `geom_mean_lt_arith_mean_weighted_iff_of_pos` for a version that compares
the elements to each other instead. -/
/-
**Real.geom_mean_lt_arith_mean_weighted_iff_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：geom_mean_lt_arith_mean_weighted_iff_of_pos' (w z : ι -> Real) (hw : foral
l i in s, 0 < w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) : ∏ 
i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, z j != ∑ i in s, w i * 
z i
参数：w z : ι -> Real；hw : forall i in s, 0 < w i；hw' : ∑ i in s, w i = 1；hz : fora
ll i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'`：geom_mean_eq_arith_me
an_weighted_iff_of_pos' (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑
 i in s, w i = 1) (hz : forall i in s, …
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `Real.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighted 
(w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz :
 forall i in s, 0 <= z i) :…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
**AM-GM inequality - strict inequality condition**.
The condition is that not all elements of `z` are equal to their center of mass
`∑ i ∈ s, w i * z i`; see `geom_mean_lt_arith_mean_weighted_iff_of_pos` for a ve
rsion that compares
the elements to each other instead.
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, z j ≠ ∑ i ∈ s, w i * z i := by
  contrapose!
  rw [← geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz]
  exact geom_mean_le_arith_mean_weighted s w z (hw · · |>.le) hw' hz |>.ge_iff_eq

/-- **AM-GM inequality - strict inequality condition**.
The condition is that not all elements of `z` with a nonzero weight are equal to their center of
mass `∑ i ∈ s, w i * z i`; see `geom_mean_lt_arith_mean_weighted_iff_of_nonneg` for a version that
compares the elements to each other instead. -/
/-
**Real.geom_mean_lt_arith_mean_weighted_iff_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间
 `Real`。
形式化陈述：geom_mean_lt_arith_mean_weighted_iff_of_nonneg' (w z : ι -> Real) (hw : fo
rall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) 
: ∏ i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, w j != 0 ∧ z j != ∑
 i in s, w i * z i
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_lt_arith_mean_weighted_iff_of_pos'`：geom_mean_lt_arith_me
an_weighted_iff_of_pos' (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑
 i in s, w i = 1) (hz : forall i in s, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
**AM-GM inequality - strict inequality condition**.
The condition is that not all elements of `z` with a nonzero weight are equal to
 their center of
mass `∑ i ∈ s, w i * z i`; see `geom_mean_lt_arith_mean_weighted_iff_of_nonneg` 
for a version that
compares the elements to each other instead.
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_nonneg' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, w j ≠ 0 ∧ z j ≠ ∑ i ∈ s, w i * z i := by
  have :
      ∏ i ∈ s with w i ≠ 0, z i ^ w i < ∑ i ∈ s with w i ≠ 0, w i * z i ↔
        ∃ j ∈ {x ∈ s | w x ≠ 0}, z j ≠ ∑ i ∈ s with w i ≠ 0, w i * z i :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos' _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

/-- **AM-GM inequality - strict inequality condition**: This theorem provides the strict inequality
condition for the *positive* weighted version of the AM-GM inequality for real-valued nonnegative
functions.

The condition is that not all elements of `z` are equal to each other;
see `geom_mean_lt_arith_mean_weighted_iff_of_pos'` for a version that compares the elements to their
center of mass `∑ i ∈ s, w i * z i` instead. -/
/-
**Real.geom_mean_lt_arith_mean_weighted_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Re
al`。
形式化陈述：geom_mean_lt_arith_mean_weighted_iff_of_pos (w z : ι -> Real) (hw : forall
 i in s, 0 < w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) : ∏ i
 in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, exists k in s, z j != z 
k
参数：w z : ι -> Real；hw : forall i in s, 0 < w i；hw' : ∑ i in s, w i = 1；hz : fora
ll i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'`：geom_mean_eq_arith_me
an_weighted_iff_of_pos' (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑
 i in s, w i = 1) (hz : forall i in s, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.arith_mean_weighted_of_constant`：arith_mean_weighted_of_constant (w
 z : ι -> Real) (x : Real) (hw' : ∑ i in s, w i = 1) (hx : forall i in s, w i !=
 0 -> z i = x) : ∑ i in s,…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighted 
(w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz :
 forall i in s, 0 <= z i) :…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
**AM-GM inequality - strict inequality condition**: This theorem provides the st
rict inequality
condition for the *positive* weighted version of the AM-GM inequality for real-v
alued nonnegative
functions.

The condition is that not all elements of `z` are equal to each other;
see `geom_mean_lt_arith_mean_weighted_iff_of_pos'` for a version that compares t
he elements to their
center of mass `∑ i ∈ s, w i * z i` instead.
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k := by
  constructor
  · intro h
    by_contra! h_contra
    rw [(geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz).mpr ?_] at h
    · exact (lt_self_iff_false _).mp h
    · intro j hjs
      rw [← arith_mean_weighted_of_constant s w (fun _ => z j) (z j) hw' fun _ _ => congrFun rfl]
      apply sum_congr rfl (fun x a => congrArg (HMul.hMul (w x)) (h_contra j hjs x a))
  · rintro ⟨j, hjs, k, hks, hzjk⟩
    have := geom_mean_le_arith_mean_weighted s w z (fun i a => le_of_lt (hw i a)) hw' hz
    by_contra! h
    apply le_antisymm this at h
    apply (geom_mean_eq_arith_mean_weighted_iff_of_pos' s w z hw hw' hz).mp at h
    simp only [h j hjs, h k hks, ne_eq, not_true_eq_false] at hzjk

/-- **AM-GM inequality - strict inequality condition**.
The condition is that not all elements of `z` with a nonzero weight are equal to each other;
see `geom_mean_lt_arith_mean_weighted_iff_of_nonneg'` for a version that compares the elements to
their center of mass `∑ i ∈ s, w i * z i` instead. -/
/-
**Real.geom_mean_lt_arith_mean_weighted_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 
`Real`。
形式化陈述：geom_mean_lt_arith_mean_weighted_iff_of_nonneg (w z : ι -> Real) (hw : for
all i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) :
 ∏ i in s, z i ^ w i < ∑ i in s, w i * z i ↔ exists j in s, exists k in s, w j !
= 0 ∧ w k != 0 ∧ z j != z k
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_lt_arith_mean_weighted_iff_of_pos`：geom_mean_lt_arith_mea
n_weighted_iff_of_pos (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑ i
 in s, w i = 1) (hz : forall i in s, 0…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
**AM-GM inequality - strict inequality condition**.
The condition is that not all elements of `z` with a nonzero weight are equal to
 each other;
see `geom_mean_lt_arith_mean_weighted_iff_of_nonneg'` for a version that compare
s the elements to
their center of mass `∑ i ∈ s, w i * z i` instead.
-/
theorem geom_mean_lt_arith_mean_weighted_iff_of_nonneg (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, ∃ k ∈ s, w j ≠ 0 ∧ w k ≠ 0 ∧ z j ≠ z k := by
  have :
      ∏ i ∈ s with w i ≠ 0, z i ^ w i < ∑ i ∈ s with w i ≠ 0, w i * z i ↔
        ∃ j ∈ {x ∈ s | w x ≠ 0}, ∃ k ∈ {x ∈ s | w x ≠ 0}, z j ≠ z k :=
    geom_mean_lt_arith_mean_weighted_iff_of_pos _ w z (by grind)
      (sum_filter_ne_zero _ |>.trans hw') (hz _ <| mem_of_mem_filter · ·)
  grind [prod_filter_of_ne, sum_filter_of_ne, rpow_zero]

end Real

namespace NNReal

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for `NNReal`-valued functions. -/
/-
**NNReal.geom_mean_le_arith_mean_weighted** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：geom_mean_le_arith_mean_weighted (w z : ι -> Real>=0) (hw' : ∑ i in s, w i
 = 1) : (∏ i in s, z i ^ (w i : Real)) <= ∑ i in s, w i * z i
参数：w z : ι -> Real>=0；hw' : ∑ i in s, w i = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighted 
(w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz :
 forall i in s, 0 <= z i) :…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
**AM-GM inequality**: The geometric mean is less than or equal to the arithmetic
 mean, weighted
version for `NNReal`-valued functions.
-/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) :
    (∏ i ∈ s, z i ^ (w i : ℝ)) ≤ ∑ i ∈ s, w i * z i :=
  mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for two `NNReal` numbers. -/
/-
**NNReal.geom_mean_le_arith_mean2_weighted** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : Real>=0) : w₁ + w₂ = 1 ->
 p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real) <= w₁ * p₁ + w₂ * p₂
参数：w₁ w₂ p₁ p₂ : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NNReal.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighte
d (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) : (∏ i in s, z i ^ (w i : Real)
) <= ∑ i in s, w i * z i

--- 原说明 ---
**AM-GM inequality**: The geometric mean is less than or equal to the arithmetic
 mean, weighted
version for two `NNReal` numbers.
-/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
    w₁ + w₂ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using!
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]
/-
**NNReal.geom_mean_le_arith_mean3_weighted** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : Real>=0) : w₁ + w₂ 
+ w₃ = 1 -> p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real) * p₃ ^ (w₃ : Real) <= w₁ * p₁ + 
w₂ * p₂ + w₃ * p₃
参数：w₁ w₂ w₃ p₁ p₂ p₃ : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NNReal.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighte
d (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) : (∏ i in s, z i ^ (w i : Real)
) <= ∑ i in s, w i * z i
-/
theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
    w₁ + w₂ + w₃ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]
/-
**NNReal.geom_mean_le_arith_mean4_weighted** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real>=0) : w₁
 + w₂ + w₃ + w₄ = 1 -> p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real) * p₃ ^ (w₃ : Real) * 
p₄ ^ (w₄ : Real) <= w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄
参数：w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NNReal.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighte
d (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) : (∏ i in s, z i ^ (w i : Real)
) <= ∑ i in s, w i * z i
-/
theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
    w₁ + w₂ + w₃ + w₄ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) * p₄ ^ (w₄ : ℝ) ≤
        w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using! geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

end NNReal

namespace Real

/-
**Real.geom_mean_le_arith_mean2_weighted** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁) (hw
₂ : 0 <= w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^
 w₂ <= w₁ * p₁ + w₂ * p₂
参数：hw₁ : 0 <= w₁；hw₂ : 0 <= w₂；hp₁ : 0 <= p₁；hp₂ : 0 <= p₂；hw : w₁ + w₂ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.geom_mean_le_arith_mean2_weighted`：geom_mean_le_arith_mean2_weigh
ted (w₁ w₂ p₁ p₂ : Real>=0) : w₁ + w₂ = 1 -> p₁ ^ (w₁ : Real) * p₂ ^ (w₂ : Real)
 <= w₁ * p₁ + w₂ * p₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
-/
theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ <|
    NNReal.coe_inj.1 <| by assumption
/-
**Real.geom_mean_le_arith_mean3_weighted** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : Real} (hw₁ : 0 <= w
₁) (hw₂ : 0 <= w₂) (hw₃ : 0 <= w₃) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hp₃ : 0 <= p
₃) (hw : w₁ + w₂ + w₃ = 1) : p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ <= w₁ * p₁ + w₂ * p₂ + 
w₃ * p₃
参数：hw₁ : 0 <= w₁；hw₂ : 0 <= w₂；hw₃ : 0 <= w₃；hp₁ : 0 <= p₁；hp₂ : 0 <= p₂；hp₃ : 0
 <= p₃；hw : w₁ + w₂ + w₃ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.geom_mean_le_arith_mean3_weighted`：geom_mean_le_arith_mean3_weigh
ted (w₁ w₂ w₃ p₁ p₂ p₃ : Real>=0) : w₁ + w₂ + w₃ = 1 -> p₁ ^ (w₁ : Real) * p₂ ^ 
(w₂ : Real) * p₃ ^ (w₃ : Real)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
-/
theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      ⟨p₃, hp₃⟩ <|
    NNReal.coe_inj.1 hw
/-
**Real.geom_mean_le_arith_mean4_weighted** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real} (hw₁ : 
0 <= w₁) (hw₂ : 0 <= w₂) (hw₃ : 0 <= w₃) (hw₄ : 0 <= w₄) (hp₁ : 0 <= p₁) (hp₂ : 
0 <= p₂) (hp₃ : 0 <= p₃) (hp₄ : 0 <= p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) : p₁ ^ w₁ 
* p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ <= w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄
参数：hw₁ : 0 <= w₁；hw₂ : 0 <= w₂；hw₃ : 0 <= w₃；hw₄ : 0 <= w₄；hp₁ : 0 <= p₁；hp₂ : 0
 <= p₂；hp₃ : 0 <= p₃；hp₄ : 0 <= p₄；hw : w₁ + w₂ + w₃ + w₄ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.geom_mean_le_arith_mean4_weighted`：geom_mean_le_arith_mean4_weigh
ted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : Real>=0) : w₁ + w₂ + w₃ + w₄ = 1 -> p₁ ^ (w₁ : Re
al) * p₂ ^ (w₂ : Real) * p₃ ^ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
-/
theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
      ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ <|
    NNReal.coe_inj.1 <| by assumption
/-
**Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：geom_mean_eq_arith_mean2_weighted_iff_of_pos {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0
 < w₁) (hw₂ : 0 < w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) : p₁ ^ 
w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ p₁ = p₂
参数：hw₁ : 0 < w₁；hw₂ : 0 < w₂；hp₁ : 0 <= p₁；hp₂ : 0 <= p₂；hw : w₁ + w₂ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`：geom_mean_eq_arith_mea
n_weighted_iff_of_pos (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑ i
 in s, w i = 1) (hz : forall i in s, 0…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem geom_mean_eq_arith_mean2_weighted_iff_of_pos {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ p₁ = p₂ := by
  have := geom_mean_eq_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind
/-
**Real.geom_mean_eq_arith_mean2_weighted_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 `Real`。
形式化陈述：geom_mean_eq_arith_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : Real} (hw₁ 
: 0 <= w₁) (hw₂ : 0 <= w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) : 
p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ w₁ = 0 ∨ w₂ = 0 ∨ p₁ = p₂
参数：hw₁ : 0 <= w₁；hw₂ : 0 <= w₂；hp₁ : 0 <= p₁；hp₂ : 0 <= p₂；hw : w₁ + w₂ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg`：geom_mean_eq_arith_
mean_weighted_iff_of_nonneg (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw
' : ∑ i in s, w i = 1) (hz : forall i in …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem geom_mean_eq_arith_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ w₁ = 0 ∨ w₂ = 0 ∨ p₁ = p₂ := by
  have := geom_mean_eq_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind
/-
**Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：geom_mean_lt_arith_mean2_weighted_iff_of_pos {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0
 < w₁) (hw₂ : 0 < w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) : p₁ ^ 
w₁ * p₂ ^ w₂ < w₁ * p₁ + w₂ * p₂ ↔ p₁ != p₂
参数：hw₁ : 0 < w₁；hw₂ : 0 < w₂；hp₁ : 0 <= p₁；hp₂ : 0 <= p₂；hw : w₁ + w₂ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_lt_arith_mean_weighted_iff_of_pos`：geom_mean_lt_arith_mea
n_weighted_iff_of_pos (w z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : ∑ i
 in s, w i = 1) (hz : forall i in s, 0…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem geom_mean_lt_arith_mean2_weighted_iff_of_pos {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ < w₁ * p₁ + w₂ * p₂ ↔ p₁ ≠ p₂ := by
  have := geom_mean_lt_arith_mean_weighted_iff_of_pos univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind
/-
**Real.geom_mean_lt_arith_mean2_weighted_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 `Real`。
形式化陈述：geom_mean_lt_arith_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : Real} (hw₁ 
: 0 <= w₁) (hw₂ : 0 <= w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w₁ + w₂ = 1) : 
p₁ ^ w₁ * p₂ ^ w₂ < w₁ * p₁ + w₂ * p₂ ↔ w₁ != 0 ∧ w₂ != 0 ∧ p₁ != p₂
参数：hw₁ : 0 <= w₁；hw₂ : 0 <= w₂；hp₁ : 0 <= p₁；hp₂ : 0 <= p₂；hw : w₁ + w₂ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_lt_arith_mean_weighted_iff_of_nonneg`：geom_mean_lt_arith_
mean_weighted_iff_of_nonneg (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw
' : ∑ i in s, w i = 1) (hz : forall i in …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem geom_mean_lt_arith_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ < w₁ * p₁ + w₂ * p₂ ↔ w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ p₁ ≠ p₂ := by
  have := geom_mean_lt_arith_mean_weighted_iff_of_nonneg univ ![w₁, w₂] ![p₁, p₂]
  simp at this
  grind

end Real

end GeomMeanLEArithMean

section HarmMeanLEGeomMean

/-! ### HM-GM inequality -/

namespace Real

/-- **HM-GM inequality**: The harmonic mean is less than or equal to the geometric mean, weighted
version for real-valued nonnegative functions. -/
/-
**Real.harm_mean_le_geom_mean_weighted** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：harm_mean_le_geom_mean_weighted (w z : ι -> Real) (hs : s.Nonempty) (hw : 
forall i in s, 0 < w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 < z i) 
: (∑ i in s, w i / z i)⁻¹ <= ∏ i in s, z i ^ w i
参数：w z : ι -> Real；hs : s.Nonempty；hw : forall i in s, 0 < w i；hw' : ∑ i in s, w
 i = 1；hz : forall i in s, 0 < z i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.geom_mean_le_arith_mean_weighted`：geom_mean_le_arith_mean_weighted 
(w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz :
 forall i in s, 0 <= z i) :…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_nonneg`：one_div_nonneg : 0 <= 1 / a ↔ 0 <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**HM-GM inequality**: The harmonic mean is less than or equal to the geometric m
ean, weighted
version for real-valued nonnegative functions.
-/
theorem harm_mean_le_geom_mean_weighted (w z : ι → ℝ) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i / z i)⁻¹ ≤ ∏ i ∈ s, z i ^ w i := by
  have : ∏ i ∈ s, (1 / z) i ^ w i ≤ ∑ i ∈ s, w i * (1 / z) i :=
    geom_mean_le_arith_mean_weighted s w (1 / z) (fun i hi ↦ le_of_lt (hw i hi)) hw'
    (fun i hi ↦ one_div_nonneg.2 (le_of_lt (hz i hi)))
  have p_pos : 0 < ∏ i ∈ s, (z i)⁻¹ ^ w i :=
    prod_pos fun i hi => rpow_pos_of_pos (inv_pos.2 (hz i hi)) _
  have s_pos : 0 < ∑ i ∈ s, w i * (z i)⁻¹ :=
    sum_pos (fun i hi => mul_pos (hw i hi) (inv_pos.2 (hz i hi))) hs
  simp only [Pi.div_apply, Pi.one_apply, one_div, ← inv_le_inv₀ s_pos p_pos] at this
  apply le_trans this
  have p_pos₂ : 0 < (∏ i ∈ s, (z i) ^ w i)⁻¹ :=
    inv_pos.2 (prod_pos fun i hi => rpow_pos_of_pos ((hz i hi)) _)
  rw [← inv_inv (∏ i ∈ s, z i ^ w i), inv_le_inv₀ p_pos p_pos₂, ← Finset.prod_inv_distrib]
  gcongr
  · exact fun i hi ↦ by positivity [hz i hi]
  · rw [Real.inv_rpow]; apply fun i hi ↦ le_of_lt (hz i hi); assumption


/-- **HM-GM inequality**: The harmonic mean is less than or equal to the geometric mean. -/
/-
**Real.harm_mean_le_geom_mean** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：harm_mean_le_geom_mean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι
 -> Real) (z : ι -> Real) (hw : forall i in s, 0 < w i) (hw' : 0 < ∑ i in s, w i
) (hz : forall i in s, 0 < z i) : (∑ i in s, w i) / (∑ i in s, w i / z i) <= (∏ 
i in s, z i ^ w i) ^ (∑ i in s, w i)⁻¹
参数：s : Finset ι；hs : s.Nonempty；w : ι -> Real；z : ι -> Real；hw : forall i in s, 
0 < w i；hw' : 0 < ∑ i in s, w i；hz : forall i in s, 0 < z i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.harm_mean_le_geom_mean_weighted`：harm_mean_le_geom_mean_weighted (w
 z : ι -> Real) (hs : s.Nonempty) (hw : forall i in s, 0 < w i) (hw' : ∑ i in s,
 w i = 1) (hz : forall i i…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Real.finsetProd_rpow`：∀ {ι : Type u_1} (s : Finset ι) (f : ι → ℝ), (∀ i 
∈ s, 0 ≤ f i) → ∀ (r : ℝ), ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z

--- 原说明 ---
**HM-GM inequality**: The harmonic mean is less than or equal to the geometric m
ean.
-/
theorem harm_mean_le_geom_mean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i) / (∑ i ∈ s, w i / z i) ≤ (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ := by
  have := harm_mean_le_geom_mean_weighted s (fun i => (w i) / ∑ i ∈ s, w i) z hs ?_ ?_ hz
  · set n := ∑ i ∈ s, w i
    nth_rw 1 [div_eq_mul_inv, (show n = (n⁻¹)⁻¹ by simp), ← mul_inv, Finset.mul_sum _ _ n⁻¹]
    simp_rw [inv_mul_eq_div n ((w _) / (z _)), div_right_comm _ _ n]
    convert! this
    rw [← Real.finsetProd_rpow s _ (fun i hi ↦ by positivity [hz i hi])]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_mul (le_of_lt <| hz i hi) (w _) n⁻¹, div_eq_mul_inv (w _) n]
  · exact fun i hi ↦ div_pos (hw i hi) hw'
  · simp_rw [div_eq_mul_inv (w _) (∑ i ∈ s, w i), ← Finset.sum_mul _ _ (∑ i ∈ s, w i)⁻¹]
    exact mul_inv_cancel₀ hw'.ne'

end Real

end HarmMeanLEGeomMean


section Young

/-! ### Young's inequality -/


namespace Real

/-- **Young's inequality**, a version for nonnegative real numbers. -/
/-
**Real.young_inequality_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：young_inequality_of_nonneg {a b p q : Real} (ha : 0 <= a) (hb : 0 <= b) (h
pq : p.HolderConjugate q) : a * b <= a ^ p / p + b ^ q / q
参数：ha : 0 <= a；hb : 0 <= b；hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `Real.geom_mean_le_arith_mean2_weighted`：geom_mean_le_arith_mean2_weighte
d {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w₂) (hp₁ : 0 <= p₁) (hp₂ : 0 
<= p₂) (hw : w₁ + w₂ = 1) : …
· 使用定理 `Real.HolderTriple.inv_nonneg`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 ≤ p⁻
¹
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q⁻¹ 
= 1

--- 原说明 ---
**Young's inequality**, a version for nonnegative real numbers.
-/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) : a * b ≤ a ^ p / p + b ^ q / q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

/-- **Young's inequality**, a version for arbitrary real numbers. -/
/-
**Real.young_inequality** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：young_inequality (a b : Real) {p q : Real} (hpq : p.HolderConjugate q) : a
 * b <= |a| ^ p / p + |b| ^ q / q
参数：a b : Real；hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Real.young_inequality_of_nonneg`：young_inequality_of_nonneg {a b p q : R
eal} (ha : 0 <= a) (hb : 0 <= b) (hpq : p.HolderConjugate q) : a * b <= a ^ p / 
p + b ^ q / q
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
**Young's inequality**, a version for arbitrary real numbers.
-/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q :=
  calc
    a * b ≤ |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ ≤ |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

/-- **Young's inequality** equality condition for nonnegative real numbers. -/
/-
**Real.young_inequality_eq_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：young_inequality_eq_iff_of_nonneg {a b p q : Real} (ha : 0 <= a) (hb : 0 <
= b) (hpq : p.HolderConjugate q) : a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q
参数：ha : 0 <= a；hb : 0 <= b；hpq : p.HolderConjugate q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Real.geom_mean_eq_arith_mean2_weighted_iff_of_nonneg`：geom_mean_eq_arith
_mean2_weighted_iff_of_nonneg {w₁ w₂ p₁ p₂ : Real} (hw₁ : 0 <= w₁) (hw₂ : 0 <= w
₂) (hp₁ : 0 <= p₁) (hp₂ : 0 <= p₂) (hw : w…
· 使用定理 `Real.HolderTriple.inv_nonneg`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 ≤ p⁻
¹
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q⁻¹ 
= 1

--- 原说明 ---
**Young's inequality** equality condition for nonnegative real numbers.
-/
theorem young_inequality_eq_iff_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) : a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
    geom_mean_eq_arith_mean2_weighted_iff_of_nonneg hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

end Real

namespace NNReal

/-- **Young's inequality**, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators. -/
/-
**NNReal.young_inequality** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：young_inequality (a b : Real>=0) {p q : Real>=0} (hpq : p.HolderConjugate 
q) : a * b <= a ^ (p : Real) / p + b ^ (q : Real) / q
参数：a b : Real>=0；hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.young_inequality_of_nonneg`：young_inequality_of_nonneg {a b p q : R
eal} (ha : 0 <= a) (hb : 0 <= b) (hpq : p.HolderConjugate q) : a * b <= a ^ p / 
p + b ^ q / q
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `NNReal.HolderConjugate.coe`：∀ {p q : NNReal}, p.HolderConjugate q → (↑p)
.HolderConjugate ↑q

--- 原说明 ---
**Young's inequality**, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid co
nstructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.
-/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ (p : ℝ) / p + b ^ (q : ℝ) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

/-- **Young's inequality**, `ℝ≥0` version with real conjugate exponents. -/
/-
**NNReal.young_inequality_real** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：young_inequality_real (a b : Real>=0) {p q : Real} (hpq : p.HolderConjugat
e q) : a * b <= a ^ p / p.toNNReal + b ^ q / q.toNNReal
参数：a b : Real>=0；hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Real.HolderTriple.nonneg`：nonneg : 0 <= p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `NNReal.young_inequality`：young_inequality (a b : Real>=0) {p q : Real>=0
} (hpq : p.HolderConjugate q) : a * b <= a ^ (p : Real) / p + b ^ (q : Real) / q
· 使用定理 `Real.HolderConjugate.toNNReal`：∀ {p q : ℝ}, p.HolderConjugate q → p.toNN
Real.HolderConjugate q.toNNReal

--- 原说明 ---
**Young's inequality**, `ℝ≥0` version with real conjugate exponents.
-/
theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / p.toNNReal + b ^ q / q.toNNReal := by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality a b hpq.toNNReal

/-- **Young's inequality** equality condition, `ℝ≥0` version. -/
/-
**NNReal.young_inequality_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：young_inequality_eq_iff (a b : Real>=0) {p q : Real>=0} (hpq : p.HolderCon
jugate q) : a * b = a ^ (p : Real) / p + b ^ (q : Real) / q ↔ a ^ (p : Real) = b
 ^ (q : Real)
参数：a b : Real>=0；hpq : p.HolderConjugate q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.young_inequality_eq_iff_of_nonneg`：young_inequality_eq_iff_of_nonne
g {a b p q : Real} (ha : 0 <= a) (hb : 0 <= b) (hpq : p.HolderConjugate q) : a *
 b = a ^ p / p + b ^ q / q ↔…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `NNReal.HolderConjugate.coe`：∀ {p q : NNReal}, p.HolderConjugate q → (↑p)
.HolderConjugate ↑q

--- 原说明 ---
**Young's inequality** equality condition, `ℝ≥0` version.
-/
theorem young_inequality_eq_iff (a b : ℝ≥0) {p q : ℝ≥0} (hpq : p.HolderConjugate q) :
    a * b = a ^ (p : ℝ) / p + b ^ (q : ℝ) / q ↔ a ^ (p : ℝ) = b ^ (q : ℝ) :=
  mod_cast Real.young_inequality_eq_iff_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

/-- **Young's inequality** equality condition, `ℝ≥0` version with real conjugate exponents. -/
/-
**NNReal.young_inequality_real_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：young_inequality_real_eq_iff (a b : Real>=0) {p q : Real} (hpq : p.HolderC
onjugate q) : a * b = a ^ p / p.toNNReal + b ^ q / q.toNNReal ↔ a ^ p = b ^ q
参数：a b : Real>=0；hpq : p.HolderConjugate q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Real.HolderTriple.nonneg`：nonneg : 0 <= p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `NNReal.young_inequality_eq_iff`：young_inequality_eq_iff (a b : Real>=0) 
{p q : Real>=0} (hpq : p.HolderConjugate q) : a * b = a ^ (p : Real) / p + b ^ (
q : Real) / q ↔ a ^ …
· 使用定理 `Real.HolderConjugate.toNNReal`：∀ {p q : ℝ}, p.HolderConjugate q → p.toNN
Real.HolderConjugate q.toNNReal

--- 原说明 ---
**Young's inequality** equality condition, `ℝ≥0` version with real conjugate exp
onents.
-/
theorem young_inequality_real_eq_iff (a b : ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b = a ^ p / p.toNNReal + b ^ q / q.toNNReal ↔ a ^ p = b ^ q := by
  simpa [hpq.nonneg, hpq.symm.nonneg] using young_inequality_eq_iff a b hpq.toNNReal

end NNReal

namespace ENNReal

/-- **Young's inequality**, `ℝ≥0∞` version with real conjugate exponents. -/
/-
**ENNReal.young_inequality** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：young_inequality (a b : Real>=0∞) {p q : Real} (hpq : p.HolderConjugate q)
 : a * b <= a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q
参数：a b : Real>=0∞；hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `Real.HolderTriple.nonneg`：nonneg : 0 <= p
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `NNReal.young_inequality_real`：young_inequality_real (a b : Real>=0) {p q
 : Real} (hpq : p.HolderConjugate q) : a * b <= a ^ p / p.toNNReal + b ^ q / q.t
oNNReal

--- 原说明 ---
**Young's inequality**, `ℝ≥0∞` version with real conjugate exponents.
-/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q := by
  by_cases! h : a = ⊤ ∨ b = ⊤
  · refine le_trans le_top (le_of_eq ?_)
    repeat rw [div_eq_mul_inv]
    rcases h with h | h <;> rw [h] <;> simp [hpq.pos, hpq.symm.pos]
  -- if `a ≠ ⊤` and `b ≠ ⊤`, use the `NNReal` version: `NNReal.young_inequality_real`
  rw [← coe_toNNReal h.left, ← coe_toNNReal h.right, ← coe_mul, ← coe_rpow_of_nonneg _ hpq.nonneg,
    ← coe_rpow_of_nonneg _ hpq.symm.nonneg, ENNReal.ofReal, ENNReal.ofReal, ←
    @coe_div (Real.toNNReal p) _ (by simp [hpq.pos]), ←
    @coe_div (Real.toNNReal q) _ (by simp [hpq.symm.pos]), ← coe_add, coe_le_coe]
  exact NNReal.young_inequality_real a.toNNReal b.toNNReal hpq

/-- **Young's inequality** equality condition, `ℝ≥0∞` version with real conjugate exponents. -/
/-
**ENNReal.young_inequality_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：young_inequality_eq_iff (a b : Real>=0∞) {p q : Real} (hpq : p.HolderConju
gate q) : a * b = a ^ p / .ofReal p + b ^ q / .ofReal q ↔ (a = ⊤ ∧ b != 0) ∨ (a 
!= 0 ∧ b = ⊤) ∨ a ^ p = b ^ q
参数：a b : Real>=0∞；hpq : p.HolderConjugate q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
**Young's inequality** equality condition, `ℝ≥0∞` version with real conjugate ex
ponents.
-/
theorem young_inequality_eq_iff (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b = a ^ p / .ofReal p + b ^ q / .ofReal q ↔
      (a = ⊤ ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = ⊤) ∨ a ^ p = b ^ q := by
  by_cases! h0 : a = 0 ∨ b = 0
  · rcases h0 with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, eq_comm]
  by_cases! h : a = ⊤ ∨ b = ⊤
  · rcases h with rfl | rfl <;> simp [hpq.pos, hpq.symm.pos, h0, div_eq_mul_inv]
  rw [← coe_toNNReal h.left, ← coe_toNNReal h.right, ← coe_mul, ← coe_rpow_of_nonneg _ hpq.nonneg,
    ← coe_rpow_of_nonneg _ hpq.symm.nonneg, ← ofNNReal_toNNReal, ← ofNNReal_toNNReal,
    ← coe_div (by simp [hpq.pos]), ← coe_div (by simp [hpq.symm.pos]), ← coe_add, coe_inj, coe_inj]
  simp [young_inequality_real_eq_iff a.toNNReal b.toNNReal hpq]

end ENNReal

end Young

section HoelderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace NNReal

/-
**NNReal.inner_le_Lp_mul_Lp_of_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p ≤ 1) (hg : ∑ i ∈ s, g i ^ q ≤ 1) :
    ∑ i ∈ s, f i * g i ≤ 1 := by
  have hp : 0 < p.toNNReal := zero_lt_one.trans hpq.toNNReal.lt
  have hq : 0 < q.toNNReal := zero_lt_one.trans hpq.toNNReal.symm.lt
  calc
    ∑ i ∈ s, f i * g i ≤ ∑ i ∈ s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i) (g i) hpq
    _ = (∑ i ∈ s, f i ^ p) / Real.toNNReal p + (∑ i ∈ s, g i ^ q) / Real.toNNReal q := by
      rw [sum_add_distrib, sum_div, sum_div]
    _ ≤ 1 / Real.toNNReal p + 1 / Real.toNNReal q := by gcongr
    _ = 1 := by simp_rw [one_div, hpq.toNNReal.inv_add_inv_eq_one]
/-
**NNReal.inner_le_Lp_mul_Lp_of_norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p = 0) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

/-- **Hölder inequality**: The scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
/-
**NNReal.inner_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inner_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q : Real} (hpq : p.HolderConjug
ate q) : ∑ i in s, f i * g i <= (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^
 q) ^ (1 / q)
参数：f g : ι -> Real>=0；hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `_private.Mathlib.Analysis.MeanInequalities.0.NNReal.inner_le_Lp_mul_Lp_o
f_norm_eq_zero`：∀ {ι : Type u} (s : Finset ι) (f g : ι → NNReal) {p q : ℝ},   p.
HolderConjugate q →     ∑ i ∈ s, f i ^ p = 0 → ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `_private.Mathlib.Analysis.MeanInequalities.0.NNReal.inner_le_Lp_mul_Lp_o
f_norm_le_one`：∀ {ι : Type u} (s : Finset ι) (f g : ι → NNReal) {p q : ℝ},   p.H
olderConjugate q → ∑ i ∈ s, f i ^ p ≤ 1 → ∑ i ∈ s, g i ^ q ≤ 1 → ∑ i ∈ s, f…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.div_rpow`：div_rpow (x y : Real>=0) (z : Real) : (x / y) ^ z = x ^
 z / y ^ z
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**Hölder inequality**: The scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums
 over finite sets,
with `ℝ≥0`-valued functions.
-/
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  obtain hf | hf := eq_zero_or_pos (∑ i ∈ s, f i ^ p)
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hf
  obtain hg | hg := eq_zero_or_pos (∑ i ∈ s, g i ^ q)
  · calc
      ∑ i ∈ s, f i * g i = ∑ i ∈ s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ ≤ (∑ i ∈ s, g i ^ q) ^ (1 / q) * (∑ i ∈ s, f i ^ p) ^ (1 / p) :=
        (inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hg)
      _ = (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := mul_comm _ _
  let f' i := f i / (∑ i ∈ s, f i ^ p) ^ (1 / p)
  let g' i := g i / (∑ i ∈ s, g i ^ q) ^ (1 / q)
  suffices (∑ i ∈ s, f' i * g' i) ≤ 1 by
    simp_rw [f', g', div_mul_div_comm, ← sum_div] at this
    rwa [div_le_iff₀, one_mul] at this
    positivity
  refine inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eq ?_) (le_of_eq ?_)
  · simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.ne_zero, rpow_one,
      div_self hf.ne']
  · simp_rw [g', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.symm.ne_zero,
      rpow_one, div_self hg.ne']

/-- **Hölder inequality**: The (`r`-power of the) `L^r` norm of the product of two functions is
bounded by the product of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q`, and `r`
form a `Real.HolderTriple`. -/
/-
**NNReal.Lr_rpow_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lr_rpow_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q r : Real} (hpqr : p.HolderT
riple q r) : ∑ i in s, (f i * g i) ^ r <= (∑ i in s, f i ^ p) ^ (r / p) * (∑ i i
n s, g i ^ q) ^ (r / q)
参数：f g : ι -> Real>=0；hpqr : p.HolderTriple q r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `NNReal.inner_le_Lp_mul_Lq`：inner_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q 
: Real} (hpq : p.HolderConjugate q) : ∑ i in s, f i * g i <= (∑ i in s, f i ^ p)
 ^ (1 / p) * (∑…
· 使用引理 `Real.HolderTriple.holderConjugate_div_div`：holderConjugate_div_div : (p 
/ r).HolderConjugate (q / r) where inv_add_inv_eq_inv

--- 原说明 ---
**Hölder inequality**: The (`r`-power of the) `L^r` norm of the product of two f
unctions is
bounded by the product of (the `r`-powers of) their `L^p` and `L^q` norms when `
p`, `q`, and `r`
form a `Real.HolderTriple`.
-/
theorem Lr_rpow_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
  simpa [mul_rpow, ← NNReal.rpow_mul, ← mul_div_assoc, hpqr.pos'.ne', fieldEq] using
    inner_le_Lp_mul_Lq s (fun i ↦ f i ^ r) (fun i ↦ g i ^ r) hpqr.holderConjugate_div_div

/-- **Hölder inequality**: The `L^r` norm of the product of two functions is bounded by the
product of their `L^p` and `L^q` norms when `p`, `q`, and `r` form a `Real.HolderTriple`. -/
/-
**NNReal.Lr_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lr_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q r : Real} (hpqr : p.HolderTriple
 q r) : (∑ i in s, (f i * g i) ^ r) ^ (1 / r) <= (∑ i in s, f i ^ p) ^ (1 / p) *
 (∑ i in s, g i ^ q) ^ (1 / q)
参数：f g : ι -> Real>=0；hpqr : p.HolderTriple q r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
**Hölder inequality**: The `L^r` norm of the product of two functions is bounded
 by the
product of their `L^p` and `L^q` norms when `p`, `q`, and `r` form a `Real.Holde
rTriple`.
-/
theorem Lr_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    (∑ i ∈ s, (f i * g i) ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  convert
    rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos' : 0 < 1 / r) |>.mpr <|
      Lr_rpow_le_Lp_mul_Lq s f g hpqr
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

/-- **Weighted Hölder inequality**. -/
/-
**NNReal.inner_le_weight_mul_Lp** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：inner_le_weight_mul_Lp (s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι ->
 Real>=0) : ∑ i in s, w i * f i <= (∑ i in s, w i) ^ (1 - p⁻¹) * (∑ i in s, w i 
* f i ^ p) ^ p⁻¹
参数：s : Finset ι；hp : 1 <= p；w f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `NNReal.rpow_of_add_eq`：rpow_of_add_eq (x : Real>=0) (hw : w != 0) (h : y
 + z = w) : x ^ w = x ^ y * x ^ z
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNReal.inner_le_Lp_mul_Lq`：inner_le_Lp_mul_Lq (f g : ι -> Real>=0) {p q 
: Real} (hpq : p.HolderConjugate q) : ∑ i in s, f i * g i <= (∑ i in s, f i ^ p)
 ^ (1 / p) * (∑…
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.holderConjugate_iff`：∀ {p q : ℝ}, p.HolderConjugate q ↔ 1 < p ∧ p⁻¹
 + q⁻¹ = 1
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
**Weighted Hölder inequality**.
-/
lemma inner_le_weight_mul_Lp (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i ∈ s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ ≤ (∑ i ∈ s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i ∈ s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lq _ _ _ (.symm <| Real.holderConjugate_iff.mpr ⟨hp, by simp⟩)
    _ = _ := ?_
  · congr with i
    rw [← mul_assoc, ← rpow_of_add_eq _ one_ne_zero, rpow_one]
    simp
  · have hp₀ : p ≠ 0 := by positivity
    have hp₁ : 1 - p⁻¹ ≠ 0 := by simp [sub_eq_zero, hp.ne']
    simp [mul_rpow, div_inv_eq_mul, one_mul, one_div, hp₀, hp₁]

/-- **Hölder inequality**: The (`r`-power of the) `L^r` norm of the product of two functions is
bounded by the product of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q`, and `r`
form a `Real.HolderTriple`. A version for `NNReal`-valued functions. For an alternative version,
convenient if the infinite sums are already expressed as powers, see `inner_le_Lp_mul_Lq_hasSum`. -/
/-
**NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNRea
l`。
形式化陈述：summable_and_Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real}
 (hpqr : p.HolderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun
 i => g i ^ q) : (Summable fun i => (f i * g i) ^ r) ∧ ∑' i, (f i * g i) ^ r <= 
(∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q)
参数：hpqr : p.HolderTriple q r；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.all_pos`：all_pos : 0 < p ∧ 0 < q ∧ 0 < r
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `NNReal.Lr_rpow_le_Lp_mul_Lq`：Lr_rpow_le_Lp_mul_Lq (f g : ι -> Real>=0) {
p q r : Real} (hpqr : p.HolderTriple q r) : ∑ i in s, (f i * g i) ^ r <= (∑ i in
 s, f i ^ p) ^ (r…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `hasSum_of_isLUB`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid α
] [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α]   [inst_3 : TopologicalSpac
e α] …
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Summable.tsum_le_of_sum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : Summati
onFilter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topologic
alSpace α] [Orde…

--- 原说明 ---
**Hölder inequality**: The (`r`-power of the) `L^r` norm of the product of two f
unctions is
bounded by the product of (the `r`-powers of) their `L^p` and `L^q` norms when `
p`, `q`, and `r`
form a `Real.HolderTriple`. A version for `NNReal`-valued functions. For an alte
rnative version,
convenient if the infinite sums are already expressed as powers, see `inner_le_L
p_mul_Lq_hasSum`.
-/
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  have H₁ : ∀ s : Finset ι,
      ∑ i ∈ s, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
    intro s
    obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
    refine le_trans (Lr_rpow_le_Lp_mul_Lq s f g hpqr) (mul_le_mul ?_ ?_ bot_le bot_le)
    · gcongr
      exact hf.sum_le_tsum _ (fun _ _ => zero_le)
    · gcongr
      exact hg.sum_le_tsum _ (fun _ _ => zero_le)
  have bdd : BddAbove (Set.range fun s => ∑ i ∈ s, (f i * g i) ^ r) := by
    refine ⟨(∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q), ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  exact ⟨H₂, H₂.tsum_le_of_sum_le H₁⟩

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_hasSum`. -/
/-
**NNReal.summable_and_inner_le_Lp_mul_Lq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`
。
形式化陈述：summable_and_inner_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hp
q : p.HolderConjugate q) (hf : Summable fun i => f i ^ p) (hg : Summable fun i =
> g i ^ q) : (Summable fun i => f i * g i) ∧ ∑' i, f i * g i <= (∑' i, f i ^ p) 
^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum`：summable_and_Lr_rpow_le_L
p_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r) (h
f : Summable fun i => f i ^ p) (hg …

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `N
NReal`-valued
functions. For an alternative version, convenient if the infinite sums are alrea
dy expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_hasSum`.
-/
theorem summable_and_inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpq hf hg
/-
**NNReal.summable_mul_rpow_of_Lp_Lq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_mul_rpow_of_Lp_Lq {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.H
olderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ 
q) : Summable fun i => (f i * g i) ^ r
参数：hpqr : p.HolderTriple q r；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum`：summable_and_Lr_rpow_le_L
p_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r) (h
f : Summable fun i => f i ^ p) (hg …
-/
theorem summable_mul_rpow_of_Lp_Lq {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1
/-
**NNReal.summable_mul_of_Lp_Lq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_mul_of_Lp_Lq {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderCon
jugate q) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) : Su
mmable fun i => f i * g i
参数：hpq : p.HolderConjugate q；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NNReal.summable_and_inner_le_Lp_mul_Lq_tsum`：summable_and_inner_le_Lp_mu
l_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q) (hf : Su
mmable fun i => f i ^ p) (hg : Su…
-/
theorem summable_mul_of_Lp_Lq {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1
/-
**NNReal.Lr_rpow_le_Lp_mul_Lq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.Ho
lderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q
) : ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / 
q)
参数：hpqr : p.HolderTriple q r；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum`：summable_and_Lr_rpow_le_L
p_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r) (h
f : Summable fun i => f i ^ p) (hg …
-/
theorem Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2
/-
**NNReal.Lr_le_Lp_mul_Lq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lr_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderT
riple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) : (
∑' i, (f i * g i) ^ r) ^ (1 / r) <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) 
^ (1 / q)
参数：hpqr : p.HolderTriple q r；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
（共 46 条，此处仅展示前 30 条）
-/
theorem Lr_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  convert!
    rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos') |>.mpr <|
      Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp
/-
**NNReal.inner_le_Lp_mul_Lq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inner_le_Lp_mul_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderC
onjugate q) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) : 
∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : Summable fun i => f i ^ p；hg : Summable fun i 
=> g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NNReal.summable_and_inner_le_Lp_mul_Lq_tsum`：summable_and_inner_le_Lp_mu
l_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q) (hf : Su
mmable fun i => f i ^ p) (hg : Su…
-/
theorem inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2

@[deprecated (since := "2026-02-12")] alias inner_le_Lp_mul_Lq_tsum' := inner_le_Lp_mul_Lq_tsum

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum`. -/
/-
**NNReal.inner_le_Lp_mul_Lq_hasSum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inner_le_Lp_mul_Lq_hasSum {f g : ι -> Real>=0} {A B : Real>=0} {p q : Real
} (hpq : p.HolderConjugate q) (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : Has
Sum (fun i => g i ^ q) (B ^ q)) : exists C, C <= A * B ∧ HasSum (fun i => f i * 
g i) C
参数：hpq : p.HolderConjugate q；hf : HasSum (fun i => f i ^ p) (A ^ p)；hg : HasSum 
(fun i => g i ^ q) (B ^ q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.summable_and_inner_le_Lp_mul_Lq_tsum`：summable_and_inner_le_Lp_mu
l_Lq_tsum {f g : ι -> Real>=0} {p q : Real} (hpq : p.HolderConjugate q) (hf : Su
mmable fun i => f i ^ p) (hg : Su…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `NNReal.rpow_inv_rpow_self`：rpow_inv_rpow_self {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ y) ^ (1 / y) = x
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `N
NReal`-valued
functions. For an alternative version, convenient if the infinite sums are not a
lready expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum`.
-/
theorem inner_le_Lp_mul_Lq_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : HasSum (fun i => f i ^ p) (A ^ p))
    (hg : HasSum (fun i => g i ^ q) (B ^ q)) : ∃ C, C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  obtain ⟨H₁, H₂⟩ := summable_and_inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq, rpow_inv_rpow_self hpq.symm.ne_zero]
  refine ⟨∑' i, f i * g i, ?_, ?_⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hpq.ne_zero] using H₁.hasSum

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0`-valued functions.
-/
/-
**NNReal.rpow_sum_le_const_mul_sum_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_sum_le_const_mul_sum_rpow (f : ι -> Real>=0) {p : Real} (hp : 1 <= p)
 : (∑ i in s, f i) ^ p <= (#s : Real>=0) ^ (p - 1) * ∑ i in s, f i ^ p
参数：f : ι -> Real>=0；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.HolderConjugate.conjExponent`：∀ {p : ℝ}, 1 < p → p.HolderConjugate 
p.conjExponent
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `Real.HolderConjugate.div_conj_eq_sub_one`：div_conj_eq_sub_one : p / q = 
p - 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant
 times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0`
-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (f : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (#s : ℝ≥0) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [NNReal.mul_rpow, ← NNReal.rpow_mul, hp₁, hq, one_mul, one_rpow, rpow_one,
    Pi.one_apply, sum_const, Nat.smul_one_eq_cast] using
    NNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i ∈ s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
/-
**NNReal.isGreatest_Lp** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：isGreatest_Lp (f : ι -> Real>=0) {p q : Real} (hpq : p.HolderConjugate q) 
: IsGreatest ((fun g : ι -> Real>=0 => ∑ i in s, f i * g i) '' { g | ∑ i in s, g
 i ^ q <= 1 }) ((∑ i in s, f i ^ p) ^ (1 / p))
参数：f : ι -> Real>=0；hpq : p.HolderConjugate q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用引理 `mul_div_cancel_left_of_imp`：mul_div_cancel_left_of_imp (h : a = 0 -> b =
 0) : a * b / a = b
· 使用定理 `NNReal.div_rpow`：div_rpow (x y : Real>=0) (z : Real) : (x / y) ^ z = x ^
 z / y ^ z
· 使用定理 `Real.HolderConjugate.mul_eq_add`：mul_eq_add : p * q = p + q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_sub'`：rpow_sub' (h : y - z != 0) (x : Real>=0) : x ^ (y - z)
 = x ^ y / x ^ z
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i ∈ s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to 
one.
-/
theorem isGreatest_Lp (f : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest ((fun g : ι → ℝ≥0 => ∑ i ∈ s, f i * g i) '' { g | ∑ i ∈ s, g i ^ q ≤ 1 })
      ((∑ i ∈ s, f i ^ p) ^ (1 / p)) := by
  constructor
  · use fun i => f i ^ p / f i / (∑ i ∈ s, f i ^ p) ^ (1 / q)
    obtain hf | hf := eq_zero_or_pos (∑ i ∈ s, f i ^ p)
    · simp [hf, hpq.ne_zero, hpq.symm.ne_zero]
    · have A : p + q - q ≠ 0 := by simp [hpq.ne_zero]
      have B : ∀ y : ℝ≥0, y * y ^ p / y = y ^ p := by
        refine fun y => mul_div_cancel_left_of_imp fun h => ?_
        simp [h, hpq.ne_zero]
      simp only [Set.mem_ofPred_eq, div_rpow, ← sum_div, ← rpow_mul,
        div_mul_cancel₀ _ hpq.symm.ne_zero, rpow_one, div_le_iff₀ hf, one_mul, hpq.mul_eq_add, ←
        rpow_sub' A, add_sub_cancel_right, le_refl, true_and, ← mul_div_assoc, B]
      rw [div_eq_iff, ← rpow_add hf.ne', one_div, one_div, hpq.inv_add_inv_eq_one, rpow_one]
      simpa [hpq.symm.ne_zero] using hf.ne'
  · rintro _ ⟨g, hg, rfl⟩
    apply le_trans (inner_le_Lp_mul_Lq s f g hpq)
    simpa only [mul_one] using
      mul_le_mul_right (NNReal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) _

/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `NNReal`-valued functions. -/
/-
**NNReal.Lp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lp_add_le (f g : ι -> Real>=0) {p : Real} (hp : 1 <= p) : (∑ i in s, (f i 
+ g i) ^ p) ^ (1 / p) <= (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (
1 / p)
参数：f g : ι -> Real>=0；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.HolderConjugate.conjExponent`：∀ {p : ℝ}, 1 < p → p.HolderConjugate 
p.conjExponent
· 使用定理 `NNReal.isGreatest_Lp`：isGreatest_Lp (f : ι -> Real>=0) {p q : Real} (hpq
 : p.HolderConjugate q) : IsGreatest ((fun g : ι -> Real>=0 => ∑ i in s, f i * g
 i) '' { g…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less t
han or equal
to the sum of the `L_p`-seminorms of the summands. A version for `NNReal`-valued
 functions.
-/
theorem Lp_add_le (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp [Finset.sum_add_distrib]
  have hpq := Real.HolderConjugate.conjExponent hp
  have := isGreatest_Lp s (f + g) hpq
  simp only [Pi.add_apply, add_mul, sum_add_distrib] at this
  rcases this.1 with ⟨φ, hφ, H⟩
  rw [← H]
  exact add_le_add ((isGreatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩) ((isGreatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, convenient if the
infinite sums are already expressed as `p`-th powers, see `Lp_add_le_hasSum_of_nonneg`. -/
/-
**NNReal.Lp_add_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lp_add_le_tsum {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summabl
e fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : (Summable fun i => (f i +
 g i) ^ p) ∧ (∑' i, (f i + g i) ^ p) ^ (1 / p) <= (∑' i, f i ^ p) ^ (1 / p) + (∑
' i, g i ^ p) ^ (1 / p)
参数：hp : 1 <= p；hf : Summable fun i => f i ^ p；hg : Summable fun i => g i ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_inv_le_iff`：rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `NNReal.Lp_add_le`：Lp_add_le (f g : ι -> Real>=0) {p : Real} (hp : 1 <= p
) : (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <= (∑ i in s, f i ^ p) ^ (1 / p) + (∑ 
i in s…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors 
is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infin
ite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, conv
enient if the
infinite sums are already expressed as `p`-th powers, see `Lp_add_le_hasSum_of_n
onneg`.
-/
theorem Lp_add_le_tsum {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have H₁ : ∀ s : Finset ι,
      (∑ i ∈ s, (f i + g i) ^ p) ≤
        ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p := by
    intro s
    rw [one_div, ← NNReal.rpow_inv_le_iff pos, ← one_div]
    refine le_trans (Lp_add_le s f g hp) ?_
    gcongr <;>
      refine Summable.sum_le_tsum _ (fun _ _ ↦ zero_le) ?_
    exacts [hf, hg]
  have bdd : BddAbove (Set.range fun s => ∑ i ∈ s, (f i + g i) ^ p) := by
    refine ⟨((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p, ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  refine ⟨H₂, ?_⟩
  rw [one_div, NNReal.rpow_inv_le_iff pos, ← one_div]
  exact H₂.tsum_le_of_sum_le H₁
/-
**NNReal.summable_Lp_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：summable_Lp_add {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summab
le fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : Summable fun i => (f i +
 g i) ^ p
参数：hp : 1 <= p；hf : Summable fun i => f i ^ p；hg : Summable fun i => g i ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NNReal.Lp_add_le_tsum`：Lp_add_le_tsum {f g : ι -> Real>=0} {p : Real} (h
p : 1 <= p) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : 
(Summable f…
-/
theorem summable_Lp_add {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum hp hf hg).1
/-
**NNReal.Lp_add_le_tsum'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lp_add_le_tsum' {f g : ι -> Real>=0} {p : Real} (hp : 1 <= p) (hf : Summab
le fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : (∑' i, (f i + g i) ^ p) 
^ (1 / p) <= (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)
参数：hp : 1 <= p；hf : Summable fun i => f i ^ p；hg : Summable fun i => g i ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NNReal.Lp_add_le_tsum`：Lp_add_le_tsum {f g : ι -> Real>=0} {p : Real} (h
p : 1 <= p) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : 
(Summable f…
-/
theorem Lp_add_le_tsum' {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum hp hf hg).2

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, convenient if the
infinite sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
/-
**NNReal.Lp_add_le_hasSum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：Lp_add_le_hasSum {f g : ι -> Real>=0} {A B : Real>=0} {p : Real} (hp : 1 <
= p) (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ p) (B
 ^ p)) : exists C, C <= A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p)
参数：hp : 1 <= p；hf : HasSum (fun i => f i ^ p) (A ^ p)；hg : HasSum (fun i => g i 
^ p) (B ^ p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNReal.Lp_add_le_tsum`：Lp_add_le_tsum {f g : ι -> Real>=0} {p : Real} (h
p : 1 <= p) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : 
(Summable f…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `NNReal.rpow_inv_rpow_self`：rpow_inv_rpow_self {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ y) ^ (1 / y) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.rpow_self_rpow_inv`：rpow_self_rpow_inv {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ (1 / y)) ^ y = x
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors 
is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infin
ite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, conv
enient if the
infinite sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of
_nonneg`.
-/
theorem Lp_add_le_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p : ℝ} (hp : 1 ≤ p)
    (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  have hp' : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by rw [hg.tsum_eq, rpow_inv_rpow_self hp']
  refine ⟨(∑' i, (f i + g i) ^ p) ^ (1 / p), ?_, ?_⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hp'] using H₁.hasSum

end NNReal

namespace Real

variable (f g : ι → ℝ) {p q r : ℝ}

/-- **Hölder inequality**: the sum of (the `r`-powers of) the product of two functions is bounded by
the product of their `L^p` and `L^q` norms when `p`, `q` and `r` form a `Real.HolderTriple`.
Version for sums over finite sets, with real-valued functions. -/
/-
**Real.Lr_rpow_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q r) : ∑ i in s, |f i * g i| ^
 r <= (∑ i in s, |f i| ^ p) ^ (r / p) * (∑ i in s, |g i| ^ q) ^ (r / q)
参数：hpqr : HolderTriple p q r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.Lr_rpow_le_Lp_mul_Lq`：Lr_rpow_le_Lp_mul_Lq (f g : ι -> Real>=0) {
p q r : Real} (hpqr : p.HolderTriple q r) : ∑ i in s, (f i * g i) ^ r <= (∑ i in
 s, f i ^ p) ^ (r…

--- 原说明 ---
**Hölder inequality**: the sum of (the `r`-powers of) the product of two functio
ns is bounded by
the product of their `L^p` and `L^q` norms when `p`, `q` and `r` form a `Real.Ho
lderTriple`.
Version for sums over finite sets, with real-valued functions.
-/
theorem Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q r) :
    ∑ i ∈ s, |f i * g i| ^ r ≤ (∑ i ∈ s, |f i| ^ p) ^ (r / p) * (∑ i ∈ s, |g i| ^ q) ^ (r / q) := by
  simpa using! NNReal.coe_le_coe.2 <| NNReal.Lr_rpow_le_Lp_mul_Lq s (fun i ↦ ⟨_, abs_nonneg (f i)⟩)
    (fun i ↦ ⟨_, abs_nonneg (g i)⟩) hpqr

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
/-
**Real.inner_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inner_le_Lp_mul_Lq (hpq : HolderConjugate p q) : ∑ i in s, f i * g i <= (∑
 i in s, |f i| ^ p) ^ (1 / p) * (∑ i in s, |g i| ^ q) ^ (1 / q)
参数：hpq : HolderConjugate p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.Lr_rpow_le_Lp_mul_Lq`：Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q
 r) : ∑ i in s, |f i * g i| ^ r <= (∑ i in s, |f i| ^ p) ^ (r / p) * (∑ i in s, 
|g i| ^ q) ^ (r…

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums
 over finite sets,
with real-valued functions.
-/
theorem inner_le_Lp_mul_Lq (hpq : HolderConjugate p q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := by
  refine le_trans (sum_le_sum fun i _ ↦ ?_) (by simpa using Lr_rpow_le_Lp_mul_Lq s f g hpq)
  simp only [← abs_mul, le_abs_self]

set_option backward.isDefEq.respectTransparency false in
/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ`-valued functions. -/
/-
**Real.rpow_sum_le_const_mul_sum_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_sum_le_const_mul_sum_rpow (hp : 1 <= p) : (∑ i in s, |f i|) ^ p <= (#
s : Real) ^ (p - 1) * ∑ i in s, |f i| ^ p
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.rpow_sum_le_const_mul_sum_rpow`：rpow_sum_le_const_mul_sum_rpow (f
 : ι -> Real>=0) {p : Real} (hp : 1 <= p) : (∑ i in s, f i) ^ p <= (#s : Real>=0
) ^ (p - 1) * ∑ i in s, f i…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant
 times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ`-v
alued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i|) ^ p ≤ (#s : ℝ) ^ (p - 1) * ∑ i ∈ s, |f i| ^ p := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this

-- for some reason `exact_mod_cast` can't replace this argument
/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `Real`-valued functions. -/
/-
**Real.Lp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lp_add_le (hp : 1 <= p) : (∑ i in s, |f i + g i| ^ p) ^ (1 / p) <= (∑ i in
 s, |f i| ^ p) ^ (1 / p) + (∑ i in s, |g i| ^ p) ^ (1 / p)
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.Lp_add_le`：Lp_add_le (f g : ι -> Real>=0) {p : Real} (hp : 1 <= p
) : (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <= (∑ i in s, f i ^ p) ^ (1 / p) + (∑ 
i in s…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less t
han or equal
to the sum of the `L_p`-seminorms of the summands. A version for `Real`-valued f
unctions.
-/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i + g i| ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) + (∑ i ∈ s, |g i| ^ p) ^ (1 / p) := by
  have := NNReal.coe_le_coe.2
    (NNReal.Lp_add_le s (fun i => .mk _ (abs_nonneg (f i))) (fun i => .mk _ (abs_nonneg (g i))) hp)
  push_cast at this
  refine le_trans (rpow_le_rpow ?_ (sum_le_sum fun i _ => ?_) ?_) this <;>
    simp [sum_nonneg, rpow_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add_le,
      rpow_le_rpow]

variable {f g}

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
/-
**Real.inner_le_Lp_mul_Lq_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : forall i in
 s, 0 <= f i) (hg : forall i in s, 0 <= g i) : ∑ i in s, f i * g i <= (∑ i in s,
 f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q)
参数：hpq : HolderConjugate p q；hf : forall i in s, 0 <= f i；hg : forall i in s, 0 
<= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.inner_le_Lp_mul_Lq`：inner_le_Lp_mul_Lq (hpq : HolderConjugate p q) 
: ∑ i in s, f i * g i <= (∑ i in s, |f i| ^ p) ^ (1 / p) * (∑ i in s, |g i| ^ q)
 ^ (1 / q)

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums
 over finite sets,
with real-valued nonnegative functions.
-/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  convert! inner_le_Lp_mul_Lq s f g hpq using 3 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi]

/-- **Hölder inequality**: the sum of (the `r`-power of) the product of two functions is bounded
by (the `r`-power of) the product of their `L^p` and `L^q` norms, when `p`, `q`, `r` form a
`Real.HolderTriple`. -/
/-
**Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lr_rpow_le_Lp_mul_Lq_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι -> Real
} {p q r : Real} (hpqr : p.HolderTriple q r) (hf : forall i in s, 0 <= f i) (hg 
: forall i in s, 0 <= g i) : ∑ i in s, (f i * g i) ^ r <= (∑ i in s, f i ^ p) ^ 
(r / p) * (∑ i in s, g i ^ q) ^ (r / q)
参数：s : Finset ι；hpqr : p.HolderTriple q r；hf : forall i in s, 0 <= f i；hg : fora
ll i in s, 0 <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.Lr_rpow_le_Lp_mul_Lq`：Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q
 r) : ∑ i in s, |f i * g i| ^ r <= (∑ i in s, |f i| ^ p) ^ (r / p) * (∑ i in s, 
|g i| ^ q) ^ (r…

--- 原说明 ---
**Hölder inequality**: the sum of (the `r`-power of) the product of two function
s is bounded
by (the `r`-power of) the product of their `L^p` and `L^q` norms, when `p`, `q`,
 `r` form a
`Real.HolderTriple`.
-/
theorem Lr_rpow_le_Lp_mul_Lq_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
  convert Lr_rpow_le_Lp_mul_Lq s f g hpqr with i hi
  · rw [abs_of_nonneg (mul_nonneg (hf i hi) (hg i hi))]
  all_goals
    exact Eq.symm (abs_of_nonneg (by grind))

/-- **Weighted Hölder inequality**. -/
/-
**Real.inner_le_weight_mul_Lp_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : Real} (hp : 1 <= p) (
w f : ι -> Real) (hw : forall i, 0 <= w i) (hf : forall i, 0 <= f i) : ∑ i in s,
 w i * f i <= (∑ i in s, w i) ^ (1 - p⁻¹) * (∑ i in s, w i * f i ^ p) ^ p⁻¹
参数：s : Finset ι；hp : 1 <= p；w f : ι -> Real；hw : forall i, 0 <= w i；hf : forall 
i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `NNReal.inner_le_weight_mul_Lp`：inner_le_weight_mul_Lp (s : Finset ι) {p 
: Real} (hp : 1 <= p) (w f : ι -> Real>=0) : ∑ i in s, w i * f i <= (∑ i in s, w
 i) ^ (1 - p⁻¹) * (…

--- 原说明 ---
**Weighted Hölder inequality**.
-/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  lift w to ι → ℝ≥0 using hw
  lift f to ι → ℝ≥0 using hf
  beta_reduce at *
  norm_cast at *
  exact NNReal.inner_le_weight_mul_Lp _ hp _ _

/-- **Weighted Hölder inequality** in terms of `Finset.expect`. -/
/-
**Real.compact_inner_le_weight_mul_Lp_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`
。
形式化陈述：compact_inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : Real} (hp : 1
 <= p) {w f : ι -> Real} (hw : forall i, 0 <= w i) (hf : forall i, 0 <= f i) : 𝔼
 i in s, w i * f i <= (𝔼 i in s, w i) ^ (1 - p⁻¹) * (𝔼 i in s, w i * f i ^ p) ^ 
p⁻¹
参数：s : Finset ι；hp : 1 <= p；hw : forall i, 0 <= w i；hf : forall i, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_eq_sum_div_card`：expect_eq_sum_div_card (s : Finset ι) (f 
: ι -> K) : 𝔼 i in s, f i = (∑ i in s, f i) / #s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.div_rpow`：div_rpow (hx : 0 <= x) (hy : 0 <= y) (z : Real) : (x / y)
 ^ z = x ^ z / y ^ z
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Real.inner_le_weight_mul_Lp_of_nonneg`：inner_le_weight_mul_Lp_of_nonneg 
(s : Finset ι) {p : Real} (hp : 1 <= p) (w f : ι -> Real) (hw : forall i, 0 <= w
 i) (hf : forall i, 0 <= f …
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)

--- 原说明 ---
**Weighted Hölder inequality** in terms of `Finset.expect`.
-/
lemma compact_inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) {w f : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    𝔼 i ∈ s, w i * f i ≤ (𝔼 i ∈ s, w i) ^ (1 - p⁻¹) * (𝔼 i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  simp_rw [expect_eq_sum_div_card]
  rw [div_rpow, div_rpow, div_mul_div_comm, ← rpow_add', sub_add_cancel, rpow_one]
  · gcongr
    exact inner_le_weight_mul_Lp_of_nonneg s hp _ _ hw hf
  any_goals simp
  · exact sum_nonneg fun i _ ↦ by have := hw i; have := hf i; positivity
  · exact sum_nonneg fun i _ ↦ by have := hw i; positivity

/-- **Hölder inequality**: the sum of (the `r`-powers of) two functions is bounded by the product
of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q` and `r` form a `Real.HolderTriple`.
A version for `ℝ`-valued functions. -/
/-
**Real.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空
间 `Real`。
形式化陈述：summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q 
r) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i 
=> f i ^ p) (hg_sum : Summable fun i => g i ^ q) : (Summable fun i => (f i * g i
) ^ r) ∧ ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ 
(r / q)
参数：hpqr : p.HolderTriple q r；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum`：summable_and_Lr_rpow_le_L
p_mul_Lq_tsum {f g : ι -> Real>=0} {p q r : Real} (hpqr : p.HolderTriple q r) (h
f : Summable fun i => f i ^ p) (hg …

--- 原说明 ---
**Hölder inequality**: the sum of (the `r`-powers of) two functions is bounded b
y the product
of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q` and `r` form a 
`Real.HolderTriple`.
A version for `ℝ`-valued functions.
-/
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at *
  exact NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf_sum hg_sum

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `ℝ`-valued functions.
For an alternative version, convenient if the infinite sums are already expressed as `p`-th powers,
see `inner_le_Lp_mul_Lq_hasSum_of_nonneg`. -/
/-
**Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 
`Real`。
形式化陈述：summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q)
 (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i =>
 f i ^ p) (hg_sum : Summable fun i => g i ^ q) : (Summable fun i => f i * g i) ∧
 ∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg`：summable_and_Lr_r
pow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i, 0 <=
 f i) (hg : forall i, 0 <= g i) (hf_sum : S…

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `ℝ
`-valued functions.
For an alternative version, convenient if the infinite sums are already expresse
d as `p`-th powers,
see `inner_le_Lp_mul_Lq_hasSum_of_nonneg`.
-/
theorem summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum
/-
**Real.summable_Lr_of_Lp_Lq_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：summable_Lr_of_Lp_Lq_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i,
 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_su
m : Summable fun i => g i ^ q) : Summable fun i => (f i * g i) ^ r
参数：hpqr : p.HolderTriple q r；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg`：summable_and_Lr_r
pow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i, 0 <=
 f i) (hg : forall i, 0 <= g i) (hf_sum : S…
-/
theorem summable_Lr_of_Lp_Lq_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).1
/-
**Real.summable_mul_of_Lp_Lq_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：summable_mul_of_Lp_Lq_of_nonneg (hpq : p.HolderConjugate q) (hf : forall i
, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_s
um : Summable fun i => g i ^ q) : Summable fun i => f i * g i
参数：hpq : p.HolderConjugate q；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg`：summable_and_inner_
le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : forall i, 0 <= f i
) (hg : forall i, 0 <= g i) (hf_sum : Sum…
-/
theorem summable_mul_of_Lp_Lq_of_nonneg (hpq : p.HolderConjugate q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1
/-
**Real.Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : fora
ll i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (
hg_sum : Summable fun i => g i ^ q) : ∑' i, (f i * g i) ^ r <= (∑' i, f i ^ p) ^
 (r / p) * (∑' i, g i ^ q) ^ (r / q)
参数：hpqr : p.HolderTriple q r；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Real.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg`：summable_and_Lr_r
pow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i, 0 <=
 f i) (hg : forall i, 0 <= g i) (hf_sum : S…
-/
theorem Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).2
/-
**Real.Lr_le_Lp_mul_Lq_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lr_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : forall i,
 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_su
m : Summable fun i => g i ^ q) : (∑' i, (f i * g i) ^ r) ^ (1 / r) <= (∑' i, f i
 ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q)
参数：hpqr : p.HolderTriple q r；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 52 条，此处仅展示前 30 条）
-/
theorem Lr_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  -- It's really inconvenient that `positivity` can't use `∀` hypotheses.
  have hf' : 0 ≤ ∑' i, f i ^ p := tsum_nonneg fun i ↦ rpow_nonneg (hf i) p
  have hg' : 0 ≤ ∑' i, g i ^ q := tsum_nonneg fun i ↦ rpow_nonneg (hg i) q
  have hr := hpqr.pos'
  convert
    rpow_le_rpow_iff (tsum_nonneg fun i ↦ by positivity [hf i, hg i]) (by positivity)
          (inv_eq_one_div r ▸ inv_pos.mpr hr) |>.mpr <|
      Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum
  rw [mul_rpow (rpow_nonneg hf' _) (rpow_nonneg hg' _), ← Real.rpow_mul hg', ← Real.rpow_mul hf']
  field_simp
/-
**Real.inner_le_Lp_mul_Lq_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : forall
 i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg
_sum : Summable fun i => g i ^ q) : ∑' i, f i * g i <= (∑' i, f i ^ p) ^ (1 / p)
 * (∑' i, g i ^ q) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_
sum : Summable fun i => f i ^ p；hg_sum : Summable fun i => g i ^ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg`：summable_and_inner_
le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : forall i, 0 <= f i
) (hg : forall i, 0 <= g i) (hf_sum : Sum…
-/
theorem inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

@[deprecated (since := "2026-02-12")]
alias inner_le_Lp_mul_Lq_of_nonneg' := inner_le_Lp_mul_Lq_of_nonneg

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum_of_nonneg`. -/
/-
**Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inner_le_Lp_mul_Lq_hasSum_of_nonneg (hpq : p.HolderConjugate q) {A B : Rea
l} (hA : 0 <= A) (hB : 0 <= B) (hf : forall i, 0 <= f i) (hg : forall i, 0 <= g 
i) (hf_sum : HasSum (fun i => f i ^ p) (A ^ p)) (hg_sum : HasSum (fun i => g i ^
 q) (B ^ q)) : exists C : Real, 0 <= C ∧ C <= A * B ∧ HasSum (fun i => f i * g i
) C
参数：hpq : p.HolderConjugate q；hA : 0 <= A；hB : 0 <= B；hf : forall i, 0 <= f i；hg 
: forall i, 0 <= g i；hf_sum : HasSum (fun i => f i ^ p) (A ^ p)；hg_sum : HasSum 
(fun i => g i ^ q) (B ^ q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `NNReal.inner_le_Lp_mul_Lq_hasSum`：inner_le_Lp_mul_Lq_hasSum {f g : ι -> 
Real>=0} {A B : Real>=0} {p q : Real} (hpq : p.HolderConjugate q) (hf : HasSum (
fun i => f i ^ p) (A ^…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `N
NReal`-valued
functions. For an alternative version, convenient if the infinite sums are not a
lready expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum_of_nonneg`.
-/
theorem inner_le_Lp_mul_Lq_hasSum_of_nonneg (hpq : p.HolderConjugate q) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : HasSum (fun i => f i ^ p) (A ^ p)) (hg_sum : HasSum (fun i => g i ^ q) (B ^ q)) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ := NNReal.inner_le_Lp_mul_Lq_hasSum hpq hf_sum hg_sum
  refine ⟨C, C.prop, hC, ?_⟩
  norm_cast

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with nonnegative `ℝ`-valued
functions. -/
/-
**Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`
。
形式化陈述：rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 <= p) (hf : forall i in s
, 0 <= f i) : (∑ i in s, f i) ^ p <= (#s : Real) ^ (p - 1) * ∑ i in s, f i ^ p
参数：hp : 1 <= p；hf : forall i in s, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_sum_le_const_mul_sum_rpow`：rpow_sum_le_const_mul_sum_rpow (hp 
: 1 <= p) : (∑ i in s, |f i|) ^ p <= (#s : Real) ^ (p - 1) * ∑ i in s, |f i| ^ p

--- 原说明 ---
For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant
 times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with nonne
gative `ℝ`-valued
functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ p ≤ (#s : ℝ) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  convert! rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi]

/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ`-valued nonnegative
functions. -/
/-
**Real.Lp_add_le_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lp_add_le_of_nonneg (hp : 1 <= p) (hf : forall i in s, 0 <= f i) (hg : for
all i in s, 0 <= g i) : (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <= (∑ i in s, f i 
^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p)
参数：hp : 1 <= p；hf : forall i in s, 0 <= f i；hg : forall i in s, 0 <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.Lp_add_le`：Lp_add_le (hp : 1 <= p) : (∑ i in s, |f i + g i| ^ p) ^ 
(1 / p) <= (∑ i in s, |f i| ^ p) ^ (1 / p) + (∑ i in s, |g i| ^ p) ^ (1 / p)

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less t
han or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ`-valued nonn
egative
functions.
-/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  convert! Lp_add_le s f g hp using 2 <;> [skip; congr 1; congr 1] <;> apply sum_congr rfl <;>
      intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are already expressed as `p`-th powers, see `Lp_add_le_hasSum_of_nonneg`. -/
/-
**Real.Lp_add_le_tsum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lp_add_le_tsum_of_nonneg (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : for
all i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i =
> g i ^ p) : (Summable fun i => (f i + g i) ^ p) ∧ (∑' i, (f i + g i) ^ p) ^ (1 
/ p) <= (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)
参数：hp : 1 <= p；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_sum : Summable
 fun i => f i ^ p；hg_sum : Summable fun i => g i ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.Lp_add_le_tsum`：Lp_add_le_tsum {f g : ι -> Real>=0} {p : Real} (h
p : 1 <= p) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ p) : 
(Summable f…

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors 
is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infin
ite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenien
t if the infinite
sums are already expressed as `p`-th powers, see `Lp_add_le_hasSum_of_nonneg`.
-/
theorem Lp_add_le_tsum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast0 at *
  exact NNReal.Lp_add_le_tsum hp hf_sum hg_sum
/-
**Real.summable_Lp_add_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：summable_Lp_add_of_nonneg (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : fo
rall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i 
=> g i ^ p) : Summable fun i => (f i + g i) ^ p
参数：hp : 1 <= p；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_sum : Summable
 fun i => f i ^ p；hg_sum : Summable fun i => g i ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.Lp_add_le_tsum_of_nonneg`：Lp_add_le_tsum_of_nonneg (hp : 1 <= p) (h
f : forall i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f 
i ^ p) (hg_sum : Su…
-/
theorem summable_Lp_add_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1
/-
**Real.Lp_add_le_tsum_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lp_add_le_tsum_of_nonneg' (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : fo
rall i, 0 <= g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i 
=> g i ^ p) : (∑' i, (f i + g i) ^ p) ^ (1 / p) <= (∑' i, f i ^ p) ^ (1 / p) + (
∑' i, g i ^ p) ^ (1 / p)
参数：hp : 1 <= p；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hf_sum : Summable
 fun i => f i ^ p；hg_sum : Summable fun i => g i ^ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Real.Lp_add_le_tsum_of_nonneg`：Lp_add_le_tsum_of_nonneg (hp : 1 <= p) (h
f : forall i, 0 <= f i) (hg : forall i, 0 <= g i) (hf_sum : Summable fun i => f 
i ^ p) (hg_sum : Su…
-/
theorem Lp_add_le_tsum_of_nonneg' (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
/-
**Real.Lp_add_le_hasSum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Lp_add_le_hasSum_of_nonneg (hp : 1 <= p) (hf : forall i, 0 <= f i) (hg : f
orall i, 0 <= g i) {A B : Real} (hA : 0 <= A) (hB : 0 <= B) (hfA : HasSum (fun i
 => f i ^ p) (A ^ p)) (hgB : HasSum (fun i => g i ^ p) (B ^ p)) : exists C, 0 <=
 C ∧ C <= A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p)
参数：hp : 1 <= p；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i；hA : 0 <= A；hB : 
0 <= B；hfA : HasSum (fun i => f i ^ p) (A ^ p)；hgB : HasSum (fun i => g i ^ p) (
B ^ p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `NNReal.Lp_add_le_hasSum`：Lp_add_le_hasSum {f g : ι -> Real>=0} {A B : Re
al>=0} {p : Real} (hp : 1 <= p) (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : H
asSum (fun i …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors 
is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infin
ite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenien
t if the infinite
sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`.
-/
theorem Lp_add_le_hasSum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hfA : HasSum (fun i => f i ^ p) (A ^ p))
    (hgB : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, 0 ≤ C ∧ C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at hfA hgB
  norm_cast at hfA hgB
  obtain ⟨C, hC₁, hC₂⟩ := NNReal.Lp_add_le_hasSum hp hfA hgB
  use C
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce
  norm_cast
  exact ⟨zero_le, hC₁, hC₂⟩

end Real

namespace ENNReal

variable (f g : ι → ℝ≥0∞) {p q : ℝ}

-- TODO: fix the non-terminal simp on the last line
set_option linter.flexible false in
/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
/-
**ENNReal.inner_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inner_le_Lp_mul_Lq (hpq : p.HolderConjugate q) : ∑ i in s, f i * g i <= (∑
 i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q)
参数：hpq : p.HolderConjugate q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
**Hölder inequality**: the scalar product of two functions is bounded by the pro
duct of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums
 over finite sets,
with `ℝ≥0∞`-valued functions.
-/
theorem inner_le_Lp_mul_Lq (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  by_cases! H : (∑ i ∈ s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i ∈ s, g i ^ q) ^ (1 / q) = 0
  · replace H : (∀ i ∈ s, f i = 0) ∨ ∀ i ∈ s, g i = 0 := by
      simpa [ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
        sum_eq_zero_iff_of_nonneg] using H
    have : ∀ i ∈ s, f i * g i = 0 := fun i hi => by rcases H with H | H <;> simp [H i hi]
    simp [sum_eq_zero this]
  by_cases H' : (∑ i ∈ s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i ∈ s, g i ^ q) ^ (1 / q) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ s, g i ≠ ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
      ENNReal.sum_eq_top, not_or] using H'
  have := ENNReal.coe_le_coe.2 (@NNReal.inner_le_Lp_mul_Lq _ s (fun i => ENNReal.toNNReal (f i))
    (fun i => ENNReal.toNNReal (g i)) _ _ hpq)
  simp [ENNReal.coe_rpow_of_nonneg, hpq.pos.le, hpq.symm.pos.le] at this
  convert! this using 1 <;> [skip; congr 2] <;> [skip; skip; simp; skip; simp] <;>
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [H'.1 i hi, H'.2 i hi, -WithZero.coe_mul]

/-- **Weighted Hölder inequality**. -/
/-
**ENNReal.inner_le_weight_mul_Lp_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : Real} (hp : 1 <= p) (
w f : ι -> Real>=0∞) : ∑ i in s, w i * f i <= (∑ i in s, w i) ^ (1 - p⁻¹) * (∑ i
 in s, w i * f i ^ p) ^ p⁻¹
参数：s : Finset ι；hp : 1 <= p；w f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
**Weighted Hölder inequality**.
-/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0∞) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  have hp₀ : 0 < p := by positivity
  have hp₁ : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  by_cases! H : (∑ i ∈ s, w i) ^ (1 - p⁻¹) = 0 ∨ (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ = 0
  · replace H : (∀ i ∈ s, w i = 0) ∨ ∀ i ∈ s, w i = 0 ∨ f i = 0 := by
      simpa [hp₀, hp₁, hp₀.not_gt, hp₁.not_gt, sum_eq_zero_iff_of_nonneg] using H
    have (i) (hi : i ∈ s) : w i * f i = 0 := by rcases H with H | H <;> simp [H i hi]
    simp [sum_eq_zero this]
  by_cases H' : (∑ i ∈ s, w i) ^ (1 - p⁻¹) = ⊤ ∨ (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (∀ i ∈ s, w i ≠ ⊤) ∧ ∀ i ∈ s, w i * f i ^ p ≠ ⊤ := by
    simpa [rpow_eq_top_iff, hp₀, hp₁, hp₀.not_gt, hp₁.not_gt, sum_eq_top, not_or] using H'
  have := coe_le_coe.2 <| NNReal.inner_le_weight_mul_Lp s hp.le (fun i ↦ ENNReal.toNNReal (w i))
    fun i ↦ ENNReal.toNNReal (f i)
  rw [coe_mul] at this
  simp_rw [coe_rpow_of_nonneg _ <| inv_nonneg.2 hp₀.le, ofNNReal_finsetSum, ← ENNReal.toNNReal_rpow,
    ← ENNReal.toNNReal_mul, sum_congr rfl fun i hi ↦ coe_toNNReal (H'.2 i hi)] at this
  simp only [toNNReal_mul, coe_mul, sub_nonneg, hp₁.le, coe_rpow_of_nonneg, ofNNReal_finsetSum]
    at this
  convert! this using 2 with i hi
  · obtain hw | hw := eq_or_ne (w i) 0
    · simp [hw]
    rw [coe_toNNReal (H'.1 _ hi), coe_toNNReal]
    simpa [mul_eq_top, hw, hp₀, hp₀.not_gt, H'.1 _ hi] using H'.2 _ hi
  · convert! rfl with i hi
    exact coe_toNNReal (H'.1 _ hi)

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0∞`-valued functions.
-/
/-
**ENNReal.rpow_sum_le_const_mul_sum_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_sum_le_const_mul_sum_rpow (hp : 1 <= p) : (∑ i in s, f i) ^ p <= (car
d s : Real>=0∞) ^ (p - 1) * ∑ i in s, f i ^ p
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.HolderConjugate.conjExponent`：∀ {p : ℝ}, 1 < p → p.HolderConjugate 
p.conjExponent
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `Real.HolderConjugate.div_conj_eq_sub_one`：div_conj_eq_sub_one : p / q = 
p - 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant
 times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0∞
`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (card s : ℝ≥0∞) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul, hp₁, hq, coe_one,
    one_mul, one_rpow, rpow_one, Pi.one_apply, sum_const, Nat.smul_one_eq_cast] using
    ENNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞`-valued nonnegative
functions. -/
/-
**ENNReal.Lp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：Lp_add_le (hp : 1 <= p) : (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <= (∑ i in
 s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p)
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `NNReal.Lp_add_le`：Lp_add_le (f g : ι -> Real>=0) {p : Real} (hp : 1 <= p
) : (∑ i in s, (f i + g i) ^ p) ^ (1 / p) <= (∑ i in s, f i ^ p) ^ (1 / p) + (∑ 
i in s…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less t
han or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞`-valued n
onnegative
functions.
-/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  by_cases H' : (∑ i ∈ s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i ∈ s, g i ^ p) ^ (1 / p) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div]
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ s, g i ≠ ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff, asymm pos, pos, ENNReal.sum_eq_top, not_or] using H'
  have :=
    ENNReal.coe_le_coe.2
      (@NNReal.Lp_add_le _ s (fun i => ENNReal.toNNReal (f i)) (fun i => ENNReal.toNNReal (g i)) _
        hp)
  push_cast [ENNReal.coe_rpow_of_nonneg, le_of_lt pos, le_of_lt (one_div_pos.2 pos)] at this
  simp_all

end ENNReal

end HoelderMinkowski

