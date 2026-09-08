/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Mean value inequalities

In this file we prove several mean inequalities for finite sums. Versions for integrals of some of
these inequalities are available in `MeasureTheory.MeanInequalities`.

## Main theorems: generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `Mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`zpow_arith_mean_le_arith_mean_zpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

public section


universe u v

open Finset NNReal ENNReal

noncomputable section

variable {ι : Type u} (s : Finset ι)

namespace Real

/-
**Real.pow_arith_mean_le_arith_mean_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pow_arith_mean_le_arith_mean_pow (w z : ι -> Real) (hw : forall i in s, 0 
<= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) (n : Nat) : (∑ 
i in s, w i * z i) ^ n <= ∑ i in s, w i * z i ^ n
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `convexOn_pow`：convexOn_pow : forall n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 => x
 ^ n
-/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
    (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n :=
  (convexOn_pow n).map_sum_le hw hw' hz
/-
**Real.pow_arith_mean_le_arith_mean_pow_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Real`
。
形式化陈述：pow_arith_mean_le_arith_mean_pow_of_even (w z : ι -> Real) (hw : forall i 
in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) {n : Nat} (hn : Even n) : (∑ i in s, w
 i * z i) ^ n <= ∑ i in s, w i * z i ^ n
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hn : Eve
n n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Even.convexOn_pow`：∀ {𝕜 : Type u_1} [inst : CommRing 𝕜] [inst_1 : Linear
Order 𝕜] [IsStrictOrderedRing 𝕜] {n : ℕ},   Even n → ConvexOn 𝕜 Set.univ fun x =
> x ^ n
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) {n : ℕ} (hn : Even n) :
    (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n :=
  hn.convexOn_pow.map_sum_le hw hw' fun _ _ => Set.mem_univ _
/-
**Real.zpow_arith_mean_le_arith_mean_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：zpow_arith_mean_le_arith_mean_zpow (w z : ι -> Real) (hw : forall i in s, 
0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 < z i) (m : Int) : (∑
 i in s, w i * z i) ^ m <= ∑ i in s, w i * z i ^ m
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 < z i；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `convexOn_zpow`：convexOn_zpow : forall n : Int, ConvexOn 𝕜 (Ioi 0) fun x 
: 𝕜 => x ^ n | (n : Nat) => by simp_rw [zpow_natCast] exact (convexOn_pow n).sub
set…
-/
theorem zpow_arith_mean_le_arith_mean_zpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
    (∑ i ∈ s, w i * z i) ^ m ≤ ∑ i ∈ s, w i * z i ^ m :=
  (convexOn_zpow m).map_sum_le hw hw' hz
/-
**Real.rpow_arith_mean_le_arith_mean_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_arith_mean_le_arith_mean_rpow (w z : ι -> Real) (hw : forall i in s, 
0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) {p : Real} (h
p : 1 <= p) : (∑ i in s, w i * z i) ^ p <= ∑ i in s, w i * z i ^ p
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `convexOn_rpow`：convexOn_rpow {p : Real} (hp : 1 <= p) : ConvexOn Real (I
ci 0) fun x : Real => x ^ p
-/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  (convexOn_rpow hp).map_sum_le hw hw' hz
/-
**Real.arith_mean_le_rpow_mean** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arith_mean_le_rpow_mean (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (
hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 <= z i) {p : Real} (hp : 1 <= p)
 : ∑ i in s, w i * z i <= (∑ i in s, w i * z i ^ p) ^ (1 / p)
参数：w z : ι -> Real；hw : forall i in s, 0 <= w i；hw' : ∑ i in s, w i = 1；hz : for
all i in s, 0 <= z i；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_arith_mean_le_arith_mean_rpow`：rpow_arith_mean_le_arith_mean_r
pow (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (
hz : forall i in s, 0 <= z i)…
-/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, w i * z i ≤ (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) := by
  have : 0 < p := by positivity
  rw [← rpow_le_rpow_iff _ _ this, ← rpow_mul, one_div_mul_cancel (ne_of_gt this), rpow_one]
  · exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
  all_goals
    apply_rules [sum_nonneg, rpow_nonneg]
    intro i hi
    positivity [hw i hi, hz i hi]

end Real

namespace NNReal

/-- Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-valued
functions and natural exponent. -/
/-
**NNReal.pow_arith_mean_le_arith_mean_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：pow_arith_mean_le_arith_mean_pow (w z : ι -> Real>=0) (hw' : ∑ i in s, w i
 = 1) (n : Nat) : (∑ i in s, w i * z i) ^ n <= ∑ i in s, w i * z i ^ n
参数：w z : ι -> Real>=0；hw' : ∑ i in s, w i = 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.pow_arith_mean_le_arith_mean_pow`：pow_arith_mean_le_arith_mean_pow 
(w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz :
 forall i in s, 0 <= z i) (…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-
valued
functions and natural exponent.
-/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) (n : ℕ) :
    (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n :=
  mod_cast
    Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) n

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
/-
**NNReal.rpow_arith_mean_le_arith_mean_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_arith_mean_le_arith_mean_rpow (w z : ι -> Real>=0) (hw' : ∑ i in s, w
 i = 1) {p : Real} (hp : 1 <= p) : (∑ i in s, w i * z i) ^ p <= ∑ i in s, w i * 
z i ^ p
参数：w z : ι -> Real>=0；hw' : ∑ i in s, w i = 1；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_arith_mean_le_arith_mean_rpow`：rpow_arith_mean_le_arith_mean_r
pow (w z : ι -> Real) (hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (
hz : forall i in s, 0 <= z i)…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
Weighted generalized mean inequality, version for sums over finite sets, with `ℝ
≥0`-valued
functions and real exponents.
-/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ}
    (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  mod_cast
    Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
      (mod_cast hw') (fun i _ => (z i).coe_nonneg) hp

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
/-
**NNReal.rpow_arith_mean_le_arith_mean2_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : Real>=0) (hw' : w₁ + w₂
 = 1) {p : Real} (hp : 1 <= p) : (w₁ * z₁ + w₂ * z₂) ^ p <= w₁ * z₁ ^ p + w₂ * z
₂ ^ p
参数：w₁ w₂ z₁ z₂ : Real>=0；hw' : w₁ + w₂ = 1；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.rpow_arith_mean_le_arith_mean_rpow`：rpow_arith_mean_le_arith_mean
_rpow (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) {p : Real} (hp : 1 <= p) : 
(∑ i in s, w i * z i) ^ p <= ∑ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real
 exponents.
-/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0) (hw' : w₁ + w₂ = 1) {p : ℝ}
    (hp : 1 ≤ p) : (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p := by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

/-- Unweighted mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
/-
**NNReal.rpow_add_le_mul_rpow_add_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : Real>=0) {p : Real} (hp : 1 <= p) :
 (z₁ + z₂) ^ p <= (2 : Real>=0) ^ (p - 1) * (z₁ ^ p + z₂ ^ p)
参数：z₁ z₂ : Real>=0；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `NNReal.rpow_sub'`：rpow_sub' (h : y - z != 0) (x : Real>=0) : x ^ (y - z)
 = x ^ y / x ^ z
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
Unweighted mean inequality, version for two elements of `ℝ≥0` and real exponents
.
-/
theorem rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (z₁ + z₂) ^ p ≤ (2 : ℝ≥0) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) := by
  rcases eq_or_lt_of_le hp with (rfl | h'p)
  · simp only [rpow_one, sub_self, rpow_zero, one_mul]; rfl
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (add_halves 1) hp using 1
  · simp only [one_div, inv_mul_cancel_left₀, Ne, two_ne_zero,
      not_false_iff]
  · have A : p - 1 ≠ 0 := ne_of_gt (sub_pos.2 h'p)
    simp only [mul_rpow, rpow_sub' A, rpow_one]
    ring

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
/-
**NNReal.arith_mean_le_rpow_mean** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：arith_mean_le_rpow_mean (w z : ι -> Real>=0) (hw' : ∑ i in s, w i = 1) {p 
: Real} (hp : 1 <= p) : ∑ i in s, w i * z i <= (∑ i in s, w i * z i ^ p) ^ (1 / 
p)
参数：w z : ι -> Real>=0；hw' : ∑ i in s, w i = 1；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.arith_mean_le_rpow_mean`：arith_mean_le_rpow_mean (w z : ι -> Real) 
(hw : forall i in s, 0 <= w i) (hw' : ∑ i in s, w i = 1) (hz : forall i in s, 0 
<= z i) {p : Real}…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r

--- 原说明 ---
Weighted generalized mean inequality, version for sums over finite sets, with `ℝ
≥0`-valued
functions and real exponents.
-/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, w i * z i ≤ (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) :=
  mod_cast
    Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg) (mod_cast hw')
      (fun i _ => (z i).coe_nonneg) hp
/-
**NNReal.add_rpow_le_one_of_add_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_rpow_le_one_of_add_le_one {p : ℝ} (a b : ℝ≥0) (hab : a + b ≤ 1) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ 1 := by
  have h_le_one : ∀ x : ℝ≥0, x ≤ 1 → x ^ p ≤ x := fun x hx => rpow_le_self_of_le_one hx hp1
  have ha : a ≤ 1 := (self_le_add_right a b).trans hab
  have hb : b ≤ 1 := (self_le_add_left b a).trans hab
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab
/-
**NNReal.add_rpow_le_rpow_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：add_rpow_le_rpow_add {p : Real} (a b : Real>=0) (hp1 : 1 <= p) : a ^ p + b
 ^ p <= (a + b) ^ p
参数：a b : Real>=0；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `_private.Mathlib.Analysis.MeanInequalitiesPow.0.NNReal.add_rpow_le_one_o
f_add_le_one`：∀ {p : ℝ} (a b : NNReal), a + b ≤ 1 → 1 ≤ p → a ^ p + b ^ p ≤ 1
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NNReal.div_rpow`：div_rpow (x y : Real>=0) (z : Real) : (x / y) ^ z = x ^
 z / y ^ z
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
（共 35 条，此处仅展示前 30 条）
-/
theorem add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) : a ^ p + b ^ p ≤ (a + b) ^ p := by
  have hp_pos : 0 < p := by positivity
  by_cases h_zero : a + b = 0
  · simp [add_eq_zero.mp h_zero, hp_pos.ne']
  have h_nonzero : ¬(a = 0 ∧ b = 0) := by rwa [add_eq_zero] at h_zero
  have h_add : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h_zero]
  have h := add_rpow_le_one_of_add_le_one (a / (a + b)) (b / (a + b)) h_add.le hp1
  rw [div_rpow a (a + b), div_rpow b (a + b)] at h
  have hab_0 : (a + b) ^ p ≠ 0 := by simp [h_nonzero]
  have h_mul : (a + b) ^ p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) ≤ (a + b) ^ p := by
    nth_rw 4 [← mul_one ((a + b) ^ p)]; gcongr
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a ^ p), mul_comm (b ^ p), ← mul_assoc, ←
    mul_assoc, mul_inv_cancel₀ hab_0, one_mul, one_mul] at h_mul
/-
**NNReal.rpow_add_rpow_le_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_rpow_le_add {p : Real} (a b : Real>=0) (hp1 : 1 <= p) : (a ^ p + 
b ^ p) ^ (1 / p) <= a + b
参数：a b : Real>=0；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `NNReal.add_rpow_le_rpow_add`：add_rpow_le_rpow_add {p : Real} (a b : Real
>=0) (hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p
-/
theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b := by
  rw [one_div,
    ← @NNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1]), inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1
/-
**NNReal.rpow_add_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_rpow_le {p q : Real} (a b : Real>=0) (hp_pos : 0 < p) (hpq : p <=
 q) : (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ (1 / p)
参数：a b : Real>=0；hp_pos : 0 < p；hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NNReal.rpow_add_rpow_le_add`：rpow_add_rpow_le_add {p : Real} (a b : Real
>=0) (hp1 : 1 <= p) : (a ^ p + b ^ p) ^ (1 / p) <= a + b
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `one_div_div`：one_div_div : 1 / (a / b) = b / a
-/
theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0) (hp_pos : 0 < p) (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) := by
  have h_rpow : ∀ a : ℝ≥0, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← NNReal.rpow_mul, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hp_pos.ne.symm,
      one_mul]
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) ≤ a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a, h_rpow b, one_div p, NNReal.le_rpow_inv_iff hp_pos, ← NNReal.rpow_mul, mul_comm,
    mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add
/-
**NNReal.rpow_add_le_add_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_le_add_rpow {p : Real} (a b : Real>=0) (hp : 0 <= p) (hp1 : p <= 
1) : (a + b) ^ p <= a ^ p + b ^ p
参数：a b : Real>=0；hp : 0 <= p；hp1 : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NNReal.rpow_add_rpow_le`：rpow_add_rpow_le {p q : Real} (a b : Real>=0) (
hp_pos : 0 < p) (hpq : p <= q) : (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ 
(1 / p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `one_div_one`：one_div_one : (1 : G) / 1 = 1
-/
theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one, one_div] at h
  repeat' rw [NNReal.rpow_one] at h
  exact (NNReal.le_rpow_inv_iff hp_pos).mp h

end NNReal

namespace Real

/-
**Real.add_rpow_le_rpow_add** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：add_rpow_le_rpow_add {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (
hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p
参数：ha : 0 <= a；hb : 0 <= b；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.add_rpow_le_rpow_add`：add_rpow_le_rpow_add {p : Real} (a b : Real
>=0) (hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p
-/
lemma add_rpow_le_rpow_add {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) :
     a ^ p + b ^ p ≤ (a + b) ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.add_rpow_le_rpow_add a b hp1
/-
**Real.rpow_add_rpow_le_add** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_rpow_le_add {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (
hp1 : 1 <= p) : (a ^ p + b ^ p) ^ (1 / p) <= a + b
参数：ha : 0 <= a；hb : 0 <= b；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.rpow_add_rpow_le_add`：rpow_add_rpow_le_add {p : Real} (a b : Real
>=0) (hp1 : 1 <= p) : (a ^ p + b ^ p) ^ (1 / p) <= a + b
-/
lemma rpow_add_rpow_le_add {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le_add a b hp1
/-
**Real.rpow_add_rpow_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_rpow_le {p q : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hp
_pos : 0 < p) (hpq : p <= q) : (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ (1
 / p)
参数：ha : 0 <= a；hb : 0 <= b；hp_pos : 0 < p；hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.rpow_add_rpow_le`：rpow_add_rpow_le {p q : Real} (a b : Real>=0) (
hp_pos : 0 < p) (hpq : p <= q) : (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ 
(1 / p)
-/
lemma rpow_add_rpow_le {p q : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp_pos : 0 < p)
    (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_rpow_le a b hp_pos hpq
/-
**Real.rpow_add_le_add_rpow** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_le_add_rpow {p : Real} {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (
hp : 0 <= p) (hp1 : p <= 1) : (a + b) ^ p <= a ^ p + b ^ p
参数：ha : 0 <= a；hb : 0 <= b；hp : 0 <= p；hp1 : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_add_le_add_rpow`：rpow_add_le_add_rpow {p : Real} (a b : Real
>=0) (hp : 0 <= p) (hp1 : p <= 1) : (a + b) ^ p <= a ^ p + b ^ p
-/
lemma rpow_add_le_add_rpow {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_add_rpow a b hp hp1

end Real

namespace ENNReal

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0∞`-valued
functions and real exponents. -/
/-
**ENNReal.rpow_arith_mean_le_arith_mean_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`
。
形式化陈述：rpow_arith_mean_le_arith_mean_rpow (w z : ι -> Real>=0∞) (hw' : ∑ i in s, 
w i = 1) {p : Real} (hp : 1 <= p) : (∑ i in s, w i * z i) ^ p <= ∑ i in s, w i *
 z i ^ p
参数：w z : ι -> Real>=0∞；hw' : ∑ i in s, w i = 1；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ENNReal.le_of_top_imp_top_of_toNNReal_le`：le_of_top_imp_top_of_toNNReal_
le {a b : Real>=0∞} (h : a = ⊤ -> b = ⊤) (h_nnreal : a != ⊤ -> b != ⊤ -> a.toNNR
eal <= b.toNNReal) : a <= b
· 使用定理 `ENNReal.rpow_eq_top_iff`：rpow_eq_top_iff {x : Real>=0∞} {y : Real} : x ^
 y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y
· 使用定理 `ENNReal.sum_eq_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 x ∈ s, f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.lt_top_of_sum_ne_top`：lt_top_of_sum_ne_top {s : Finset α} {f : α
 -> Real>=0∞} (h : ∑ x in s, f x != ∞) {a : α} (ha : a in s) : f a < ∞
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toNNReal_sum`：toNNReal_sum {s : Finset α} {f : α -> Real>=0∞} (h
f : forall a in s, f a != ∞) : ENNReal.toNNReal (∑ a in s, f a) = ∑ a in s, ENNR
eal.toNNRe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toNNReal_rpow`：∀ (x : ENNReal) (z : ℝ), (x ^ z).toNNReal = x.toN
NReal ^ z
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Weighted generalized mean inequality, version for sums over finite sets, with `ℝ
≥0∞`-valued
functions and real exponents.
-/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0∞) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ}
    (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p := by
  have hp_pos : 0 < p := by positivity
  have hp_nonneg : 0 ≤ p := by positivity
  have hp_not_neg : ¬p < 0 := by simp [hp_nonneg]
  have h_top_iff_rpow_top : ∀ (i : ι), i ∈ s → (w i * z i = ⊤ ↔ w i * z i ^ p = ⊤) := by
    simp [ENNReal.mul_eq_top, hp_pos, hp_not_neg]
  refine le_of_top_imp_top_of_toNNReal_le ?_ ?_
  · -- first, prove `(∑ i ∈ s, w i * z i) ^ p = ⊤ → ∑ i ∈ s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff, sum_eq_top, sum_eq_top]
    grind
  · -- second, suppose both `(∑ i ∈ s, w i * z i) ^ p ≠ ⊤` and `∑ i ∈ s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i ∈ s, w i * z i) ^ p).toNNReal ≤ (∑ i ∈ s, (w i * z i ^ p)).toNNReal`,
    -- by using `NNReal.rpow_arith_mean_le_arith_mean_rpow`.
    intro h_top_rpow_sum _
    -- show hypotheses needed to put the `.toNNReal` inside the sums.
    have h_top : ∀ a : ι, a ∈ s → w a * z a ≠ ⊤ :=
      haveI h_top_sum : ∑ i ∈ s, w i * z i ≠ ⊤ := by
        intro h
        rw [h, top_rpow_of_pos hp_pos] at h_top_rpow_sum
        exact h_top_rpow_sum rfl
      fun a ha => (lt_top_of_sum_ne_top h_top_sum ha).ne
    have h_top_rpow : ∀ a : ι, a ∈ s → w a * z a ^ p ≠ ⊤ := by
      intro i hi
      specialize h_top i hi
      rwa [Ne, ← h_top_iff_rpow_top i hi]
    -- put the `.toNNReal` inside the sums.
    simp_rw [toNNReal_sum h_top_rpow, toNNReal_rpow, toNNReal_sum h_top, toNNReal_mul,
      toNNReal_rpow]
    -- use corresponding nnreal result
    refine
      NNReal.rpow_arith_mean_le_arith_mean_rpow s (fun i => (w i).toNNReal)
        (fun i => (z i).toNNReal) ?_ hp
    -- verify the hypothesis `∑ i ∈ s, (w i).toNNReal = 1`, using `∑ i ∈ s, w i = 1` .
    have h_sum_nnreal : ∑ i ∈ s, w i = ↑(∑ i ∈ s, (w i).toNNReal) := by
      push_cast
      congr! with i hi
      refine (coe_toNNReal (lt_top_of_sum_ne_top ?_ hi).ne).symm
      exact hw'.symm ▸ ENNReal.one_ne_top
    rwa [← coe_inj, ← h_sum_nnreal]

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0∞` and real
exponents. -/
/-
**ENNReal.rpow_arith_mean_le_arith_mean2_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : Real>=0∞) (hw' : w₁ + w
₂ = 1) {p : Real} (hp : 1 <= p) : (w₁ * z₁ + w₂ * z₂) ^ p <= w₁ * z₁ ^ p + w₂ * 
z₂ ^ p
参数：w₁ w₂ z₁ z₂ : Real>=0∞；hw' : w₁ + w₂ = 1；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.rpow_arith_mean_le_arith_mean_rpow`：rpow_arith_mean_le_arith_mea
n_rpow (w z : ι -> Real>=0∞) (hw' : ∑ i in s, w i = 1) {p : Real} (hp : 1 <= p) 
: (∑ i in s, w i * z i) ^ p <= ∑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Weighted generalized mean inequality, version for two elements of `ℝ≥0∞` and rea
l
exponents.
-/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0∞) (hw' : w₁ + w₂ = 1) {p : ℝ}
    (hp : 1 ≤ p) : (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p := by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] ?_ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]

/-- Unweighted mean inequality, version for two elements of `ℝ≥0∞` and real exponents. -/
/-
**ENNReal.rpow_add_le_mul_rpow_add_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : Real>=0∞) {p : Real} (hp : 1 <= p) 
: (z₁ + z₂) ^ p <= (2 : Real>=0∞) ^ (p - 1) * (z₁ ^ p + z₂ ^ p)
参数：z₁ z₂ : Real>=0∞；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.rpow_sub`：rpow_sub {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'
x : x != ⊤) : x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Unweighted mean inequality, version for two elements of `ℝ≥0∞` and real exponent
s.
-/
theorem rpow_add_le_mul_rpow_add_rpow (z₁ z₂ : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (z₁ + z₂) ^ p ≤ (2 : ℝ≥0∞) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) := by
  convert!
    rpow_arith_mean_le_arith_mean2_rpow (1 / 2) (1 / 2) (2 * z₁) (2 * z₂) (ENNReal.add_halves 1) hp
      using 1
  · simp [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  · simp only [mul_rpow_of_nonneg _ _ (zero_le_one.trans hp), rpow_sub _ _ two_ne_zero ofNat_ne_top,
      ENNReal.div_eq_inv_mul, rpow_one, mul_one]
    ring
/-
**ENNReal.add_rpow_le_rpow_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_rpow_le_rpow_add {p : Real} (a b : Real>=0∞) (hp1 : 1 <= p) : a ^ p + 
b ^ p <= (a + b) ^ p
参数：a b : Real>=0∞；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_eq_top_iff_of_pos`：rpow_eq_top_iff_of_pos {x : Real>=0∞} {y
 : Real} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `NNReal.add_rpow_le_rpow_add`：add_rpow_le_rpow_add {p : Real} (a b : Real
>=0) (hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p
-/
theorem add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) : a ^ p + b ^ p ≤ (a + b) ^ p := by
  have hp_pos : 0 < p := by positivity
  by_cases h_top : a + b = ⊤
  · rw [← @ENNReal.rpow_eq_top_iff_of_pos (a + b) p hp_pos] at h_top
    rw [h_top]
    exact le_top
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top
  lift a to ℝ≥0 using ha_top
  lift b to ℝ≥0 using hb_top
  simpa [ENNReal.coe_rpow_of_nonneg _ hp_pos.le] using
    ENNReal.coe_le_coe.2 (NNReal.add_rpow_le_rpow_add a b hp1)
/-
**ENNReal.rpow_add_rpow_le_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_rpow_le_add {p : Real} (a b : Real>=0∞) (hp1 : 1 <= p) : (a ^ p +
 b ^ p) ^ (1 / p) <= a + b
参数：a b : Real>=0∞；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.add_rpow_le_rpow_add`：add_rpow_le_rpow_add {p : Real} (a b : Rea
l>=0∞) (hp1 : 1 <= p) : a ^ p + b ^ p <= (a + b) ^ p
-/
theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b := by
  rw [one_div, ← @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [inv_inv]
  exact add_rpow_le_rpow_add _ _ hp1
/-
**ENNReal.rpow_add_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_rpow_le {p q : Real} (a b : Real>=0∞) (hp_pos : 0 < p) (hpq : p <
= q) : (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) ^ (1 / p)
参数：a b : Real>=0∞；hp_pos : 0 < p；hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_add_rpow_le_add`：rpow_add_rpow_le_add {p : Real} (a b : Rea
l>=0∞) (hp1 : 1 <= p) : (a ^ p + b ^ p) ^ (1 / p) <= a + b
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `one_div_div`：one_div_div : 1 / (a / b) = b / a
-/
theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0∞) (hp_pos : 0 < p) (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) := by
  have h_rpow : ∀ a : ℝ≥0∞, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hp_pos.ne']
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) ≤ a ^ p + b ^ p := by
    refine rpow_add_rpow_le_add (a ^ p) (b ^ p) ?_
    rwa [one_le_div hp_pos]
  rw [h_rpow a, h_rpow b, one_div p, ENNReal.le_rpow_inv_iff hp_pos, ← ENNReal.rpow_mul, mul_comm,
    mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add
/-
**ENNReal.rpow_add_le_add_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_le_add_rpow {p : Real} (a b : Real>=0∞) (hp : 0 <= p) (hp1 : p <=
 1) : (a + b) ^ p <= a ^ p + b ^ p
参数：a b : Real>=0∞；hp : 0 <= p；hp1 : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.rpow_add_rpow_le`：rpow_add_rpow_le {p q : Real} (a b : Real>=0∞)
 (hp_pos : 0 < p) (hpq : p <= q) : (a ^ q + b ^ q) ^ (1 / q) <= (a ^ p + b ^ p) 
^ (1 / p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `one_div_one`：one_div_one : (1 : G) / 1 = 1
-/
theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one, one_div] at h
  repeat' rw [ENNReal.rpow_one] at h
  exact (ENNReal.le_rpow_inv_iff hp_pos).mp h

/-- A constant for the inequality `‖f + g‖_{L^p} ≤ C * (‖f‖_{L^p} + ‖g‖_{L^p})`. It is equal to `1`
for `p ≥ 1` or `p = 0`, and `2^(1/p-1)` in the more tricky interval `(0, 1)`. -/
/-
**ENNReal.LpAddConst** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ENNReal → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant for the inequality `‖f + g‖_{L^p} ≤ C * (‖f‖_{L^p} + ‖g‖_{L^p})`. It 
is equal to `1`
for `p ≥ 1` or `p = 0`, and `2^(1/p-1)` in the more tricky interval `(0, 1)`.
-/
@[expose] noncomputable def LpAddConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p ∈ Set.Ioo (0 : ℝ≥0∞) 1 then (2 : ℝ≥0∞) ^ (1 / p.toReal - 1) else 1
/-
**ENNReal.LpAddConst_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：LpAddConst_of_one_le {p : Real>=0∞} (hp : 1 <= p) : LpAddConst p = 1
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.LpAddConst.eq_1`：∀ (p : ENNReal), p.LpAddConst = if p ∈ Set.Ioo 
0 1 then 2 ^ (1 / p.toReal - 1) else 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem LpAddConst_of_one_le {p : ℝ≥0∞} (hp : 1 ≤ p) : LpAddConst p = 1 := by
  rw [LpAddConst, if_neg]
  intro h
  exact lt_irrefl _ (h.2.trans_le hp)
/-
**ENNReal.LpAddConst_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：LpAddConst_zero : LpAddConst 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.LpAddConst.eq_1`：∀ (p : ENNReal), p.LpAddConst = if p ∈ Set.Ioo 
0 1 then 2 ^ (1 / p.toReal - 1) else 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem LpAddConst_zero : LpAddConst 0 = 1 := by
  rw [LpAddConst, if_neg]
  intro h
  exact lt_irrefl _ h.1
/-
**ENNReal.LpAddConst_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：LpAddConst_lt_top (p : Real>=0∞) : LpAddConst p < ∞
参数：p : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.LpAddConst.eq_1`：∀ (p : ENNReal), p.LpAddConst = if p ∈ Set.Ioo 
0 1 then 2 ^ (1 / p.toReal - 1) else 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.one_le_inv`：∀ {a : ENNReal}, 1 ≤ a⁻¹ ↔ a ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
-/
theorem LpAddConst_lt_top (p : ℝ≥0∞) : LpAddConst p < ∞ := by
  rw [LpAddConst]
  split_ifs with h
  · apply ENNReal.rpow_lt_top_of_nonneg _ ENNReal.ofNat_ne_top
    rw [one_div, sub_nonneg, ← ENNReal.toReal_inv, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simpa using h.1.ne') (ENNReal.one_le_inv.2 h.2.le)
  · exact ENNReal.one_lt_top

/-- Variant of `ENNReal.rpow_add_le_mul_rpow_add_rpow` using `LpAddConst` as the constant,
valid for all `0 ≤ p` (not just `1 ≤ p`). -/
/-
**ENNReal.rpow_add_le_mul_rpow_add_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_le_mul_rpow_add_rpow' (z₁ z₂ : Real>=0∞) {p : Real} (hp : 0 <= p)
 : (z₁ + z₂) ^ p <= LpAddConst (ENNReal.ofReal p)⁻¹ * (z₁ ^ p + z₂ ^ p)
参数：z₁ z₂ : Real>=0∞；hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.inv_lt_one`：∀ {a : ENNReal}, a⁻¹ < 1 ↔ 1 < a
· 使用引理 `ENNReal.one_lt_ofReal`：one_lt_ofReal {r : Real} : 1 < ENNReal.ofReal r ↔
 1 < r
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.LpAddConst.eq_1`：∀ (p : ENNReal), p.LpAddConst = if p ∈ Set.Ioo 
0 1 then 2 ^ (1 / p.toReal - 1) else 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `ENNReal.rpow_add_le_mul_rpow_add_rpow`：rpow_add_le_mul_rpow_add_rpow (z₁
 z₂ : Real>=0∞) {p : Real} (hp : 1 <= p) : (z₁ + z₂) ^ p <= (2 : Real>=0∞) ^ (p 
- 1) * (z₁ ^ p + z₂ ^ p)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `ENNReal.LpAddConst_of_one_le`：LpAddConst_of_one_le {p : Real>=0∞} (hp : 
1 <= p) : LpAddConst p = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.one_le_inv`：∀ {a : ENNReal}, 1 ≤ a⁻¹ ↔ a ≤ 1
· 使用引理 `ENNReal.ofReal_le_one`：ofReal_le_one {r : Real} : ENNReal.ofReal r <= 1 
↔ r <= 1
· 使用定理 `ENNReal.rpow_add_le_add_rpow`：rpow_add_le_add_rpow {p : Real} (a b : Rea
l>=0∞) (hp : 0 <= p) (hp1 : p <= 1) : (a + b) ^ p <= a ^ p + b ^ p

--- 原说明 ---
Variant of `ENNReal.rpow_add_le_mul_rpow_add_rpow` using `LpAddConst` as the con
stant,
valid for all `0 ≤ p` (not just `1 ≤ p`).
-/
theorem rpow_add_le_mul_rpow_add_rpow' (z₁ z₂ : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) :
    (z₁ + z₂) ^ p ≤ LpAddConst (ENNReal.ofReal p)⁻¹ * (z₁ ^ p + z₂ ^ p) := by
  by_cases h : 1 < p
  · have hmem : (ENNReal.ofReal p)⁻¹ ∈ Set.Ioo (0 : ℝ≥0∞) 1 := by
      constructor
      · simp
      · rwa [ENNReal.inv_lt_one, one_lt_ofReal]
    rw [show LpAddConst (ENNReal.ofReal p)⁻¹ =
        (2 : ℝ≥0∞) ^ (1 / ((ENNReal.ofReal p)⁻¹).toReal - 1) by
      rw [LpAddConst, if_pos hmem]]
    simp only [ENNReal.toReal_inv, div_inv_eq_mul, one_mul]
    rw [ENNReal.toReal_ofReal hp]
    exact rpow_add_le_mul_rpow_add_rpow _ _ h.le
  · have hp1 : p ≤ 1 := not_lt.mp h
    rw [LpAddConst_of_one_le (ENNReal.one_le_inv.mpr (ENNReal.ofReal_le_one.mpr hp1)), one_mul]
    exact rpow_add_le_add_rpow _ _ hp hp1

/-- Variant of `ENNReal.rpow_add_le_mul_rpow_add_rpow'` with `p : ℝ≥0∞`. -/
/-
**ENNReal.rpow_add_le_mul_rpow_add_rpow''** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_le_mul_rpow_add_rpow'' (z₁ z₂ : Real>=0∞) {p : Real>=0∞} : (z₁ + 
z₂) ^ p.toReal⁻¹ <= LpAddConst p * (z₁ ^ p.toReal⁻¹ + z₂ ^ p.toReal⁻¹)
参数：z₁ z₂ : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.LpAddConst_zero`：LpAddConst_zero : LpAddConst 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.rpow_add_le_mul_rpow_add_rpow'`：rpow_add_le_mul_rpow_add_rpow' (
z₁ z₂ : Real>=0∞) {p : Real} (hp : 0 <= p) : (z₁ + z₂) ^ p <= LpAddConst (ENNRea
l.ofReal p)⁻¹ * (z₁ ^ p + z₂…
· 使用定理 `inv_nonneg_of_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_
1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a → 0 ≤ a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal

--- 原说明 ---
Variant of `ENNReal.rpow_add_le_mul_rpow_add_rpow'` with `p : ℝ≥0∞`.
-/
theorem rpow_add_le_mul_rpow_add_rpow'' (z₁ z₂ : ℝ≥0∞) {p : ℝ≥0∞} :
    (z₁ + z₂) ^ p.toReal⁻¹ ≤
      LpAddConst p * (z₁ ^ p.toReal⁻¹ + z₂ ^ p.toReal⁻¹) := by
  by_cases p_zero : p = 0
  · simp [p_zero, LpAddConst_zero]
  convert rpow_add_le_mul_rpow_add_rpow' z₁ z₂ (p := p.toReal⁻¹) (by positivity)
  rw [← ENNReal.toReal_inv, ENNReal.ofReal_toReal (by simpa), inv_inv]

end ENNReal

