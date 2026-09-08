/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.FloorPow
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The strong law of large numbers

We prove the strong law of large numbers, in `ProbabilityTheory.strong_law_ae`:
If `X n` is a sequence of independent identically distributed integrable random
variables, then `∑ i ∈ range n, X i / n` converges almost surely to `𝔼[X 0]`.
We give here the strong version, due to Etemadi, that only requires pairwise independence.

This file also contains the Lᵖ version of the strong law of large numbers provided by
`ProbabilityTheory.strong_law_Lp` which shows `∑ i ∈ range n, X i / n` converges in Lᵖ to
`𝔼[X 0]` provided `X n` is independent identically distributed and is Lᵖ.

## Implementation

The main point is to prove the result for real-valued random variables, as the general case
of Banach-space-valued random variables follows from this case and approximation by simple
functions. The real version is given in `ProbabilityTheory.strong_law_ae_real`.

We follow the proof by Etemadi
[Etemadi, *An elementary proof of the strong law of large numbers*][etemadi_strong_law],
which goes as follows.

It suffices to prove the result for nonnegative `X`, as one can prove the general result by
splitting a general `X` into its positive part and negative part.
Consider `Xₙ` a sequence of nonnegative integrable identically distributed pairwise independent
random variables. Let `Yₙ` be the truncation of `Xₙ` up to `n`. We claim that
* Almost surely, `Xₙ = Yₙ` for all but finitely many indices. Indeed, `∑ ℙ (Xₙ ≠ Yₙ)` is bounded by
  `1 + 𝔼[X]` (see `sum_prob_mem_Ioc_le` and `tsum_prob_mem_Ioi_lt_top`).
* Let `c > 1`. Along the sequence `n = c ^ k`, then `(∑_{i=0}^{n-1} Yᵢ - 𝔼[Yᵢ])/n` converges almost
  surely to `0`. This follows from a variance control, as
  ```
  ∑_k ℙ (|∑_{i=0}^{c^k - 1} Yᵢ - 𝔼[Yᵢ]| > c^k ε)
    ≤ ∑_k (c^k ε)^{-2} ∑_{i=0}^{c^k - 1} Var[Yᵢ]    (by Markov inequality)
    ≤ ∑_i (C/i^2) Var[Yᵢ]                           (as ∑_{c^k > i} 1/(c^k)^2 ≤ C/i^2)
    ≤ ∑_i (C/i^2) 𝔼[Yᵢ^2]
    ≤ 2C 𝔼[X^2]                                     (see `sum_variance_truncation_le`)
  ```
* As `𝔼[Yᵢ]` converges to `𝔼[X]`, it follows from the two previous items and Cesàro that, along
  the sequence `n = c^k`, one has `(∑_{i=0}^{n-1} Xᵢ) / n → 𝔼[X]` almost surely.
* To generalize it to all indices, we use the fact that `∑_{i=0}^{n-1} Xᵢ` is nondecreasing and
  that, if `c` is close enough to `1`, the gap between `c^k` and `c^(k+1)` is small.
-/

@[expose] public section


noncomputable section

open MeasureTheory Filter Finset Asymptotics

open Set (indicator)

open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal

open scoped Function -- required for scoped `on` notation

namespace ProbabilityTheory

/-! ### Prerequisites on truncations -/


section Truncation

variable {α : Type*}

/-- Truncating a real-valued function to the interval `(-A, A]`. -/
/-
**ProbabilityTheory.truncation** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：truncation (f : α -> Real) (A : Real)
参数：f : α -> Real；A : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Truncating a real-valued function to the interval `(-A, A]`.
-/
def truncation (f : α → ℝ) (A : ℝ) :=
  indicator (Set.Ioc (-A) A) id ∘ f

variable {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.truncation** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.truncation (hf : AEStronglyMeasurable f μ)
    {A : ℝ} : AEStronglyMeasurable (truncation f A) μ := by
  apply AEStronglyMeasurable.comp_aemeasurable _ hf.aemeasurable
  exact (stronglyMeasurable_id.indicator measurableSet_Ioc).aestronglyMeasurable
/-
**ProbabilityTheory.abs_truncation_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：abs_truncation_le_bound (f : α -> Real) (A : Real) (x : α) : |truncation f
 A x| <= |A|
参数：f : α -> Real；A : Real；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `abs_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 b : α}, a ≤ b → -a ≤ b → |a| ≤ |b|
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
-/
theorem abs_truncation_le_bound (f : α → ℝ) (A : ℝ) (x : α) : |truncation f A x| ≤ |A| := by
  simp only [truncation, Set.indicator, id, Function.comp_apply]
  split_ifs with h
  · exact abs_le_abs h.2 (neg_le.2 h.1.le)
  · simp [abs_nonneg]

@[simp]
/-
**ProbabilityTheory.truncation_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：truncation_zero (f : α -> Real) : truncation f 0 = 0
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.indicator_empty`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f 
: α → M), ∅.indicator f = fun x => 0
-/
theorem truncation_zero (f : α → ℝ) : truncation f 0 = 0 := by simp [truncation]; rfl
/-
**ProbabilityTheory.abs_truncation_le_abs_self** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：abs_truncation_le_abs_self (f : α -> Real) (A : Real) (x : α) : |truncatio
n f A x| <= |f x|
参数：f : α -> Real；A : Real；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem abs_truncation_le_abs_self (f : α → ℝ) (A : ℝ) (x : α) : |truncation f A x| ≤ |f x| := by
  simp only [truncation, indicator, id, Function.comp_apply]
  split_ifs
  · exact le_rfl
  · simp [abs_nonneg]
/-
**ProbabilityTheory.truncation_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：truncation_eq_self {f : α -> Real} {A : Real} {x : α} (h : |f x| < A) : tr
uncation f A x = f x
参数：h : |f x| < A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem truncation_eq_self {f : α → ℝ} {A : ℝ} {x : α} (h : |f x| < A) :
    truncation f A x = f x := by
  simp only [truncation, indicator, id, Function.comp_apply, ite_eq_left_iff]
  intro H
  apply H.elim
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le]
/-
**ProbabilityTheory.truncation_eq_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：truncation_eq_of_nonneg {f : α -> Real} {A : Real} (h : forall x, 0 <= f x
) : truncation f A = indicator (Set.Ioc 0 A) id ∘ f
参数：h : forall x, 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 62 条，此处仅展示前 30 条）
-/
theorem truncation_eq_of_nonneg {f : α → ℝ} {A : ℝ} (h : ∀ x, 0 ≤ f x) :
    truncation f A = indicator (Set.Ioc 0 A) id ∘ f := by
  ext x
  rcases (h x).lt_or_eq with (hx | hx)
  · simp only [truncation, indicator, hx, Set.mem_Ioc, id, Function.comp_apply]
    by_cases h'x : f x ≤ A
    · have : -A < f x := by linarith [h x]
      simp only [this, true_and]
    · simp only [h'x, and_false]
  · simp only [truncation, indicator, hx, id, Function.comp_apply, ite_self]
/-
**ProbabilityTheory.truncation_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：truncation_nonneg {f : α -> Real} (A : Real) {x : α} (h : 0 <= f x) : 0 <=
 truncation f A x
参数：A : Real；h : 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_apply_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preo
rder M] [inst_1 : Zero M] {s : Set α} {f : α → M} {a : α},   (a ∈ s → 0 ≤ f a) →
 0 ≤ s.indicator…
-/
theorem truncation_nonneg {f : α → ℝ} (A : ℝ) {x : α} (h : 0 ≤ f x) : 0 ≤ truncation f A x :=
  Set.indicator_apply_nonneg fun _ => h
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation**
 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) {A : ℝ} {p : ℝ≥0∞} : MemLp (truncation f A) p μ :=
  MemLp.of_bound hf.truncation |A| (Eventually.of_forall fun _ => abs_truncation_le_bound _ _ _)
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integrable_truncat
ion** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integrable_truncation [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) {A : ℝ} : Integrable (truncation f A) μ := by
  rw [← memLp_one_iff_integrable]; exact hf.memLp_truncation
/-
**ProbabilityTheory.moment_truncation_eq_intervalIntegral** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：moment_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A :
 Real} (hA : 0 <= A) {n : Nat} (hn : n != 0) : ∫ x, truncation f A x ^ n ∂μ = ∫ 
y in -A..A, y ^ n ∂Measure.map f μ
参数：hf : AEStronglyMeasurable f μ；hA : 0 <= A；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 77 条，此处仅展示前 30 条）
-/
theorem moment_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : ℝ} (hA : 0 ≤ A)
    {n : ℕ} (hn : n ≠ 0) : ∫ x, truncation f A x ^ n ∂μ = ∫ y in -A..A, y ^ n ∂Measure.map f μ := by
  have M : MeasurableSet (Set.Ioc (-A) A) := measurableSet_Ioc
  change ∫ x, (fun z => indicator (Set.Ioc (-A) A) id z ^ n) (f x) ∂μ = _
  rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable, intervalIntegral.integral_of_le,
    ← integral_indicator M]
  · simp only [indicator, zero_pow hn, id, ite_pow]
  · linarith
  · exact ((measurable_id.indicator M).pow_const n).aestronglyMeasurable
/-
**ProbabilityTheory.moment_truncation_eq_intervalIntegral_of_nonneg** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：moment_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable
 f μ) {A : Real} {n : Nat} (hn : n != 0) (h'f : 0 <= f) : ∫ x, truncation f A x 
^ n ∂μ = ∫ y in 0..A, y ^ n ∂Measure.map f μ
参数：hf : AEStronglyMeasurable f μ；hn : n != 0；h'f : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.truncation_eq_of_nonneg`：truncation_eq_of_nonneg {f : 
α -> Real} {A : Real} (h : forall x, 0 <= f x) : truncation f A = indicator (Set
.Ioc 0 A) id ∘ f
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_pow`：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then
 a else b) ^ c = if p then a ^ c else b ^ c
（共 75 条，此处仅展示前 30 条）
-/
theorem moment_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : ℝ}
    {n : ℕ} (hn : n ≠ 0) (h'f : 0 ≤ f) :
    ∫ x, truncation f A x ^ n ∂μ = ∫ y in 0..A, y ^ n ∂Measure.map f μ := by
  have M : MeasurableSet (Set.Ioc 0 A) := measurableSet_Ioc
  have M' : MeasurableSet (Set.Ioc A 0) := measurableSet_Ioc
  rw [truncation_eq_of_nonneg h'f]
  change ∫ x, (fun z => indicator (Set.Ioc 0 A) id z ^ n) (f x) ∂μ = _
  rcases le_or_gt 0 A with (hA | hA)
  · rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable, intervalIntegral.integral_of_le hA,
      ← integral_indicator M]
    · simp only [indicator, zero_pow hn, id, ite_pow]
    · exact ((measurable_id.indicator M).pow_const n).aestronglyMeasurable
  · rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable, intervalIntegral.integral_of_ge hA.le,
      ← integral_indicator M']
    · simp only [Set.Ioc_eq_empty_of_le hA.le, zero_pow hn, Set.indicator_empty, integral_zero,
        zero_eq_neg]
      apply integral_eq_zero_of_ae
      have : ∀ᵐ x ∂Measure.map f μ, (0 : ℝ) ≤ x :=
        (ae_map_iff hf.aemeasurable measurableSet_Ici).2 (Eventually.of_forall h'f)
      filter_upwards [this] with x hx
      simp only [indicator, Set.mem_Ioc, Pi.zero_apply, ite_eq_right_iff, and_imp]
      intro _ h''x
      have : x = 0 := by linarith
      simp [this, zero_pow hn]
    · exact ((measurable_id.indicator M).pow_const n).aestronglyMeasurable
/-
**ProbabilityTheory.integral_truncation_eq_intervalIntegral** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：integral_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A
 : Real} (hA : 0 <= A) : ∫ x, truncation f A x ∂μ = ∫ y in -A..A, y ∂Measure.map
 f μ
参数：hf : AEStronglyMeasurable f μ；hA : 0 <= A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.moment_truncation_eq_intervalIntegral`：moment_truncati
on_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : Real} (hA : 0 <= A) 
{n : Nat} (hn : n != 0) : ∫ x, truncation f A…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem integral_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : ℝ}
    (hA : 0 ≤ A) : ∫ x, truncation f A x ∂μ = ∫ y in -A..A, y ∂Measure.map f μ := by
  simpa using moment_truncation_eq_intervalIntegral hf hA one_ne_zero
/-
**ProbabilityTheory.integral_truncation_eq_intervalIntegral_of_nonneg** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：integral_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurab
le f μ) {A : Real} (h'f : 0 <= f) : ∫ x, truncation f A x ∂μ = ∫ y in 0..A, y ∂M
easure.map f μ
参数：hf : AEStronglyMeasurable f μ；h'f : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.moment_truncation_eq_intervalIntegral_of_nonneg`：momen
t_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : 
Real} {n : Nat} (hn : n != 0) (h'f : 0 <= f) : ∫ x, tru…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem integral_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : ℝ}
    (h'f : 0 ≤ f) : ∫ x, truncation f A x ∂μ = ∫ y in 0..A, y ∂Measure.map f μ := by
  simpa using moment_truncation_eq_intervalIntegral_of_nonneg hf one_ne_zero h'f
/-
**ProbabilityTheory.integral_truncation_le_integral_of_nonneg** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：integral_truncation_le_integral_of_nonneg (hf : Integrable f μ) (h'f : 0 <
= f) {A : Real} : ∫ x, truncation f A x ∂μ <= ∫ x, f x ∂μ
参数：hf : Integrable f μ；h'f : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.truncation_nonneg`：truncation_nonneg {f : α -> Real} (
A : Real) {x : α} (h : 0 <= f x) : 0 <= truncation f A x
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `ProbabilityTheory.abs_truncation_le_abs_self`：abs_truncation_le_abs_self
 (f : α -> Real) (A : Real) (x : α) : |truncation f A x| <= |f x|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem integral_truncation_le_integral_of_nonneg (hf : Integrable f μ) (h'f : 0 ≤ f) {A : ℝ} :
    ∫ x, truncation f A x ∂μ ≤ ∫ x, f x ∂μ := by
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun x => ?_) hf (Eventually.of_forall fun x => ?_)
  · exact truncation_nonneg _ (h'f x)
  · calc
      truncation f A x ≤ |truncation f A x| := le_abs_self _
      _ ≤ |f x| := abs_truncation_le_abs_self _ _ _
      _ = f x := abs_of_nonneg (h'f x)

/-- If a function is integrable, then the integral of its truncated versions converges to the
integral of the whole function. -/
/-
**ProbabilityTheory.tendsto_integral_truncation** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：tendsto_integral_truncation {f : α -> Real} (hf : Integrable f μ) : Tendst
o (fun A => ∫ x, truncation f A x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))
参数：hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.truncation`：∀ {α : Type u_1} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.AEStr
onglyMeasurable f μ →     ∀ {A : ℝ}…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `ProbabilityTheory.abs_truncation_le_abs_self`：abs_truncation_le_abs_self
 (f : α -> Real) (A : Real) (x : α) : |truncation f A x| <= |f x|
· 使用定理 `MeasureTheory.Integrable.abs`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_8} [inst : NormedAddCommGroup β]   [ins
t_1 : Lattice β] […
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.truncation_eq_self`：truncation_eq_self {f : α -> Real}
 {A : Real} {x : α} (h : |f x| < A) : truncation f A x = f x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
If a function is integrable, then the integral of its truncated versions converg
es to the
integral of the whole function.
-/
theorem tendsto_integral_truncation {f : α → ℝ} (hf : Integrable f μ) :
    Tendsto (fun A => ∫ x, truncation f A x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => abs (f x)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun A ↦ hf.aestronglyMeasurable.truncation
  · filter_upwards with A
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_truncation_le_abs_self _ _ _
  · exact hf.abs
  · filter_upwards with x
    apply tendsto_const_nhds.congr' _
    filter_upwards [Ioi_mem_atTop (abs (f x))] with A hA
    exact (truncation_eq_self hA).symm
/-
**ProbabilityTheory.IdentDistrib.truncation** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {β 
: Type u_2} [inst : MeasurableSpace β]   {ν : MeasureTheory.Measure β} {f : α → 
ℝ} {g : β → ℝ},   ProbabilityTheory.IdentDistrib f g μ ν →     ∀ {A : ℝ}, Probab
ilityTheory.IdentDistrib (ProbabilityTheory.truncation f A) (ProbabilityTheory.t
runcation g A) μ ν
参数：ProbabilityTheory.truncation f A；ProbabilityTheory.truncation g A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem IdentDistrib.truncation {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ}
    {g : β → ℝ} (h : IdentDistrib f g μ ν) {A : ℝ} :
    IdentDistrib (truncation f A) (truncation g A) μ ν :=
  h.comp (measurable_id.indicator measurableSet_Ioc)

end Truncation

section StrongLawAeReal

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

section MomentEstimates

/-
**ProbabilityTheory.sum_prob_mem_Ioc_le** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：sum_prob_mem_Ioc_le {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= 
X) {K : Nat} {N : Nat} (hKN : K <= N) : ∑ j in range K, ℙ {ω | X ω in Set.Ioc (j
 : Real) N} <= ENNReal.ofReal (𝔼[X] + 1)
参数：hint : Integrable X；hnonneg : 0 <= X；hKN : K <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.sum_integral_adjacent_intervals_Ico`：sum_integral_adjac
ent_intervals_Ico {a : Nat -> Real} {m n : Nat} (hmn : m <= n) (hint : forall k 
in Ico m n, IntervalIntegrable f μ (a k) (…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.instRegularOfBorelSpaceOf
R1SpaceOfIsFiniteMeasure`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : Measu
reTheory.Measure α} [inst_1 : TopologicalSpace α] [BorelSpace α]   [R1Space α] [
h : μ.…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
（共 116 条，此处仅展示前 30 条）
-/
theorem sum_prob_mem_Ioc_le {X : Ω → ℝ} (hint : Integrable X) (hnonneg : 0 ≤ X) {K : ℕ} {N : ℕ}
    (hKN : K ≤ N) :
    ∑ j ∈ range K, ℙ {ω | X ω ∈ Set.Ioc (j : ℝ) N} ≤ ENNReal.ofReal (𝔼[X] + 1) := by
  let ρ : Measure ℝ := Measure.map X ℙ
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hint.aemeasurable
  have A : ∑ j ∈ range K, ∫ _ in j..N, (1 : ℝ) ∂ρ ≤ 𝔼[X] + 1 :=
    calc
      ∑ j ∈ range K, ∫ _ in j..N, (1 : ℝ) ∂ρ =
          ∑ j ∈ range K, ∑ i ∈ Ico j N, ∫ _ in i..(i + 1 : ℕ), (1 : ℝ) ∂ρ := by
        apply sum_congr rfl fun j hj => ?_
        rw [intervalIntegral.sum_integral_adjacent_intervals_Ico ((mem_range.1 hj).le.trans hKN)]
        intro k _
        exact continuous_const.intervalIntegrable _ _
      _ = ∑ i ∈ range N, ∑ j ∈ range (min (i + 1) K), ∫ _ in i..(i + 1 : ℕ), (1 : ℝ) ∂ρ := by
        simp_rw [sum_sigma']
        refine sum_nbij' (fun p ↦ ⟨p.2, p.1⟩) (fun p ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
          aesop (add simp Nat.lt_succ_iff)
      _ ≤ ∑ i ∈ range N, (i + 1) * ∫ _ in i..(i + 1 : ℕ), (1 : ℝ) ∂ρ := by
        gcongr with i
        simp only [Nat.cast_add, Nat.cast_one, sum_const, card_range, nsmul_eq_mul, Nat.cast_min]
        refine mul_le_mul_of_nonneg_right (min_le_left _ _) ?_
        apply intervalIntegral.integral_nonneg
        · simp only [le_add_iff_nonneg_right, zero_le_one]
        · simp only [zero_le_one, imp_true_iff]
      _ ≤ ∑ i ∈ range N, ∫ x in i..(i + 1 : ℕ), x + 1 ∂ρ := by
        gcongr with i
        have I : (i : ℝ) ≤ (i + 1 : ℕ) := by
          simp only [Nat.cast_add, Nat.cast_one, le_add_iff_nonneg_right, zero_le_one]
        simp_rw [intervalIntegral.integral_of_le I, ← integral_const_mul]
        apply setIntegral_mono_on
        · exact continuous_const.integrableOn_Ioc
        · exact (continuous_id.add continuous_const).integrableOn_Ioc
        · exact measurableSet_Ioc
        · intro x hx
          simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioc] at hx
          simp [hx.1.le]
      _ = ∫ x in 0..N, x + 1 ∂ρ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => ?_]
        · norm_cast
        · exact (continuous_id.add continuous_const).intervalIntegrable _ _
      _ = ∫ x in 0..N, x ∂ρ + ∫ x in 0..N, 1 ∂ρ := by
        rw [intervalIntegral.integral_add]
        · exact continuous_id.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
      _ = 𝔼[truncation X N] + ∫ x in 0..N, 1 ∂ρ := by
        rw [integral_truncation_eq_intervalIntegral_of_nonneg hint.1 hnonneg]
      _ ≤ 𝔼[X] + ∫ x in 0..N, 1 ∂ρ := by
        grw [integral_truncation_le_integral_of_nonneg hint hnonneg]
      _ ≤ 𝔼[X] + 1 := by
        gcongr
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg _)]
        simp only [integral_const, measureReal_restrict_apply', measurableSet_Ioc, Set.univ_inter,
          smul_eq_mul, mul_one]
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have B : ∀ a b, ℙ {ω | X ω ∈ Set.Ioc a b} = ENNReal.ofReal (∫ _ in Set.Ioc a b, (1 : ℝ) ∂ρ) := by
    intro a b
    rw [ofReal_setIntegral_one ρ _,
      Measure.map_apply_of_aemeasurable hint.aemeasurable measurableSet_Ioc]
    rfl
  calc
    ∑ j ∈ range K, ℙ {ω | X ω ∈ Set.Ioc (j : ℝ) N} =
        ∑ j ∈ range K, ENNReal.ofReal (∫ _ in Set.Ioc (j : ℝ) N, (1 : ℝ) ∂ρ) := by simp_rw [B]
    _ = ENNReal.ofReal (∑ j ∈ range K, ∫ _ in Set.Ioc (j : ℝ) N, (1 : ℝ) ∂ρ) := by
      simp [ENNReal.ofReal_sum_of_nonneg]
    _ = ENNReal.ofReal (∑ j ∈ range K, ∫ _ in (j : ℝ)..N, (1 : ℝ) ∂ρ) := by
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [intervalIntegral.integral_of_le (Nat.cast_le.2 ((mem_range.1 hj).le.trans hKN))]
    _ ≤ ENNReal.ofReal (𝔼[X] + 1) := ENNReal.ofReal_le_ofReal A
/-
**ProbabilityTheory.tsum_prob_mem_Ioi_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：tsum_prob_mem_Ioi_lt_top {X : Ω -> Real} (hint : Integrable X) (hnonneg : 
0 <= X) : (∑' j : Nat, ℙ {ω | X ω in Set.Ioi (j : Real)}) < ∞
参数：hint : Integrable X；hnonneg : 0 <= X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_finsetSum`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : AddCommMonoid M] [ContinuousAdd M]   {f : ι → α 
→ M} {x…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
（共 42 条，此处仅展示前 30 条）
-/
theorem tsum_prob_mem_Ioi_lt_top {X : Ω → ℝ} (hint : Integrable X) (hnonneg : 0 ≤ X) :
    (∑' j : ℕ, ℙ {ω | X ω ∈ Set.Ioi (j : ℝ)}) < ∞ := by
  suffices ∀ K : ℕ, ∑ j ∈ range K, ℙ {ω | X ω ∈ Set.Ioi (j : ℝ)} ≤ ENNReal.ofReal (𝔼[X] + 1) from
    (le_of_tendsto_of_tendsto (ENNReal.tendsto_nat_tsum _) tendsto_const_nhds
      (Eventually.of_forall this)).trans_lt ENNReal.ofReal_lt_top
  intro K
  have A : Tendsto (fun N : ℕ => ∑ j ∈ range K, ℙ {ω | X ω ∈ Set.Ioc (j : ℝ) N}) atTop
      (𝓝 (∑ j ∈ range K, ℙ {ω | X ω ∈ Set.Ioi (j : ℝ)})) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have : {ω | X ω ∈ Set.Ioi (i : ℝ)} = ⋃ N : ℕ, {ω | X ω ∈ Set.Ioc (i : ℝ) N} := by
      apply Set.Subset.antisymm _ _
      · intro ω hω
        obtain ⟨N, hN⟩ : ∃ N : ℕ, X ω ≤ N := exists_nat_ge (X ω)
        exact Set.mem_iUnion.2 ⟨N, hω, hN⟩
      · simp +contextual only [Set.mem_Ioc, Set.mem_Ioi,
          Set.iUnion_subset_iff, Set.ofPred_subset_ofPred, imp_true_iff]
    rw [this]
    apply tendsto_measure_iUnion_atTop
    intro m n hmn x hx
    exact ⟨hx.1, hx.2.trans (Nat.cast_le.2 hmn)⟩
  apply le_of_tendsto_of_tendsto A tendsto_const_nhds
  filter_upwards [Ici_mem_atTop K] with N hN
  exact sum_prob_mem_Ioc_le hint hnonneg hN
/-
**ProbabilityTheory.sum_variance_truncation_le** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：sum_variance_truncation_le {X : Ω -> Real} (hint : Integrable X) (hnonneg 
: 0 <= X) (K : Nat) : ∑ j in range K, ((j : Real) ^ 2)⁻¹ * 𝔼[truncation X j ^ 2]
 <= 2 * 𝔼[X]
参数：hint : Integrable X；hnonneg : 0 <= X；K : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.moment_truncation_eq_intervalIntegral_of_nonneg`：momen
t_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : 
Real} {n : Nat} (hn : n != 0) (h'f : 0 <= f) : ∫ x, tru…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.sum_integral_adjacent_intervals`：sum_integral_adjacent_
intervals {a : Nat -> Real} {n : Nat} (hint : forall k < n, IntervalIntegrable f
 μ (a k) (a <| k + 1)) : ∑ k in Finset…
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.instRegularOfBorelSpaceOf
R1SpaceOfIsFiniteMeasure`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : Measu
reTheory.Measure α} [inst_1 : TopologicalSpace α] [BorelSpace α]   [R1Space α] [
h : μ.…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
（共 139 条，此处仅展示前 30 条）
-/
theorem sum_variance_truncation_le {X : Ω → ℝ} (hint : Integrable X) (hnonneg : 0 ≤ X) (K : ℕ) :
    ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * 𝔼[truncation X j ^ 2] ≤ 2 * 𝔼[X] := by
  set Y := fun n : ℕ => truncation X n
  let ρ : Measure ℝ := Measure.map X ℙ
  have Y2 : ∀ n, 𝔼[Y n ^ 2] = ∫ x in 0..n, x ^ 2 ∂ρ := by
    intro n
    change 𝔼[fun x => Y n x ^ 2] = _
    rw [moment_truncation_eq_intervalIntegral_of_nonneg hint.1 two_ne_zero hnonneg]
  calc
    ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * 𝔼[Y j ^ 2] =
        ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * ∫ x in 0..j, x ^ 2 ∂ρ := by simp_rw [Y2]
    _ = ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * ∑ k ∈ range j, ∫ x in k..(k + 1 : ℕ), x ^ 2 ∂ρ := by
      congr 1 with j
      congr 1
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      · norm_cast
      intro k _
      exact (continuous_id.pow _).intervalIntegrable _ _
    _ = ∑ k ∈ range K, (∑ j ∈ Ioo k K, ((j : ℝ) ^ 2)⁻¹) * ∫ x in k..(k + 1 : ℕ), x ^ 2 ∂ρ := by
      simp_rw [mul_sum, sum_mul, sum_sigma']
      refine sum_nbij' (fun p ↦ ⟨p.2, p.1⟩) (fun p ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
        aesop (add unsafe lt_trans)
    _ ≤ ∑ k ∈ range K, 2 / (k + 1 : ℝ) * ∫ x in k..(k + 1 : ℕ), x ^ 2 ∂ρ := by
      gcongr with k
      · refine intervalIntegral.integral_nonneg_of_forall ?_ fun u => sq_nonneg _
        simp
      · apply sum_Ioo_inv_sq_le
    _ ≤ ∑ k ∈ range K, ∫ x in k..(k + 1 : ℕ), 2 * x ∂ρ := by
      gcongr with k
      have Ik : (k : ℝ) ≤ (k + 1 : ℕ) := by simp
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le Ik,
        intervalIntegral.integral_of_le Ik]
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun x hx => ?_
      · apply Continuous.integrableOn_Ioc (by fun_prop)
      · apply Continuous.integrableOn_Ioc (by fun_prop)
      · calc
          2 / (↑k + 1) * x ^ 2 = x / (k + 1) * (2 * x) := by ring
          _ ≤ 1 * (2 * x) := by
              have : 0 < x := k.cast_nonneg.trans_lt hx.1
              gcongr
              exact (div_le_one <| by positivity).2 <| mod_cast hx.2
          _ = 2 * x := by rw [one_mul]
    _ = 2 * ∫ x in (0 : ℝ)..K, x ∂ρ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => ?_]
      swap; · exact (continuous_const.mul continuous_id').intervalIntegrable _ _
      rw [intervalIntegral.integral_const_mul]
      norm_cast
    _ ≤ 2 * 𝔼[X] := mul_le_mul_of_nonneg_left (by
      rw [← integral_truncation_eq_intervalIntegral_of_nonneg hint.1 hnonneg]
      exact integral_truncation_le_integral_of_nonneg hint hnonneg) zero_le_two

end MomentEstimates

/-! Proof of the strong law of large numbers (almost sure version, assuming only
pairwise independence) for nonnegative random variables, following Etemadi's proof. -/
section StrongLawNonneg

variable (X : ℕ → Ω → ℝ) (hint : Integrable (X 0))
  (hindep : Pairwise (IndepFun on X)) (hident : ∀ i, IdentDistrib (X i) (X 0))
  (hnonneg : ∀ i ω, 0 ≤ X i ω)

include hint hindep hident hnonneg in
/-- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers (with respect to
the truncated expectation) along the sequence `c^n`, for any `c > 1`, up to a given `ε > 0`.
This follows from a variance control. -/
/-
**ProbabilityTheory.strong_law_aux1** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux1 {c : Real} (c_one : 1 < c) {ε : Real} (εpos : 0 < ε) : for
allᵐ ω, forallᶠ n : Nat in atTop, |∑ i in range ⌊c ^ n⌋₊, truncation (X i) i ω -
 𝔼[∑ i in range ⌊c ^ n⌋₊, truncation (X i) i]| < ε * ⌊c ^ n⌋₊
参数：c_one : 1 < c；εpos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ProbabilityTheory.IdentDistrib.aestronglyMeasurable_snd`：aestronglyMeasu
rable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] (h : Ide
ntDistrib f g μ ν) (hf : AEStronglyMeasurable…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `stronglyMeasurable_id`：∀ {α : Type u_1} {mα : MeasurableSpace α} [inst :
 TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]   [OpensMeasurab
leSpace α] …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_mono`：floor_mono : Monotone (floor : R -> Nat)
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `ProbabilityTheory.IdentDistrib.variance_eq`：variance_eq {f : α -> Real} 
{g : β -> Real} (h : IdentDistrib f g μ ν) : variance f μ = variance g ν
· 使用定理 `ProbabilityTheory.IdentDistrib.truncation`：∀ {α : Type u_1} {m : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_2} [inst : MeasurableSpace
 β]   {ν : MeasureTheory.Measur…
· 使用定理 `ProbabilityTheory.variance_le_expectation_sq`：variance_le_expectation_sq
 [IsProbabilityMeasure μ] {X : Ω -> Real} (hm : AEStronglyMeasurable X μ) : vari
ance X μ <= μ[X ^ 2]
· 使用定理 `MeasureTheory.AEStronglyMeasurable.truncation`：∀ {α : Type u_1} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.AEStr
onglyMeasurable f μ →     ∀ {A : ℝ}…
（共 127 条，此处仅展示前 30 条）

--- 原说明 ---
The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers (with
 respect to
the truncated expectation) along the sequence `c^n`, for any `c > 1`, up to a gi
ven `ε > 0`.
This follows from a variance control.
-/
theorem strong_law_aux1 {c : ℝ} (c_one : 1 < c) {ε : ℝ} (εpos : 0 < ε) : ∀ᵐ ω, ∀ᶠ n : ℕ in atTop,
    |∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i ω - 𝔼[∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i]| <
    ε * ⌊c ^ n⌋₊ := by
  /- Let `S n = ∑ i ∈ range n, Y i` where `Y i = truncation (X i) i`. We should show that
    `|S k - 𝔼[S k]| / k ≤ ε` along the sequence of powers of `c`. For this, we apply Borel-Cantelli:
    it suffices to show that the converse probabilities are summable. From Chebyshev inequality,
    this will follow from a variance control `∑' Var[S (c^i)] / (c^i)^2 < ∞`. This is checked in
    `I2` using pairwise independence to expand the variance of the sum as the sum of the variances,
    and then a straightforward but tedious computation (essentially boiling down to the fact that
    the sum of `1/(c ^ i)^2` beyond a threshold `j` is comparable to `1/j^2`).
    Note that we have written `c^i` in the above proof sketch, but rigorously one should put integer
    parts everywhere, making things more painful. We write `u i = ⌊c^i⌋₊` for brevity. -/
  have c_pos : 0 < c := zero_lt_one.trans c_one
  have hX : ∀ i, AEStronglyMeasurable (X i) ℙ := fun i =>
    (hident i).symm.aestronglyMeasurable_snd hint.1
  have A : ∀ i, StronglyMeasurable (indicator (Set.Ioc (-i : ℝ) i) id) := fun i =>
    stronglyMeasurable_id.indicator measurableSet_Ioc
  set Y := fun n : ℕ => truncation (X n) n
  set S := fun n => ∑ i ∈ range n, Y i with hS
  let u : ℕ → ℕ := fun n => ⌊c ^ n⌋₊
  have u_mono : Monotone u := fun i j hij => Nat.floor_mono (pow_right_mono₀ c_one.le hij)
  have I1 : ∀ K, ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * Var[Y j] ≤ 2 * 𝔼[X 0] := by
    intro K
    calc
      ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * Var[Y j] ≤
          ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * 𝔼[truncation (X 0) j ^ 2] := by
        gcongr with j
        rw [(hident j).truncation.variance_eq]
        exact variance_le_expectation_sq (hX 0).truncation
      _ ≤ 2 * 𝔼[X 0] := sum_variance_truncation_le hint (hnonneg 0) K
  let C := c ^ 5 * (c - 1)⁻¹ ^ 3 * (2 * 𝔼[X 0])
  have I2 : ∀ N, ∑ i ∈ range N, ((u i : ℝ) ^ 2)⁻¹ * Var[S (u i)] ≤ C := by
    intro N
    calc
      ∑ i ∈ range N, ((u i : ℝ) ^ 2)⁻¹ * Var[S (u i)] =
          ∑ i ∈ range N, ((u i : ℝ) ^ 2)⁻¹ * ∑ j ∈ range (u i), Var[Y j] := by
        congr 1 with i
        congr 1
        rw [hS, IndepFun.variance_sum]
        · intro j _
          exact (hident j).aestronglyMeasurable_fst.memLp_truncation
        · intro k _ l _ hkl
          exact (hindep hkl).comp (A k).measurable (A l).measurable
      _ = ∑ j ∈ range (u (N - 1)), (∑ i ∈ range N with j < u i, ((u i : ℝ) ^ 2)⁻¹) * Var[Y j] := by
        simp_rw [mul_sum, sum_mul, sum_sigma']
        refine sum_nbij' (fun p ↦ ⟨p.2, p.1⟩) (fun p ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
        · simp only [mem_sigma, mem_range, mem_filter, and_imp,
            Sigma.forall]
          exact fun a b haN hb ↦ ⟨hb.trans_le <| u_mono <| Nat.le_pred_of_lt haN, haN, hb⟩
        all_goals simp
      _ ≤ ∑ j ∈ range (u (N - 1)), c ^ 5 * (c - 1)⁻¹ ^ 3 / ↑j ^ 2 * Var[Y j] := by
        gcongr ∑ _ ∈ _, ?_ with j
        rcases eq_zero_or_pos j with (rfl | hj)
        · simp only [Nat.cast_zero]
          simp only [Y, Nat.cast_zero, truncation_zero, variance_zero, mul_zero, le_rfl]
        apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _)
        convert! sum_div_nat_floor_pow_sq_le_div_sq N (Nat.cast_pos.2 hj) c_one using 2
        · simp only [u, Nat.cast_lt]
        · simp only [u, one_div]
      _ = c ^ 5 * (c - 1)⁻¹ ^ 3 * ∑ j ∈ range (u (N - 1)), ((j : ℝ) ^ 2)⁻¹ * Var[Y j] := by
        simp_rw [mul_sum, div_eq_mul_inv, mul_assoc]
      _ ≤ c ^ 5 * (c - 1)⁻¹ ^ 3 * (2 * 𝔼[X 0]) := by
        apply mul_le_mul_of_nonneg_left (I1 _)
        apply mul_nonneg (pow_nonneg c_pos.le _)
        exact pow_nonneg (inv_nonneg.2 (sub_nonneg.2 c_one.le)) _
  have I3 : ∀ N, ∑ i ∈ range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} ≤
      ENNReal.ofReal (ε⁻¹ ^ 2 * C) := by
    intro N
    calc
      ∑ i ∈ range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} ≤
          ∑ i ∈ range N, ENNReal.ofReal (Var[S (u i)] / (u i * ε) ^ 2) := by
        gcongr with i _
        apply meas_ge_le_variance_div_sq
        · exact memLp_finsetSum' _ fun j _ => (hident j).aestronglyMeasurable_fst.memLp_truncation
        · apply mul_pos (Nat.cast_pos.2 _) εpos
          refine zero_lt_one.trans_le ?_
          apply Nat.le_floor
          rw [Nat.cast_one]
          apply one_le_pow₀ c_one.le
      _ = ENNReal.ofReal (∑ i ∈ range N, Var[S (u i)] / (u i * ε) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => ?_]
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
      _ ≤ ENNReal.ofReal (ε⁻¹ ^ 2 * C) := by
        apply ENNReal.ofReal_le_ofReal
        simp_rw [div_eq_inv_mul, ← inv_pow, mul_inv, mul_comm _ (ε⁻¹), mul_pow, mul_assoc,
          ← mul_sum]
        gcongr
        simpa only [inv_pow] using I2 N
  have I4 : (∑' i, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|}) < ∞ :=
    (le_of_tendsto_of_tendsto' (ENNReal.tendsto_nat_tsum _) tendsto_const_nhds I3).trans_lt
      ENNReal.ofReal_lt_top
  filter_upwards [ae_eventually_notMem I4.ne] with ω hω
  simp_rw [S, not_le, mul_comm, Finset.sum_apply] at hω
  convert! hω; simp only [Y, u, Finset.sum_apply]

include hint hindep hident hnonneg in
/-- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers
(with respect to the truncated expectation) along the sequence
`c^n`, for any `c > 1`. This follows from `strong_law_aux1` by varying `ε`. -/
/-
**ProbabilityTheory.strong_law_aux2** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux2 {c : Real} (c_one : 1 < c) : forallᵐ ω, (fun n : Nat => ∑ 
i in range ⌊c ^ n⌋₊, truncation (X i) i ω - 𝔼[∑ i in range ⌊c ^ n⌋₊, truncation 
(X i) i]) =o[atTop] fun n : Nat => (⌊c ^ n⌋₊ : Real)
参数：c_one : 1 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ProbabilityTheory.strong_law_aux1`：strong_law_aux1 {c : Real} (c_one : 1
 < c) {ε : Real} (εpos : 0 < ε) : forallᵐ ω, forallᶠ n : Nat in atTop, |∑ i in r
ange ⌊c ^ n⌋₊, truncati…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers
(with respect to the truncated expectation) along the sequence
`c^n`, for any `c > 1`. This follows from `strong_law_aux1` by varying `ε`.
-/
theorem strong_law_aux2 {c : ℝ} (c_one : 1 < c) :
    ∀ᵐ ω, (fun n : ℕ => ∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i ω -
      𝔼[∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i]) =o[atTop] fun n : ℕ => (⌊c ^ n⌋₊ : ℝ) := by
  obtain ⟨v, -, v_pos, v_lim⟩ :
      ∃ v : ℕ → ℝ, StrictAnti v ∧ (∀ n : ℕ, 0 < v n) ∧ Tendsto v atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have := fun i => strong_law_aux1 X hint hindep hident hnonneg c_one (v_pos i)
  filter_upwards [ae_all_iff.2 this] with ω hω
  apply Asymptotics.isLittleO_iff.2 fun ε εpos => ?_
  obtain ⟨i, hi⟩ : ∃ i, v i < ε := ((tendsto_order.1 v_lim).2 ε εpos).exists
  filter_upwards [hω i] with n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  exact hn.le.trans (mul_le_mul_of_nonneg_right hi.le (Nat.cast_nonneg _))

include hint hident in
/-- The expectation of the truncated version of `Xᵢ` behaves asymptotically like the whole
expectation. This follows from convergence and Cesàro averaging. -/
/-
**ProbabilityTheory.strong_law_aux3** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux3 : (fun n => 𝔼[∑ i in range n, truncation (X i) i] - n * 𝔼[
X 0]) =o[atTop] ((↑) : Nat -> Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IdentDistrib.integral_eq`：integral_eq [NormedAddCommGr
oup γ] [NormedSpace Real γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) : ∫ x, f x
 ∂μ = ∫ x, g x ∂ν
· 使用定理 `ProbabilityTheory.IdentDistrib.truncation`：∀ {α : Type u_1} {m : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_2} [inst : MeasurableSpace
 β]   {ν : MeasureTheory.Measur…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ProbabilityTheory.tendsto_integral_truncation`：tendsto_integral_truncati
on {f : α -> Real} (hf : Integrable f μ) : Tendsto (fun A => ∫ x, truncation f A
 x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integrable_truncation`：∀ {α : Type u_
1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ} [MeasureThe
ory.IsFiniteMeasure μ],   MeasureTheory.AEStro…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ProbabilityTheory.IdentDistrib.integrable_snd`：integrable_snd [NormedAdd
CommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) (hf : Integrable f μ) : I
ntegrable g ν
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
· 使用定理 `Asymptotics.isLittleO_sum_range_of_tendsto_zero`：Asymptotics.isLittleO_s
um_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α] {f : Nat -> α} (h : 
Tendsto f atTop (𝓝 0)) : (fun n => ∑ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
The expectation of the truncated version of `Xᵢ` behaves asymptotically like the
 whole
expectation. This follows from convergence and Cesàro averaging.
-/
theorem strong_law_aux3 :
    (fun n => 𝔼[∑ i ∈ range n, truncation (X i) i] - n * 𝔼[X 0]) =o[atTop] ((↑) : ℕ → ℝ) := by
  have A : Tendsto (fun i => 𝔼[truncation (X i) i]) atTop (𝓝 𝔼[X 0]) := by
    convert! (tendsto_integral_truncation hint).comp tendsto_natCast_atTop_atTop using 1
    ext i
    exact (hident i).truncation.integral_eq
  convert! Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 A) using 1
  ext1 n
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, Finset.sum_apply, sub_left_inj]
  rw [integral_finsetSum _ fun i _ => ?_]
  exact ((hident i).symm.integrable_snd hint).1.integrable_truncation

include hint hindep hident hnonneg in
/-- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers
(with respect to the original expectation) along the sequence
`c^n`, for any `c > 1`. This follows from the version from the truncated expectation, and the
fact that the truncated and the original expectations have the same asymptotic behavior. -/
/-
**ProbabilityTheory.strong_law_aux4** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux4 {c : Real} (c_one : 1 < c) : forallᵐ ω, (fun n : Nat => ∑ 
i in range ⌊c ^ n⌋₊, truncation (X i) i ω - ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[atTop] fun n :
 Nat => (⌊c ^ n⌋₊ : Real)
参数：c_one : 1 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.strong_law_aux2`：strong_law_aux2 {c : Real} (c_one : 1
 < c) : forallᵐ ω, (fun n : Nat => ∑ i in range ⌊c ^ n⌋₊, truncation (X i) i ω -
 𝔼[∑ i in range ⌊c ^ n⌋…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_nat_floor_atTop`：tendsto_nat_floor_atTop {α : Type*} [Semiring α
] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] : Tendsto (fun x : α
 => ⌊x⌋₊) atT…
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `ProbabilityTheory.strong_law_aux3`：strong_law_aux3 : (fun n => 𝔼[∑ i in 
range n, truncation (X i) i] - n * 𝔼[X 0]) =o[atTop] ((↑) : Nat -> Real)

--- 原说明 ---
The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers
(with respect to the original expectation) along the sequence
`c^n`, for any `c > 1`. This follows from the version from the truncated expecta
tion, and the
fact that the truncated and the original expectations have the same asymptotic b
ehavior.
-/
theorem strong_law_aux4 {c : ℝ} (c_one : 1 < c) :
    ∀ᵐ ω, (fun n : ℕ => ∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i ω - ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[atTop]
    fun n : ℕ => (⌊c ^ n⌋₊ : ℝ) := by
  filter_upwards [strong_law_aux2 X hint hindep hident hnonneg c_one] with ω hω
  have A : Tendsto (fun n : ℕ => ⌊c ^ n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt c_one)
  convert! hω.add ((strong_law_aux3 X hint hident).comp_tendsto A) using 1
  ext1 n
  simp

include hint hident hnonneg in
/-- The truncated and non-truncated versions of `Xᵢ` have the same asymptotic behavior, as they
almost surely coincide at all but finitely many steps. This follows from a probability computation
and Borel-Cantelli. -/
/-
**ProbabilityTheory.strong_law_aux5** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux5 : forallᵐ ω, (fun n : Nat => ∑ i in range n, truncation (X
 i) i ω - ∑ i in range n, X i ω) =o[atTop] fun n : Nat => (n : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IdentDistrib.measure_mem_eq`：measure_mem_eq (h : Ident
Distrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) : μ (f ⁻¹' s) = ν (g ⁻¹' s)
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ProbabilityTheory.tsum_prob_mem_Ioi_lt_top`：tsum_prob_mem_Ioi_lt_top {X 
: Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X) : (∑' j : Nat, ℙ {ω | X ω 
in Set.Ioi (j : Real)}) < ∞
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_eventually_notMem`：ae_eventually_notMem {s : Nat -> Set
 α} (hs : (∑' i, μ (s i)) != ∞) : forallᵐ x ∂μ, forallᶠ n in atTop, x ∉ s n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The truncated and non-truncated versions of `Xᵢ` have the same asymptotic behavi
or, as they
almost surely coincide at all but finitely many steps. This follows from a proba
bility computation
and Borel-Cantelli.
-/
theorem strong_law_aux5 :
    ∀ᵐ ω, (fun n : ℕ => ∑ i ∈ range n, truncation (X i) i ω - ∑ i ∈ range n, X i ω) =o[atTop]
    fun n : ℕ => (n : ℝ) := by
  have A : (∑' j : ℕ, ℙ {ω | X j ω ∈ Set.Ioi (j : ℝ)}) < ∞ := by
    convert! tsum_prob_mem_Ioi_lt_top hint (hnonneg 0) using 2
    ext1 j
    exact (hident j).measure_mem_eq measurableSet_Ioi
  have B : ∀ᵐ ω, Tendsto (fun n : ℕ => truncation (X n) n ω - X n ω) atTop (𝓝 0) := by
    filter_upwards [ae_eventually_notMem A.ne] with ω hω
    apply tendsto_const_nhds.congr' _
    filter_upwards [hω, Ioi_mem_atTop 0] with n hn npos
    simp only [truncation, indicator, Set.mem_Ioc, id, Function.comp_apply]
    split_ifs with h
    · exact (sub_self _).symm
    · have : -(n : ℝ) < X n ω := by
        apply lt_of_lt_of_le _ (hnonneg n ω)
        simpa only [Right.neg_neg_iff, Nat.cast_pos] using! npos
      simp only [this, true_and, not_le] at h
      exact (hn h).elim
  filter_upwards [B] with ω hω
  convert! isLittleO_sum_range_of_tendsto_zero hω using 1
  ext n
  rw [sum_sub_distrib]

include hint hindep hident hnonneg in
/-- `Xᵢ` satisfies the strong law of large numbers along the sequence
`c^n`, for any `c > 1`. This follows from the version for the truncated `Xᵢ`, and the fact that
`Xᵢ` and its truncated version have the same asymptotic behavior. -/
/-
**ProbabilityTheory.strong_law_aux6** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux6 {c : Real} (c_one : 1 < c) : forallᵐ ω, Tendsto (fun n : N
at => (∑ i in range ⌊c ^ n⌋₊, X i ω) / ⌊c ^ n⌋₊) atTop (𝓝 𝔼[X 0])
参数：c_one : 1 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.strong_law_aux5`：strong_law_aux5 : forallᵐ ω, (fun n :
 Nat => ∑ i in range n, truncation (X i) i ω - ∑ i in range n, X i ω) =o[atTop] 
fun n : Nat => (n : Rea…
· 使用定理 `ProbabilityTheory.strong_law_aux4`：strong_law_aux4 {c : Real} (c_one : 1
 < c) : forallᵐ ω, (fun n : Nat => ∑ i in range ⌊c ^ n⌋₊, truncation (X i) i ω -
 ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_nat_floor_atTop`：tendsto_nat_floor_atTop {α : Type*} [Semiring α
] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] : Tendsto (fun x : α
 => ⌊x⌋₊) atT…
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
`Xᵢ` satisfies the strong law of large numbers along the sequence
`c^n`, for any `c > 1`. This follows from the version for the truncated `Xᵢ`, an
d the fact that
`Xᵢ` and its truncated version have the same asymptotic behavior.
-/
theorem strong_law_aux6 {c : ℝ} (c_one : 1 < c) :
    ∀ᵐ ω, Tendsto (fun n : ℕ => (∑ i ∈ range ⌊c ^ n⌋₊, X i ω) / ⌊c ^ n⌋₊) atTop (𝓝 𝔼[X 0]) := by
  have H : ∀ n : ℕ, (0 : ℝ) < ⌊c ^ n⌋₊ := by
    intro n
    refine zero_lt_one.trans_le ?_
    simp only [Nat.one_le_cast, Nat.one_le_floor_iff, one_le_pow₀ c_one.le]
  filter_upwards [strong_law_aux4 X hint hindep hident hnonneg c_one,
    strong_law_aux5 X hint hident hnonneg] with ω hω h'ω
  rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.isLittleO_one_iff ℝ]
  have L : (fun n : ℕ => ∑ i ∈ range ⌊c ^ n⌋₊, X i ω - ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[atTop] fun n =>
      (⌊c ^ n⌋₊ : ℝ) := by
    have A : Tendsto (fun n : ℕ => ⌊c ^ n⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt c_one)
    convert! hω.sub (h'ω.comp_tendsto A) using 1
    ext1 n
    simp only [Function.comp_apply, sub_sub_sub_cancel_left]
  convert! L.mul_isBigO (isBigO_refl (fun n : ℕ => (⌊c ^ n⌋₊ : ℝ)⁻¹) atTop) using 1 <;>
  (ext1 n; field [(H n).ne'])

include hint hindep hident hnonneg in
/-- `Xᵢ` satisfies the strong law of large numbers along all integers. This follows from the
corresponding fact along the sequences `c^n`, and the fact that any integer can be sandwiched
between `c^n` and `c^(n+1)` with comparably small error if `c` is close enough to `1`
(which is formalized in `tendsto_div_of_monotone_of_tendsto_div_floor_pow`). -/
/-
**ProbabilityTheory.strong_law_aux7** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：strong_law_aux7 : forallᵐ ω, Tendsto (fun n : Nat => (∑ i in range n, X i 
ω) / n) atTop (𝓝 𝔼[X 0])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ProbabilityTheory.strong_law_aux6`：strong_law_aux6 {c : Real} (c_one : 1
 < c) : forallᵐ ω, Tendsto (fun n : Nat => (∑ i in range ⌊c ^ n⌋₊, X i ω) / ⌊c ^
 n⌋₊) atTop (𝓝 𝔼[X 0])
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_div_of_monotone_of_tendsto_div_floor_pow`：tendsto_div_of_monoton
e_of_tendsto_div_floor_pow (u : Nat -> Real) (l : Real) (hmono : Monotone u) (c 
: Nat -> Real) (cone : forall k, 1 < c…
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.range_mono`：range_mono : Monotone range

--- 原说明 ---
`Xᵢ` satisfies the strong law of large numbers along all integers. This follows 
from the
corresponding fact along the sequences `c^n`, and the fact that any integer can 
be sandwiched
between `c^n` and `c^(n+1)` with comparably small error if `c` is close enough t
o `1`
(which is formalized in `tendsto_div_of_monotone_of_tendsto_div_floor_pow`).
-/
theorem strong_law_aux7 :
    ∀ᵐ ω, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 𝔼[X 0]) := by
  obtain ⟨c, -, cone, clim⟩ :
      ∃ c : ℕ → ℝ, StrictAnti c ∧ (∀ n : ℕ, 1 < c n) ∧ Tendsto c atTop (𝓝 1) :=
    exists_seq_strictAnti_tendsto (1 : ℝ)
  have : ∀ k, ∀ᵐ ω,
      Tendsto (fun n : ℕ => (∑ i ∈ range ⌊c k ^ n⌋₊, X i ω) / ⌊c k ^ n⌋₊) atTop (𝓝 𝔼[X 0]) :=
    fun k => strong_law_aux6 X hint hindep hident hnonneg (cone k)
  filter_upwards [ae_all_iff.2 this] with ω hω
  apply tendsto_div_of_monotone_of_tendsto_div_floor_pow _ _ _ c cone clim _
  · intro m n hmn
    exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) fun i _ _ => hnonneg i ω
  · exact hω

end StrongLawNonneg

/-- **Strong law of large numbers**, almost sure version: if `X n` is a sequence of independent
identically distributed integrable real-valued random variables, then `∑ i ∈ range n, X i / n`
converges almost surely to `𝔼[X 0]`. We give here the strong version, due to Etemadi, that only
requires pairwise independence. Superseded by `strong_law_ae`, which works for random variables
taking values in any Banach space. -/
/-
**ProbabilityTheory.strong_law_ae_real** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} (X 
: Nat -> Ω -> Real) (hint : Integrable (X 0) μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) 
on X)) (hident : forall i, IdentDistrib (X i) (X 0) μ μ) : forallᵐ ω ∂μ, Tendsto
 (fun n : Nat => (∑ i in range n, X i ω) / n) atTop (𝓝 μ[X 0])
参数：X : Nat -> Ω -> Real；hint : Integrable (X 0) μ；hindep : Pairwise ((· ⟂ᵢ[μ] ·)
 on X)；hident : forall i, IdentDistrib (X i) (X 0) μ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IdentDistrib.ae_snd`：ae_snd (h : IdentDistrib f g μ ν)
 {p : γ -> Prop} (pmeas : MeasurableSet {x | p x}) (hp : forallᵐ x ∂μ, p (f x)) 
: forallᵐ x ∂ν, p (g x)
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
· 使用定理 `measurableSet_eq`：measurableSet_eq {a : α} : MeasurableSet { x | x = a }
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
**Strong law of large numbers**, almost sure version: if `X n` is a sequence of 
independent
identically distributed integrable real-valued random variables, then `∑ i ∈ ran
ge n, X i / n`
converges almost surely to `𝔼[X 0]`. We give here the strong version, due to Ete
madi, that only
requires pairwise independence. Superseded by `strong_law_ae`, which works for r
andom variables
taking values in any Banach space.
-/
theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0]) := by
  let mΩ : MeasureSpace Ω := ⟨μ⟩
  -- first get rid of the trivial case where the space is not a probability space
  by_cases h : ∀ᵐ ω, X 0 ω = 0
  · have I : ∀ᵐ ω, ∀ i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x ↦ x = 0) measurableSet_eq h
    filter_upwards [I] with ω hω
    simpa [hω] using! (integral_eq_zero_of_ae h).symm
  have : IsProbabilityMeasure μ :=
    hint.isProbabilityMeasure_of_indepFun (X 0) (X 1) h (hindep zero_ne_one)
  -- then consider separately the positive and the negative part, and apply the result
  -- for nonnegative functions to them.
  let pos : ℝ → ℝ := fun x => max x 0
  let neg : ℝ → ℝ := fun x => max (-x) 0
  have posm : Measurable pos := measurable_id'.max measurable_const
  have negm : Measurable neg := measurable_id'.neg.max measurable_const
  have A : ∀ᵐ ω, Tendsto (fun n : ℕ => (∑ i ∈ range n, (pos ∘ X i) ω) / n) atTop (𝓝 𝔼[pos ∘ X 0]) :=
    strong_law_aux7 _ hint.pos_part (fun i j hij => (hindep hij).comp posm posm)
      (fun i => (hident i).comp posm) fun i ω => le_max_right _ _
  have B : ∀ᵐ ω, Tendsto (fun n : ℕ => (∑ i ∈ range n, (neg ∘ X i) ω) / n) atTop (𝓝 𝔼[neg ∘ X 0]) :=
    strong_law_aux7 _ hint.neg_part (fun i j hij => (hindep hij).comp negm negm)
      (fun i => (hident i).comp negm) fun i ω => le_max_right _ _
  filter_upwards [A, B] with ω hωpos hωneg
  convert! hωpos.sub hωneg using 2
  · simp only [pos, neg, ← sub_div, ← sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self,
      Function.comp_apply]
  · simp +instances only [pos, neg, ← integral_sub hint.pos_part hint.neg_part,
      max_zero_sub_max_neg_zero_eq_self, Function.comp_apply, mΩ]

end StrongLawAeReal

section StrongLawVectorSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

open Set TopologicalSpace

/-- Preliminary lemma for the strong law of large numbers for vector-valued random variables:
the composition of the random variables with a simple function satisfies the strong law of large
numbers. -/
/-
**ProbabilityTheory.strong_law_ae_simpleFunc_comp** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：strong_law_ae_simpleFunc_comp (X : Nat -> Ω -> E) (h' : Measurable (X 0)) 
(hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : forall i, IdentDistrib (X i) (X
 0) μ μ) (φ : SimpleFunc E E) : forallᵐ ω ∂μ, Tendsto (fun n : Nat => (n : Real)
⁻¹ • (∑ i in range n, φ (X i ω))) atTop (𝓝 μ[φ ∘ (X 0)])
参数：X : Nat -> Ω -> E；h' : Measurable (X 0)；hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)；
hident : forall i, IdentDistrib (X i) (X 0) μ μ；φ : SimpleFunc E E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `measurable_indicator_const_iff`：measurable_indicator_const_iff [Zero β] 
[MeasurableSingletonClass β] (b : β) [NeZero b] : Measurable (s.indicator (fun (
_ : α) => b)) ↔ Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ProbabilityTheory.strong_law_ae_real`：strong_law_ae_real {Ω : Type*} {m 
: MeasurableSpace Ω} {μ : Measure Ω} (X : Nat -> Ω -> Real) (hint : Integrable (
X 0) μ) (hindep : Pairwise…
· 使用定理 `MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure`：integrable_of_is
FiniteMeasure [IsFiniteMeasure μ] (f : α ->ₛ E) : Integrable f μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Preliminary lemma for the strong law of large numbers for vector-valued random v
ariables:
the composition of the random variables with a simple function satisfies the str
ong law of large
numbers.
-/
lemma strong_law_ae_simpleFunc_comp (X : ℕ → Ω → E) (h' : Measurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (φ : SimpleFunc E E) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, φ (X i ω))) atTop (𝓝 μ[φ ∘ (X 0)]) := by
  -- this follows from the one-dimensional version when `φ` takes a single value, and is then
  -- extended to the general case by linearity.
  refine SimpleFunc.induction (motive := fun ψ ↦ ∀ᵐ ω ∂μ,
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, ψ (X i ω))) atTop (𝓝 μ[ψ ∘ (X 0)])) ?_ ?_ φ
  · intro c s hs
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, piecewise_eq_indicator, Function.comp_apply]
    let F : E → ℝ := indicator s 1
    have F_meas : Measurable F := (measurable_indicator_const_iff 1).2 hs
    let Y : ℕ → Ω → ℝ := fun n ↦ F ∘ (X n)
    have : ∀ᵐ (ω : Ω) ∂μ, Tendsto (fun (n : ℕ) ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        atTop (𝓝 μ[Y 0]) := by
      simp only [smul_eq_mul, ← div_eq_inv_mul]
      apply strong_law_ae_real
      · exact SimpleFunc.integrable_of_isFiniteMeasure
          ((SimpleFunc.piecewise s hs (SimpleFunc.const _ (1 : ℝ))
            (SimpleFunc.const _ (0 : ℝ))).comp (X 0) h')
      · exact fun i j hij ↦ IndepFun.comp (hindep hij) F_meas F_meas
      · exact fun i ↦ (hident i).comp F_meas
    filter_upwards [this] with ω hω
    have I : indicator s (Function.const E c) = (fun x ↦ (indicator s (1 : E → ℝ) x) • c) := by
      ext
      rw [← indicator_smul_const_apply]
      congr! 1
      ext
      simp
    simp only [I, integral_smul_const]
    convert! Tendsto.smul_const hω c using 1
    simp [F, Y, ← sum_smul, smul_smul]
  · rintro φ ψ - hφ hψ
    filter_upwards [hφ, hψ] with ω hωφ hωψ
    convert! hωφ.add hωψ using 1
    · simp [sum_add_distrib]
    · congr 1
      rw [← integral_add]
      · rfl
      · exact (φ.comp (X 0) h').integrable_of_isFiniteMeasure
      · exact (ψ.comp (X 0) h').integrable_of_isFiniteMeasure

variable [BorelSpace E]

/-- Preliminary lemma for the strong law of large numbers for vector-valued random variables,
assuming measurability in addition to integrability. This is weakened to ae measurability in
the full version `ProbabilityTheory.strong_law_ae`. -/
/-
**ProbabilityTheory.strong_law_ae_of_measurable** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：strong_law_ae_of_measurable (X : Nat -> Ω -> E) (hint : Integrable (X 0) μ
) (h' : StronglyMeasurable (X 0)) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident
 : forall i, IdentDistrib (X i) (X 0) μ μ) : forallᵐ ω ∂μ, Tendsto (fun n : Nat 
=> (n : Real)⁻¹ • (∑ i in range n, X i ω)) atTop (𝓝 μ[X 0])
参数：X : Nat -> Ω -> E；hint : Integrable (X 0) μ；h' : StronglyMeasurable (X 0)；hin
dep : Pairwise ((· ⟂ᵢ[μ] ·) on X)；hident : forall i, IdentDistrib (X i) (X 0) μ 
μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `ProbabilityTheory.strong_law_ae_simpleFunc_comp`：strong_law_ae_simpleFun
c_comp (X : Nat -> Ω -> E) (h' : Measurable (X 0)) (hindep : Pairwise ((· ⟂ᵢ[μ] 
·) on X)) (hident : forall i, IdentDi…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `Measurable.norm`：Measurable.norm {f : β -> α} (hf : Measurable f) : Meas
urable fun a => norm (f a)
· 使用定理 `Measurable.sub_stronglyMeasurable`：∀ {α : Type u_5} {E : Type u_6} {x : 
MeasurableSpace α} [inst : AddGroup E] [inst_1 : TopologicalSpace E]   [inst_2 :
 MeasurableSpace E] [Bo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `ProbabilityTheory.strong_law_ae_real`：strong_law_ae_real {Ω : Type*} {m 
: MeasurableSpace Ω} {μ : Measure Ω} (X : Nat -> Ω -> Real) (hint : Integrable (
X 0) μ) (hindep : Pairwise…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure`：integrable_of_is
FiniteMeasure [IsFiniteMeasure μ] (f : α ->ₛ E) : Integrable f μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
（共 133 条，此处仅展示前 30 条）

--- 原说明 ---
Preliminary lemma for the strong law of large numbers for vector-valued random v
ariables,
assuming measurability in addition to integrability. This is weakened to ae meas
urability in
the full version `ProbabilityTheory.strong_law_ae`.
-/
lemma strong_law_ae_of_measurable
    (X : ℕ → Ω → E) (hint : Integrable (X 0) μ) (h' : StronglyMeasurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0]) := by
  /- Choose a simple function `φ` such that `φ (X 0)` approximates well enough `X 0` -- this is
  possible as `X 0` is strongly measurable. Then `φ (X n)` approximates well `X n`.
  Then the strong law for `φ (X n)` implies the strong law for `X n`, up to a small
  error controlled by `n⁻¹ ∑_{i=0}^{n-1} ‖X i - φ (X i)‖`. This one is also controlled thanks
  to the one-dimensional law of large numbers: it converges ae to `𝔼[‖X 0 - φ (X 0)‖]`, which
  is arbitrarily small for well-chosen `φ`. -/
  let s : Set E := Set.range (X 0) ∪ {0}
  have zero_s : 0 ∈ s := by simp [s]
  have : SeparableSpace s := h'.separableSpace_range_union_singleton
  have : Nonempty s := ⟨0, zero_s⟩
  -- sequence of approximating simple functions.
  let φ : ℕ → SimpleFunc E E :=
    SimpleFunc.nearestPt (fun k => Nat.casesOn k 0 ((↑) ∘ denseSeq s) : ℕ → E)
  let Y : ℕ → ℕ → Ω → E := fun k i ↦ (φ k) ∘ (X i)
  -- strong law for `φ (X n)`
  have A : ∀ᵐ ω ∂μ, ∀ k,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, Y k i ω)) atTop (𝓝 μ[Y k 0]) :=
    ae_all_iff.2 (fun k ↦ strong_law_ae_simpleFunc_comp X h'.measurable hindep hident (φ k))
  -- strong law for the error `‖X i - φ (X i)‖`
  have B : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, ‖(X i - Y k i) ω‖) / n)
        atTop (𝓝 μ[(fun ω ↦ ‖(X 0 - Y k 0) ω‖)]) := by
    apply ae_all_iff.2 (fun k ↦ ?_)
    let G : ℕ → E → ℝ := fun k x ↦ ‖x - φ k x‖
    have G_meas : ∀ k, Measurable (G k) :=
      fun k ↦ (measurable_id.sub_stronglyMeasurable (φ k).stronglyMeasurable).norm
    have I : ∀ k i, (fun ω ↦ ‖(X i - Y k i) ω‖) = (G k) ∘ (X i) := fun k i ↦ rfl
    apply strong_law_ae_real (fun i ω ↦ ‖(X i - Y k i) ω‖)
    · exact (hint.sub ((φ k).comp (X 0) h'.measurable).integrable_of_isFiniteMeasure).norm
    · unfold Function.onFun
      simp_rw [I]
      intro i j hij
      exact (hindep hij).comp (G_meas k) (G_meas k)
    · intro i
      simp_rw [I]
      apply (hident i).comp (G_meas k)
  -- check that, when both convergences above hold, then the strong law is satisfied
  filter_upwards [A, B] with ω hω h'ω
  rw [tendsto_iff_norm_sub_tendsto_zero, tendsto_order]
  refine ⟨fun c hc ↦ Eventually.of_forall (fun n ↦ hc.trans_le (norm_nonneg _)), ?_⟩
  -- start with some positive `ε` (the desired precision), and fix `δ` with `3 δ < ε`.
  intro ε (εpos : 0 < ε)
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ δ + δ + δ < ε := ⟨ε/4, by positivity, by linarith⟩
  -- choose `k` large enough so that `φₖ (X 0)` approximates well enough `X 0`, up to the
  -- precision `δ`.
  obtain ⟨k, hk⟩ : ∃ k, ∫ ω, ‖(X 0 - Y k 0) ω‖ ∂μ < δ := by
    simp_rw [Pi.sub_apply, norm_sub_rev (X 0 _)]
    exact ((tendsto_order.1 (tendsto_integral_norm_approxOn_sub h'.measurable hint)).2 δ
      δpos).exists
  have : ‖μ[Y k 0] - μ[X 0]‖ < δ := by
    rw [norm_sub_rev, ← integral_sub hint]
    · exact (norm_integral_le_integral_norm _).trans_lt hk
    · exact ((φ k).comp (X 0) h'.measurable).integrable_of_isFiniteMeasure
  -- consider `n` large enough for which the above convergences have taken place within `δ`.
  have I : ∀ᶠ n in atTop, (∑ i ∈ range n, ‖(X i - Y k i) ω‖) / n < δ :=
    (tendsto_order.1 (h'ω k)).2 δ hk
  have J : ∀ᶠ (n : ℕ) in atTop, ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, Y k i ω) - μ[Y k 0]‖ < δ := by
    specialize hω k
    rw [tendsto_iff_norm_sub_tendsto_zero] at hω
    exact (tendsto_order.1 hω).2 δ δpos
  filter_upwards [I, J] with n hn h'n
  -- at such an `n`, the strong law is realized up to `ε`.
  calc
  ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω - μ[X 0]‖
    = ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - Y k i ω) +
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y k i ω - μ[Y k 0]) + (μ[Y k 0] - μ[X 0])‖ := by
      congr
      simp only [sum_sub_distrib, smul_sub]
      abel
  _ ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - Y k i ω)‖ +
        ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y k i ω - μ[Y k 0]‖ + ‖μ[Y k 0] - μ[X 0]‖ :=
      norm_add₃_le
  _ ≤ (∑ i ∈ Finset.range n, ‖X i ω - Y k i ω‖) / n + δ + δ := by
      gcongr
      simp only [norm_smul, norm_inv, RCLike.norm_natCast,
        div_eq_inv_mul]
      gcongr
      exact norm_sum_le _ _
  _ ≤ δ + δ + δ := by
      gcongr
      exact hn.le
  _ < ε := hδ

omit [IsProbabilityMeasure μ] in
/-- **Strong law of large numbers**, almost sure version: if `X n` is a sequence of independent
identically distributed integrable random variables taking values in a Banach space,
then `n⁻¹ • ∑ i ∈ range n, X i` converges almost surely to `𝔼[X 0]`. We give here the strong
version, due to Etemadi, that only requires pairwise independence. -/
/-
**ProbabilityTheory.strong_law_ae** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：strong_law_ae (X : Nat -> Ω -> E) (hint : Integrable (X 0) μ) (hindep : Pa
irwise ((· ⟂ᵢ[μ] ·) on X)) (hident : forall i, IdentDistrib (X i) (X 0) μ μ) : f
orallᵐ ω ∂μ, Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, X i ω)) atT
op (𝓝 μ[X 0])
参数：X : Nat -> Ω -> E；hint : Integrable (X 0) μ；hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
 X)；hident : forall i, IdentDistrib (X i) (X 0) μ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IdentDistrib.ae_snd`：ae_snd (h : IdentDistrib f g μ ν)
 {p : γ -> Prop} (pmeas : MeasurableSet {x | p x}) (hp : forallᵐ x ∂μ, p (f x)) 
: forallᵐ x ∂ν, p (g x)
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
· 使用定理 `measurableSet_eq`：measurableSet_eq {a : α} : MeasurableSet { x | x = a }
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.Integrable.isProbabilityMeasure_of_indepFun`：∀ {Ω : Type u
_1} {E : Type u_2} {F : Type u_3} [inst : MeasurableSpace Ω] {μ : MeasureTheory.
Measure Ω}   [inst_1 : NormedAddCommGroup E] [i…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
**Strong law of large numbers**, almost sure version: if `X n` is a sequence of 
independent
identically distributed integrable random variables taking values in a Banach sp
ace,
then `n⁻¹ • ∑ i ∈ range n, X i` converges almost surely to `𝔼[X 0]`. We give her
e the strong
version, due to Etemadi, that only requires pairwise independence.
-/
theorem strong_law_ae (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0]) := by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : ∀ᵐ ω ∂μ, X 0 ω = 0
  · have I : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x ↦ x = 0) measurableSet_eq h
    filter_upwards [I] with ω hω
    simpa [hω] using (integral_eq_zero_of_ae h).symm
  have : IsProbabilityMeasure μ :=
    hint.isProbabilityMeasure_of_indepFun (X 0) (X 1) h (hindep zero_ne_one)
  -- we reduce to the case of strongly measurable random variables, by using `Y i` which is strongly
  -- measurable and ae equal to `X i`.
  have A : ∀ i, Integrable (X i) μ := fun i ↦ (hident i).integrable_iff.2 hint
  let Y : ℕ → Ω → E := fun i ↦ (A i).1.mk (X i)
  have B : ∀ᵐ ω ∂μ, ∀ n, X n ω = Y n ω :=
    ae_all_iff.2 (fun i ↦ AEStronglyMeasurable.ae_eq_mk (A i).1)
  have Yint : Integrable (Y 0) μ := Integrable.congr hint (AEStronglyMeasurable.ae_eq_mk (A 0).1)
  have C : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, Y i ω)) atTop (𝓝 μ[Y 0]) := by
    apply strong_law_ae_of_measurable Y Yint ((A 0).1.stronglyMeasurable_mk)
      (fun i j hij ↦ IndepFun.congr (hindep hij) (A i).1.ae_eq_mk (A j).1.ae_eq_mk)
      (fun i ↦ ((A i).1.identDistrib_mk.symm.trans (hident i)).trans (A 0).1.identDistrib_mk)
  filter_upwards [B, C] with ω h₁ h₂
  have : μ[X 0] = μ[Y 0] := integral_congr_ae (AEStronglyMeasurable.ae_eq_mk (A 0).1)
  rw [this]
  apply Tendsto.congr (fun n ↦ ?_) h₂
  congr with i
  exact (h₁ i).symm

end StrongLawVectorSpace

section StrongLawLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Strong law of large numbers**, Lᵖ version: if `X n` is a sequence of independent
identically distributed random variables in Lᵖ, then `n⁻¹ • ∑ i ∈ range n, X i`
converges in `Lᵖ` to `𝔼[X 0]`. -/
/-
**ProbabilityTheory.strong_law_Lp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：strong_law_Lp {p : Real>=0∞} (hp : 1 <= p) (hp' : p != ∞) (X : Nat -> Ω ->
 E) (hℒp : MemLp (X 0) p μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : for
all i, IdentDistrib (X i) (X 0) μ μ) : Tendsto (fun (n : Nat) => eLpNorm (fun ω 
=> (n : Real)⁻¹ • (∑ i in range n, X i ω) - μ[X 0]) p μ) atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；X : Nat -> Ω -> E；hℒp : MemLp (X 0) p μ；hindep : Pai
rwise ((· ⟂ᵢ[μ] ·) on X)；hident : forall i, IdentDistrib (X i) (X 0) μ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.IdentDistrib.ae_snd`：ae_snd (h : IdentDistrib f g μ ν)
 {p : γ -> Prop} (pmeas : MeasurableSet {x | p x}) (hp : forallᵐ x ∂μ, p (f x)) 
: forallᵐ x ∂ν, p (g x)
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
· 使用定理 `measurableSet_eq`：measurableSet_eq {a : α} : MeasurableSet { x | x = a }
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_of_ae_zero`：eLpNorm_eq_zero_of_ae_zero {f 
: α -> ε} (hf : f =ᵐ[μ] 0) : eLpNorm f p μ = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.instT5Space`：T5Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
**Strong law of large numbers**, Lᵖ version: if `X n` is a sequence of independe
nt
identically distributed random variables in Lᵖ, then `n⁻¹ • ∑ i ∈ range n, X i`
converges in `Lᵖ` to `𝔼[X 0]`.
-/
theorem strong_law_Lp {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (X : ℕ → Ω → E)
    (hℒp : MemLp (X 0) p μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun (n : ℕ) => eLpNorm (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω) - μ[X 0]) p μ)
      atTop (𝓝 0) := by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : ∀ᵐ ω ∂μ, X 0 ω = 0
  · have I : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x ↦ x = 0) measurableSet_eq h
    have A (n : ℕ) : eLpNorm (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω) - μ[X 0]) p μ = 0 := by
      simp only [integral_eq_zero_of_ae h, sub_zero]
      apply eLpNorm_eq_zero_of_ae_zero
      filter_upwards [I] with ω hω
      simp [hω]
    simp [A]
  -- Then use ae convergence and uniform integrability
  have : IsProbabilityMeasure μ := MemLp.isProbabilityMeasure_of_indepFun
    (X 0) (X 1) (zero_lt_one.trans_le hp).ne' hp' hℒp h (hindep zero_ne_one)
  have hmeas : ∀ i, AEStronglyMeasurable (X i) μ := fun i =>
    (hident i).aestronglyMeasurable_iff.2 hℒp.1
  have hint : Integrable (X 0) μ := hℒp.integrable hp
  have havg (n : ℕ) :
      AEStronglyMeasurable (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) μ :=
    AEStronglyMeasurable.const_smul (aestronglyMeasurable_fun_sum _ fun i _ => hmeas i) _
  refine tendsto_Lp_finite_of_tendstoInMeasure hp hp' havg (memLp_const _) ?_
    (tendstoInMeasure_of_tendsto_ae havg (strong_law_ae _ hint hindep hident))
  rw [(_ : (fun (n : ℕ) ω => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω))
            = fun (n : ℕ) => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i))]
  · apply UniformIntegrable.unifIntegrable
    apply uniformIntegrable_average hp
    exact MemLp.uniformIntegrable_of_identDistrib hp hp' hℒp hident
  · ext n ω
    simp only [Pi.smul_apply, Finset.sum_apply]

end StrongLawLp

end ProbabilityTheory

