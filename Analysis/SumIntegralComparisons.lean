/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson, Alastair Irving
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Set.Function

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Comparing sums and integrals

## Summary

It is often the case that error terms in analysis can be computed by comparing
an infinite sum to the improper integral of an antitone function.

It contains several lemmas in this direction, for antitone or monotone functions
(or products of antitone and monotone functions), formulated for sums on `range i` or `Ico a b`.
These are used to prove a version of the integral test for antitone functions.

## Main Results

* `AntitoneOn.integral_le_sum`: The integral of an antitone function is at most the sum of its
  values at integer steps aligning with the left-hand side of the interval.
* `AntitoneOn.sum_le_integral`: The sum of an antitone function along integer steps aligning with
  the right-hand side of the interval is at most the integral of the function along that interval
* `MonotoneOn.integral_le_sum`: The integral of a monotone function is at most the sum of its
  values at integer steps aligning with the right-hand side of the interval.
* `MonotoneOn.sum_le_integral`: The sum of a monotone function along integer steps aligning with
  the left-hand side of the interval is at most the integral of the function along that interval
* `sum_mul_Ico_le_integral_of_monotone_antitone`: the sum of `f i * g i` on an interval is bounded
  by the integral of `f x * g (x - 1)` if `f` is monotone and `g` is antitone.
* `integral_le_sum_mul_Ico_of_antitone_monotone`: the sum of `f i * g i` on an interval is bounded
  below by the integral of `f x * g (x - 1)` if `f` is antitone and `g` is monotone.
* `AntitoneOn.summable_of_integrableOn_Ioi_zero` and `AntitoneOn.tsum_le_integral`, the
  integral test for antitone functions.
* `AntitoneOn.abs_tsum_sub_sum_range_le_integral`: an error estimate for the difference
  between a sum and its partial sums in terms of an integral.
* `AntitoneOn.integrableOn_Ioi_zero_of_summable` and `AntitoneOn.integral_le_tsum`, the converse to
  the integral test.
## Tags

analysis, comparison, asymptotics
-/

public section

open Set MeasureTheory MeasureSpace intervalIntegral

variable {x₀ : ℝ} {a b : ℕ} {f g : ℝ → ℝ}

/-
**sum_Ico_le_integral_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_Ico_le_integral_of_le (hab : a <= b) (h : forall i in Ico a b, forall 
x in Ico (i : Real) ↑(i + 1), f i <= g x) (hg : IntegrableOn g (Ico a b)) : ∑ i 
in .Ico a b, f i <= ∫ x in a..b, g x
参数：hab : a <= b；h : forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), f 
i <= g x；hg : IntegrableOn g (Ico a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ico_of_le`：intervalIntegrable_iff_in
tegrableOn_Ico_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `intervalIntegral.integral_mono_on_of_le_Ioo`：integral_mono_on_of_le_Ioo 
[NullSingletonClass μ] (h : forall x in Ioo a b, f x <= g x) : (∫ u in a..b, f u
 ∂μ) <= ∫ u in a..b, g u ∂μ
（共 32 条，此处仅展示前 30 条）
-/
lemma sum_Ico_le_integral_of_le (hab : a ≤ b)
    (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) ↑(i + 1), f i ≤ g x)
    (hg : IntegrableOn g (Ico a b)) : ∑ i ∈ .Ico a b, f i ≤ ∫ x in a..b, g x := by
  have A i (hi : i ∈ Finset.Ico a b) : IntervalIntegrable g volume i ↑(i + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    simp only [Finset.mem_Ico, ← Nat.add_one_le_iff] at hi
    rify at hi
    exact hg.mono (by grind) le_rfl
  calc
  _ = ∑ i ∈ .Ico a b, (∫ x in (i : ℝ)..↑(i + 1), f i) := by simp
  _ ≤ ∑ i ∈ .Ico a b, (∫ x in (i : ℝ)..↑(i + 1), g x) := by
    gcongr with i hi
    apply integral_mono_on_of_le_Ioo (by simp) (by simp) (A _ hi) (fun x hx ↦ ?_)
    exact h _ (by simpa using hi) _ (Ioo_subset_Ico_self hx)
  _ = _ := by rw [sum_integral_adjacent_intervals_Ico (a := (↑·)) hab]; grind
/-
**integral_le_sum_Ico_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integral_le_sum_Ico_of_le (hab : a <= b) (h : forall i in Ico a b, forall 
x in Ico (i : Real) ↑(i + 1), g x <= f i) (hg : IntegrableOn g (Ico a b)) : ∫ x 
in a..b, g x <= ∑ i in .Ico a b, f i
参数：hab : a <= b；h : forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), g 
x <= f i；hg : IntegrableOn g (Ico a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用引理 `sum_Ico_le_integral_of_le`：sum_Ico_le_integral_of_le (hab : a <= b) (h :
 forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), f i <= g x) (hg : Int
egrableOn g (Ic…
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …
-/
lemma integral_le_sum_Ico_of_le (hab : a ≤ b)
    (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) ↑(i + 1), g x ≤ f i)
    (hg : IntegrableOn g (Ico a b)) : ∫ x in a..b, g x ≤ ∑ i ∈ .Ico a b, f i := by
  convert! neg_le_neg (sum_Ico_le_integral_of_le (f := -f) (g := -g) hab
    (fun i hi x hx ↦ neg_le_neg (h i hi x hx)) hg.neg) <;> simp
/-
**AntitoneOn.intervalIntegrable_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem AntitoneOn.intervalIntegrable_subset (hf : AntitoneOn f (Icc x₀ (x₀ + a)))
    (k : ℕ) (hk : k + 1 ≤ a) : IntervalIntegrable f volume (x₀ + k) (x₀ + ↑(k + 1)) := by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le (by simp)]
  apply Icc_subset_Icc <;> simp [-Nat.cast_add, hk]
/-
**AntitoneOn.integral_le_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integral_le_sum (hf : AntitoneOn f (Icc x₀ (x₀ + a))) : ∫ x in 
x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + i)
参数：hf : AntitoneOn f (Icc x₀ (x₀ + a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.sum_integral_adjacent_intervals`：sum_integral_adjacent_
intervals {a : Nat -> Real} {n : Nat} (hint : forall k < n, IntervalIntegrable f
 μ (a k) (a <| k + 1)) : ∑ k in Finset…
· 使用定理 `_private.Mathlib.Analysis.SumIntegralComparisons.0.AntitoneOn.intervalIn
tegrable_subset`：∀ {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ},   AntitoneOn f (Set.Icc x₀ (x₀ 
+ ↑a)) →     ∀ (k : ℕ), k + 1 ≤ a → IntervalIntegrable f MeasureTheory.volume…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `intervalIntegral.integral_mono_on`：integral_mono_on (h : forall x in Icc
 a b, f x <= g x) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 34 条，此处仅展示前 30 条）
-/
theorem AntitoneOn.integral_le_sum (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x ≤ ∑ i ∈ .range a, f (x₀ + i) := calc
  _ = ∑ i ∈ .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    convert! (sum_integral_adjacent_intervals hf.intervalIntegrable_subset).symm
    simp
  _ ≤ ∑ i ∈ .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + i) := by
    gcongr with i hi
    rw [Finset.mem_range, ← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
    refine integral_mono_on (by simp) this (by simp) fun _ _ ↦ by apply hf <;> grind
  _ = _ := by simp
/-
**AntitoneOn.integral_le_sum_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integral_le_sum_Ico (hab : a <= b) (hf : AntitoneOn f (Set.Icc 
a b)) : ∫ x in a..b, f x <= ∑ x in .Ico a b, f x
参数：hab : a <= b；hf : AntitoneOn f (Set.Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_add`：∀ {α : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : AddCommMonoid α] [inst_2 : PartialOrder α]   [IsOrderedCancelAddM
onoid α]…
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `AntitoneOn.integral_le_sum`：AntitoneOn.integral_le_sum (hf : AntitoneOn 
f (Icc x₀ (x₀ + a))) : ∫ x in x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
theorem AntitoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : AntitoneOn f (Set.Icc a b)) :
    ∫ x in a..b, f x ≤ ∑ x ∈ .Ico a b, f x := by
  suffices ∫ x in a..a + ↑(b - a), f x ≤ ∑ x ∈ .Ico (0 + a) (b - a + a), f x by simp_all
  rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range]
  suffices ∫ x in a..a + ↑(b - a), f x ≤ ∑ x ∈ .range (b - a), f (a + x) by simp_all
  exact AntitoneOn.integral_le_sum (by simp only [hf, hab, Nat.cast_sub, add_sub_cancel])
/-
**AntitoneOn.sum_le_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.sum_le_integral (hf : AntitoneOn f (Icc x₀ (x₀ + a))) : ∑ i in 
.range a, f (x₀ + ↑(i + 1)) <= ∫ x in x₀..x₀ + a, f x
参数：hf : AntitoneOn f (Icc x₀ (x₀ + a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `_private.Mathlib.Analysis.SumIntegralComparisons.0.AntitoneOn.intervalIn
tegrable_subset`：∀ {x₀ : ℝ} {a : ℕ} {f : ℝ → ℝ},   AntitoneOn f (Set.Icc x₀ (x₀ 
+ ↑a)) →     ∀ (k : ℕ), k + 1 ≤ a → IntervalIntegrable f MeasureTheory.volume…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `intervalIntegral.integral_mono_on`：integral_mono_on (h : forall x in Icc
 a b, f x <= g x) : (∫ u in a..b, f u ∂μ) <= ∫ u in a..b, g u ∂μ
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
（共 35 条，此处仅展示前 30 条）
-/
theorem AntitoneOn.sum_le_integral (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    ∑ i ∈ .range a, f (x₀ + ↑(i + 1)) ≤ ∫ x in x₀..x₀ + a, f x := calc
  _ = ∑ i ∈ .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + ↑(i + 1)) := by simp
  _ ≤ ∑ i ∈ .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    gcongr with i hi
    rw [Finset.mem_range, ← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
    exact integral_mono_on (by simp) (by simp) this fun _ _ ↦ by apply hf <;> grind
  _ = _ := by
    convert! sum_integral_adjacent_intervals hf.intervalIntegrable_subset
    simp [-Nat.cast_add]
/-
**AntitoneOn.sum_le_integral_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.sum_le_integral_Ico (hab : a <= b) (hf : AntitoneOn f (Icc a b)
) : ∑ i in .Ico a b, f ↑(i + 1) <= ∫ x in a..b, f x
参数：hab : a <= b；hf : AntitoneOn f (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `AntitoneOn.sum_le_integral`：AntitoneOn.sum_le_integral (hf : AntitoneOn 
f (Icc x₀ (x₀ + a))) : ∑ i in .range a, f (x₀ + ↑(i + 1)) <= ∫ x in x₀..x₀ + a, 
f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
theorem AntitoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) :
    ∑ i ∈ .Ico a b, f ↑(i + 1) ≤ ∫ x in a..b, f x := by
  suffices ∑ i ∈ .Ico (0 + a) (b - a + a), f ↑(i + 1) ≤ ∫ x in a..a + ↑(b - a), f x by simp_all
  simp_rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range, add_assoc]
  suffices ∑ x ∈ .range (b - a), f (a + ↑(x + 1)) ≤ ∫ x in a..a + ↑(b - a), f x by simp_all
  exact AntitoneOn.sum_le_integral (by simp [hf, hab])
/-
**MonotoneOn.sum_le_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.sum_le_integral (hf : MonotoneOn f (Icc x₀ (x₀ + a))) : ∑ i in 
.range a, f (x₀ + i) <= ∫ x in x₀..x₀ + a, f x
参数：hf : MonotoneOn f (Icc x₀ (x₀ + a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `AntitoneOn.integral_le_sum`：AntitoneOn.integral_le_sum (hf : AntitoneOn 
f (Icc x₀ (x₀ + a))) : ∫ x in x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + i)
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
-/
theorem MonotoneOn.sum_le_integral (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    ∑ i ∈ .range a, f (x₀ + i) ≤ ∫ x in x₀..x₀ + a, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum
/-
**MonotoneOn.sum_le_integral_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.sum_le_integral_Ico (hab : a <= b) (hf : MonotoneOn f (Set.Icc 
a b)) : ∑ x in .Ico a b, f x <= ∫ x in a..b, f x
参数：hab : a <= b；hf : MonotoneOn f (Set.Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `AntitoneOn.integral_le_sum_Ico`：AntitoneOn.integral_le_sum_Ico (hab : a 
<= b) (hf : AntitoneOn f (Set.Icc a b)) : ∫ x in a..b, f x <= ∑ x in .Ico a b, f
 x
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
-/
theorem MonotoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∑ x ∈ .Ico a b, f x ≤ ∫ x in a..b, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab
/-
**MonotoneOn.integral_le_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.integral_le_sum (hf : MonotoneOn f (Icc x₀ (x₀ + a))) : ∫ x in 
x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + ↑(i + 1))
参数：hf : MonotoneOn f (Icc x₀ (x₀ + a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `AntitoneOn.sum_le_integral`：AntitoneOn.sum_le_integral (hf : AntitoneOn 
f (Icc x₀ (x₀ + a))) : ∑ i in .range a, f (x₀ + ↑(i + 1)) <= ∫ x in x₀..x₀ + a, 
f x
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
-/
theorem MonotoneOn.integral_le_sum (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x ≤ ∑ i ∈ .range a, f (x₀ + ↑(i + 1)) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral
/-
**MonotoneOn.integral_le_sum_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.integral_le_sum_Ico (hab : a <= b) (hf : MonotoneOn f (Set.Icc 
a b)) : ∫ x in a..b, f x <= ∑ i in .Ico a b, f ↑(i + 1)
参数：hab : a <= b；hf : MonotoneOn f (Set.Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `intervalIntegral.integral_neg`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E}   {μ : MeasureTheory.Meas
ure ℝ}, ∫ (x : ℝ) i…
· 使用定理 `AntitoneOn.sum_le_integral_Ico`：AntitoneOn.sum_le_integral_Ico (hab : a 
<= b) (hf : AntitoneOn f (Icc a b)) : ∑ i in .Ico a b, f ↑(i + 1) <= ∫ x in a..b
, f x
· 使用定理 `MonotoneOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_
1 : Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β 
→ α}…
-/
theorem MonotoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∫ x in a..b, f x ≤ ∑ i ∈ .Ico a b, f ↑(i + 1) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab
/-
**sum_mul_Ico_le_integral_of_monotone_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_mul_Ico_le_integral_of_monotone_antitone (hab : a <= b) (hf : Monotone
On f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1))) (fpos : 0 <= f a) (gpo
s : 0 <= g (b - 1)) : ∑ i in .Ico a b, f i * g i <= ∫ x in a..b, f x * g (x - 1)
参数：hab : a <= b；hf : MonotoneOn f (Icc a b)；hg : AntitoneOn g (Icc (a - 1) (b - 
1))；fpos : 0 <= f a；gpos : 0 <= g (b - 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sum_Ico_le_integral_of_le`：sum_Ico_le_integral_of_le (hab : a <= b) (h :
 forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), f i <= g x) (hg : Int
egrableOn g (Ic…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Integrable.mul_of_top_left`：∀ {α : Type u_1} {m : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   
{f φ : α → 𝕜}, MeasureTheory.I…
· 使用定理 `MonotoneOn.integrableOn_isCompact`：MonotoneOn.integrableOn_isCompact [Is
FiniteMeasureOnCompacts μ] (hs : IsCompact s) (hmono : MonotoneOn f s) : Integra
bleOn f s μ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `AntitoneOn.memLp_isCompact`：AntitoneOn.memLp_isCompact [IsFiniteMeasureO
nCompacts μ] (hs : IsCompact s) (hanti : AntitoneOn f s) : MemLp f p (μ.restrict
 s)
· 使用定理 `MeasureTheory.Measure.restrict_mono_set`：restrict_mono_set {_ : Measurab
leSpace α} (μ : Measure α) {s t : Set α} (h : s subseteq t) : μ.restrict s <= μ.
restrict t
（共 31 条，此处仅展示前 30 条）
-/
lemma sum_mul_Ico_le_integral_of_monotone_antitone
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f a) (gpos : 0 ≤ g (b - 1)) :
    ∑ i ∈ .Ico a b, f i * g i ≤ ∫ x in a..b, f x * g (x - 1) := by
  apply sum_Ico_le_integral_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    · apply hg <;> grind
  · apply Integrable.mono_measure _ (volume.restrict_mono_set Ico_subset_Icc_self)
    apply (hf.integrableOn_isCompact isCompact_Icc).mul_of_top_left
    apply AntitoneOn.memLp_isCompact isCompact_Icc
    intro _ _ _ _ _
    apply hg <;> grind
/-
**integral_le_sum_mul_Ico_of_antitone_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integral_le_sum_mul_Ico_of_antitone_monotone (hab : a <= b) (hf : Antitone
On f (Icc a b)) (hg : MonotoneOn g (Icc (a - 1) (b - 1))) (fpos : 0 <= f b) (gpo
s : 0 <= g (a - 1)) : ∫ x in a..b, f x * g (x - 1) <= ∑ i in .Ico a b, f i * g i
参数：hab : a <= b；hf : AntitoneOn f (Icc a b)；hg : MonotoneOn g (Icc (a - 1) (b - 
1))；fpos : 0 <= f b；gpos : 0 <= g (a - 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `integral_le_sum_Ico_of_le`：integral_le_sum_Ico_of_le (hab : a <= b) (h :
 forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), g x <= f i) (hg : Int
egrableOn g (Ic…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Integrable.mul_of_top_left`：∀ {α : Type u_1} {m : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   
{f φ : α → 𝕜}, MeasureTheory.I…
· 使用定理 `AntitoneOn.integrableOn_isCompact`：AntitoneOn.integrableOn_isCompact [Is
FiniteMeasureOnCompacts μ] (hs : IsCompact s) (hanti : AntitoneOn f s) : Integra
bleOn f s μ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `MonotoneOn.memLp_isCompact`：MonotoneOn.memLp_isCompact [IsFiniteMeasureO
nCompacts μ] (hs : IsCompact s) (hmono : MonotoneOn f s) : MemLp f p (μ.restrict
 s)
· 使用定理 `MeasureTheory.Measure.restrict_mono_set`：restrict_mono_set {_ : Measurab
leSpace α} (μ : Measure α) {s t : Set α} (h : s subseteq t) : μ.restrict s <= μ.
restrict t
（共 31 条，此处仅展示前 30 条）
-/
lemma integral_le_sum_mul_Ico_of_antitone_monotone
    (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) (hg : MonotoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f b) (gpos : 0 ≤ g (a - 1)) :
    ∫ x in a..b, f x * g (x - 1) ≤ ∑ i ∈ .Ico a b, f i * g i := by
  apply integral_le_sum_Ico_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    · apply hg <;> grind
  · apply Integrable.mono_measure _ (volume.restrict_mono_set Ico_subset_Icc_self)
    apply (hf.integrableOn_isCompact isCompact_Icc).mul_of_top_left
    apply MonotoneOn.memLp_isCompact isCompact_Icc
    intro _ _ _ _ _
    apply hg <;> grind

/-! ## Comparison of infinite sums and integrals -/

/-- The partial sums of a nonnegative antitone function are bounded
by the integral over `(a, ∞)`. -/
/-
**AntitoneOn.sum_Ico_le_integral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.sum_Ico_le_integral {a b : Nat} (anti : AntitoneOn f (Icc a b))
 (integrable : IntegrableOn f (Ioi a)) (nonneg : forall t in Ioi (a : Real), 0 <
= f t) : ∑ n in .Ico a b, f ↑(n + 1) <= ∫ x in Ioi (a : Real), f x
参数：anti : AntitoneOn f (Icc a b)；integrable : IntegrableOn f (Ioi a)；nonneg : fo
rall t in Ioi (a : Real), 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `MeasureTheory.setIntegral_nonneg`：setIntegral_nonneg (hs : MeasurableSet
 s) (hf : forall x, x in s -> 0 <= f x) : 0 <= ∫ x in s, f x ∂μ
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
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `AntitoneOn.sum_le_integral_Ico`：AntitoneOn.sum_le_integral_Ico (hab : a 
<= b) (hf : AntitoneOn f (Icc a b)) : ∑ i in .Ico a b, f ↑(i + 1) <= ∫ x in a..b
, f x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.setIntegral_mono_set`：setIntegral_mono_set [OrderClosedTop
ology E] (hfi : IntegrableOn f t μ) (hf : 0 <=ᵐ[μ.restrict t] f) (hst : s <=ᵐ[μ]
 t) : ∫ x in s, f x ∂μ <…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `MeasureTheory.ae_restrict_of_forall_mem`：ae_restrict_of_forall_mem {μ : 
Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} (h : forall x in s
, p x) : forallᵐ (x : α) ∂μ.r…
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b

--- 原说明 ---
The partial sums of a nonnegative antitone function are bounded
by the integral over `(a, ∞)`.
-/
lemma AntitoneOn.sum_Ico_le_integral {a b : ℕ} (anti : AntitoneOn f (Icc a b))
    (integrable : IntegrableOn f (Ioi a)) (nonneg : ∀ t ∈ Ioi (a : ℝ), 0 ≤ f t) :
    ∑ n ∈ .Ico a b, f ↑(n + 1) ≤ ∫ x in Ioi (a : ℝ), f x := by
  by_cases! hab : b < a
  · simpa [Finset.Ico_eq_empty_of_le hab.le] using setIntegral_nonneg measurableSet_Ioi nonneg
  grw [anti.sum_le_integral_Ico hab, integral_of_le (mod_cast hab)]
  apply setIntegral_mono_set integrable _ (Ioc_subset_Ioi_self.eventuallyLE)
  exact ae_restrict_of_forall_mem measurableSet_Ioi nonneg

/-- The partial sums of a nonnegative function are bounded by the integral over `(0, ∞)`. -/
/-
**AntitoneOn.sum_range_le_integral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.sum_range_le_integral {N : Nat} (anti : AntitoneOn f (Icc 0 (N 
: Real))) (integrable : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <
= f t) : ∑ n in Finset.range N, f ((n + 1 : Nat)) <= ∫ x in Ioi 0, f x
参数：anti : AntitoneOn f (Icc 0 (N : Real))；integrable : IntegrableOn f (Ioi 0)；no
nneg : forall t in Ioi 0, 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AntitoneOn.sum_Ico_le_integral`：AntitoneOn.sum_Ico_le_integral {a b : Na
t} (anti : AntitoneOn f (Icc a b)) (integrable : IntegrableOn f (Ioi a)) (nonneg
 : forall t in Ioi (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The partial sums of a nonnegative function are bounded by the integral over `(0,
 ∞)`.
-/
lemma AntitoneOn.sum_range_le_integral {N : ℕ} (anti : AntitoneOn f (Icc 0 (N : ℝ)))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑ n ∈ Finset.range N, f ((n + 1 : ℕ)) ≤ ∫ x in Ioi 0, f x := by
  rw [Finset.range_eq_Ico]
  exact_mod_cast AntitoneOn.sum_Ico_le_integral (a := 0) (mod_cast anti)
    (mod_cast integrable) (mod_cast nonneg)

/-- **Integral test**: A function which is nonnegative, integrable and antitone
for sufficiently large `n` is summable. -/
/-
**AntitoneOn.summable_of_integrableOn_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.summable_of_integrableOn_Ioi {N : Nat} (anti : AntitoneOn f (Ic
i (N : Real))) (integrable : IntegrableOn f (Ioi (N : Real))) (nonneg : forall t
 in Ioi (N : Real), 0 <= f t) : Summable (fun (n : Nat) => f n)
参数：anti : AntitoneOn f (Ici (N : Real))；integrable : IntegrableOn f (Ioi (N : Re
al))；nonneg : forall t in Ioi (N : Real), 0 <= f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `summable_of_sum_range_le`：summable_of_sum_range_le {f : Nat -> Real} {c 
: Real} (hf : forall n, 0 <= f n) (h : forall n, ∑ i in Finset.range n, f i <= c
) : Summable f
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用引理 `AntitoneOn.sum_Ico_le_integral`：AntitoneOn.sum_Ico_le_integral {a b : Na
t} (anti : AntitoneOn f (Icc a b)) (integrable : IntegrableOn f (Ioi a)) (nonneg
 : forall t in Ioi (…
· 使用定理 `AntitoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   AntitoneOn f s → s₂ ⊆ s → Antit
oneOn…
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b

--- 原说明 ---
**Integral test**: A function which is nonnegative, integrable and antitone
for sufficiently large `n` is summable.
-/
theorem AntitoneOn.summable_of_integrableOn_Ioi {N : ℕ} (anti : AntitoneOn f (Ici (N : ℝ)))
    (integrable : IntegrableOn f (Ioi (N : ℝ))) (nonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t) :
    Summable (fun (n : ℕ) ↦ f n) := by
  rw [← summable_nat_add_iff (N + 1)]
  refine summable_of_sum_range_le (c := ∫ t in Ioi (N : ℝ), f t) (by grind) fun M ↦ ?_
  calc
    _ = ∑ n ∈ Finset.Ico N (N + M), f (n + 1 : ℕ) := by rw [Finset.sum_Ico_eq_sum_range]; grind
    _ ≤ _ := (anti.mono Icc_subset_Ici_self).sum_Ico_le_integral integrable nonneg

/-- **Integral test**: a nonnegative antitone function is summable if it is integrable. -/
/-
**AntitoneOn.summable_of_integrableOn_Ioi_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.summable_of_integrableOn_Ioi_zero (anti : AntitoneOn f (Ici 0))
 (integrable : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) : 
Summable (fun (n : Nat) => f n)
参数：anti : AntitoneOn f (Ici 0)；integrable : IntegrableOn f (Ioi 0)；nonneg : fora
ll t in Ioi 0, 0 <= f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.summable_of_integrableOn_Ioi`：AntitoneOn.summable_of_integrab
leOn_Ioi {N : Nat} (anti : AntitoneOn f (Ici (N : Real))) (integrable : Integrab
leOn f (Ioi (N : Real))) (non…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
**Integral test**: a nonnegative antitone function is summable if it is integrab
le.
-/
theorem AntitoneOn.summable_of_integrableOn_Ioi_zero (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    Summable (fun (n : ℕ) ↦ f n) :=
  summable_of_integrableOn_Ioi (N := 0) (mod_cast anti) (mod_cast integrable) (mod_cast nonneg)

open Filter Finset in
/-
**AntitoneOn.tsum_comp_add_le_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.tsum_comp_add_le_integral (N : Nat) (anti : AntitoneOn f (Ici (
N : Real))) (integrable : IntegrableOn f (Ioi (N : Real))) (nonneg : forall t in
 Ioi (N : Real), 0 <= f t) : ∑' (n : Nat), f (n + N + 1 : Nat) <= ∫ x in Ioi (N 
: Real), f x
参数：N : Nat；anti : AntitoneOn f (Ici (N : Real))；integrable : IntegrableOn f (Ioi
 (N : Real))；nonneg : forall t in Ioi (N : Real), 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_le_of_sum_le'`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter
 ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : TopologicalSpace 
α] [Orde…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)
· 使用引理 `AntitoneOn.sum_Ico_le_integral`：AntitoneOn.sum_Ico_le_integral {a b : Na
t} (anti : AntitoneOn f (Icc a b)) (integrable : IntegrableOn f (Ioi a)) (nonneg
 : forall t in Ioi (…
· 使用定理 `AntitoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   AntitoneOn f s → s₂ ⊆ s → Antit
oneOn…
-/
theorem AntitoneOn.tsum_comp_add_le_integral (N : ℕ) (anti : AntitoneOn f (Ici (N : ℝ)))
    (integrable : IntegrableOn f (Ioi (N : ℝ))) (nonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t) :
    ∑' (n : ℕ),  f (n + N + 1 : ℕ) ≤ ∫ x in Ioi (N : ℝ), f x := by
  refine tsum_le_of_sum_le' (integral_nonneg_of_ae ?_) fun s ↦ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] using nonneg
  · obtain ⟨t, ht⟩ := tendsto_finset_range.eventually (Ici_mem_atTop s) |>.exists
    calc
      ∑ i ∈ s, f ↑(i + N + 1) ≤ ∑ i ∈ range t, f ↑(i + N + 1) :=
        sum_le_sum_of_subset_of_nonneg ht <| by grind
      _ = ∑ i ∈ Ico N (N + t), f ↑(i + 1) := by rw [Finset.sum_Ico_eq_sum_range]; grind
      _ ≤ ∫ (x : ℝ) in Set.Ioi (N : ℝ), f x :=
        (anti.mono <| by grind).sum_Ico_le_integral integrable nonneg

/-- **Integral test**: bounds the sum from 1 by an integral. -/
/-
**AntitoneOn.tsum_add_one_le_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.tsum_add_one_le_integral (anti : AntitoneOn f (Ici 0)) (integra
ble : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) : ∑' (n : N
at), f (n + 1 : Nat) <= ∫ x in Ioi 0, f x
参数：anti : AntitoneOn f (Ici 0)；integrable : IntegrableOn f (Ioi 0)；nonneg : fora
ll t in Ioi 0, 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AntitoneOn.tsum_comp_add_le_integral`：AntitoneOn.tsum_comp_add_le_integr
al (N : Nat) (anti : AntitoneOn f (Ici (N : Real))) (integrable : IntegrableOn f
 (Ioi (N : Real))) (nonneg…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
**Integral test**: bounds the sum from 1 by an integral.
-/
theorem AntitoneOn.tsum_add_one_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑' (n : ℕ),  f (n + 1 : ℕ) ≤ ∫ x in Ioi 0, f x  := by
  exact_mod_cast AntitoneOn.tsum_comp_add_le_integral 0 (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)

/-- **Integral test**: bounds the sum of a nonnegative antitone function by an integral. -/
/-
**AntitoneOn.tsum_le_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.tsum_le_integral (anti : AntitoneOn f (Ici 0)) (integrable : In
tegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) : ∑' (n : Nat), f n
 <= f 0 + ∫ x in Ioi 0, f x
参数：anti : AntitoneOn f (Ici 0)；integrable : IntegrableOn f (Ioi 0)；nonneg : fora
ll t in Ioi 0, 0 <= f t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Integral test**: bounds the sum of a nonnegative antitone function by an integ
ral.
-/
theorem AntitoneOn.tsum_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑' (n : ℕ),  f n ≤ f 0 + ∫ x in Ioi 0, f x  := by
  grind [(anti.summable_of_integrableOn_Ioi_zero integrable nonneg).tsum_eq_zero_add,
    anti.tsum_add_one_le_integral integrable nonneg]

/-- Bounds the difference between a sum and its partial sums by an integral. -/
/-
**AntitoneOn.abs_tsum_sub_sum_range_le_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.abs_tsum_sub_sum_range_le_integral {N : Nat} (hN : 1 <= N) (ant
i : AntitoneOn f (Ici (N - 1 : Real))) (integrable : IntegrableOn f (Ioi (N - 1 
: Real))) (nonneg : forall t in Ioi (N - 1 : Real), 0 <= f t) : |(∑' (n : Nat), 
f n) - ∑ n in Finset.range N, f n| <= ∫ x in Ioi (N - 1 : Real), f x
参数：hN : 1 <= N；anti : AntitoneOn f (Ici (N - 1 : Real))；integrable : IntegrableO
n f (Ioi (N - 1 : Real))；nonneg : forall t in Ioi (N - 1 : Real), 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_nat_add`：∀ {G : Type u_2} [inst : AddCommGroup G] 
[inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] {f : ℕ → G} 
  (k : ℕ), Summable…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `AntitoneOn.summable_of_integrableOn_Ioi`：AntitoneOn.summable_of_integrab
leOn_Ioi {N : Nat} (anti : AntitoneOn f (Ici (N : Real))) (integrable : Integrab
leOn f (Ioi (N : Real))) (non…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AntitoneOn.tsum_comp_add_le_integral`：AntitoneOn.tsum_comp_add_le_integr
al (N : Nat) (anti : AntitoneOn f (Ici (N : Real))) (integrable : IntegrableOn f
 (Ioi (N : Real))) (nonneg…

--- 原说明 ---
Bounds the difference between a sum and its partial sums by an integral.
-/
theorem AntitoneOn.abs_tsum_sub_sum_range_le_integral {N : ℕ} (hN : 1 ≤ N)
    (anti : AntitoneOn f (Ici (N - 1 : ℝ)))
    (integrable : IntegrableOn f (Ioi (N - 1 : ℝ))) (nonneg : ∀ t ∈ Ioi (N - 1 : ℝ), 0 ≤ f t) :
    |(∑' (n : ℕ), f n) - ∑ n ∈ Finset.range N, f n| ≤ ∫ x in Ioi (N - 1 : ℝ), f x := by
  rw [← (AntitoneOn.summable_of_integrableOn_Ioi (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)).sum_add_tsum_nat_add N, add_sub_cancel_left,
    abs_of_nonneg (tsum_nonneg <| by grind)]
  convert! AntitoneOn.tsum_comp_add_le_integral (N - 1) (mod_cast anti) (mod_cast integrable)
      (mod_cast nonneg) using 1
  · congr; ext; congr 2; grind
  · norm_cast

open Filter in
/-- Converse to the integral test: a nonnegative, integrable, summable function is integrable. -/
/-
**AntitoneOn.integrableOn_Ioi_of_summable_comp_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integrableOn_Ioi_of_summable_comp_add {N : Nat} (anti : Antiton
eOn f (Ici (N : Real))) (summable : Summable (fun n => f (n + N : Nat))) (nonneg
 : forall t in Ioi (N : Real), 0 <= f t) : IntegrableOn f (Ioi (N : Real))
参数：anti : AntitoneOn f (Ici (N : Real))；summable : Summable (fun n => f (n + N :
 Nat))；nonneg : forall t in Ioi (N : Real), 0 <= f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded`：integra
bleOn_Ioi_of_intervalIntegral_norm_bounded (I a : Real) (hfi : forall i, Integra
bleOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop) (h …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `AntitoneOn.intervalIntegrable`：AntitoneOn.intervalIntegrable {u : Real -
> E} {a b : Real} (hu : AntitoneOn u (uIcc a b)) : IntervalIntegrable u μ a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AntitoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   AntitoneOn f s → s₂ ⊆ s → Antit
oneOn…
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `intervalIntegral.integral_congr_uIoo`：integral_congr_uIoo [NullSingleton
Class μ] (h : (uIoo a b).EqOn f g) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AntitoneOn.integral_le_sum`：AntitoneOn.integral_le_sum (hf : AntitoneOn 
f (Icc x₀ (x₀ + a))) : ∫ x in x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + i)

--- 原说明 ---
Converse to the integral test: a nonnegative, integrable, summable function is i
ntegrable.
-/
theorem AntitoneOn.integrableOn_Ioi_of_summable_comp_add {N : ℕ} (anti : AntitoneOn f (Ici (N : ℝ)))
    (summable : Summable (fun n ↦ f (n + N : ℕ))) (nonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t) :
    IntegrableOn f (Ioi (N : ℝ)) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (∑' (n : ℕ), f (n + N : ℕ)) _ ?_
    (tendsto_atTop_add_const_right atTop (N : ℝ) tendsto_natCast_atTop_atTop) ?_
  · intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by grind)]
    exact (anti.mono <| by grind [uIcc_of_le]).intervalIntegrable
  · filter_upwards [eventually_gt_atTop 0] with M hM
    calc
      _ = ∫ x in N..M+N, f x := by
        refine intervalIntegral.integral_congr_uIoo fun x ↦ ?_
        grind [Real.norm_of_nonneg, uIoo_of_le]
      _ ≤ ∑ n ∈ Finset.range M, f (n + N : ℕ) := by
        convert! AntitoneOn.integral_le_sum (anti.mono _) using 2 <;> grind
      _ ≤ _ := by grind [summable.sum_le_tsum, Nat.cast_pos]

/-- Converse to the integral test: a nonnegative, integrable, summable function is integrable. -/
/-
**AntitoneOn.integrableOn_Ioi_zero_of_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integrableOn_Ioi_zero_of_summable (anti : AntitoneOn f (Ici 0))
 (summable : Summable (fun (n : Nat) => f n)) (nonneg : forall t in Ioi 0, 0 <= 
f t) : IntegrableOn f (Ioi 0)
参数：anti : AntitoneOn f (Ici 0)；summable : Summable (fun (n : Nat) => f n)；nonneg
 : forall t in Ioi 0, 0 <= f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AntitoneOn.integrableOn_Ioi_of_summable_comp_add`：AntitoneOn.integrableO
n_Ioi_of_summable_comp_add {N : Nat} (anti : AntitoneOn f (Ici (N : Real))) (sum
mable : Summable (fun n => f (n + N : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Converse to the integral test: a nonnegative, integrable, summable function is i
ntegrable.
-/
theorem AntitoneOn.integrableOn_Ioi_zero_of_summable (anti : AntitoneOn f (Ici 0))
    (summable : Summable (fun (n : ℕ) ↦ f n)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    IntegrableOn f (Ioi 0) :=
  mod_cast AntitoneOn.integrableOn_Ioi_of_summable_comp_add (N := 0) (mod_cast anti) summable
    (mod_cast nonneg)

open Filter in
/-- The sum of a nonnegative, antitone function is bounded below by its integral. -/
/-
**AntitoneOn.integral_le_tsum_comp_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integral_le_tsum_comp_add (N : Nat) (anti : AntitoneOn f (Ici (
N : Real))) (summable : Summable (fun (n : Nat) => f n)) (nonneg : forall t in I
oi (N : Real), 0 <= f t) : ∫ x in Ioi (N : Real), f x <= ∑' (n : Nat), f (n + N 
: Nat)
参数：N : Nat；anti : AntitoneOn f (Ici (N : Real))；summable : Summable (fun (n : Na
t) => f n)；nonneg : forall t in Ioi (N : Real), 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tendsto_sum_tsum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M]
 [inst_1 : TopologicalSpace M] {f : ℕ → M},   Summable f → Filter.Tendsto (fun n
 => ∑ i ∈ Finset.ra…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `AntitoneOn.integrableOn_Ioi_of_summable_comp_add`：AntitoneOn.integrableO
n_Ioi_of_summable_comp_add {N : Nat} (anti : AntitoneOn f (Ici (N : Real))) (sum
mable : Summable (fun n => f (n + N : …
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
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
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AntitoneOn.integral_le_sum_Ico`：AntitoneOn.integral_le_sum_Ico (hab : a 
<= b) (hf : AntitoneOn f (Set.Icc a b)) : ∫ x in a..b, f x <= ∑ x in .Ico a b, f
 x
· 使用定理 `Finset.sum_Ico_eq_sum_range`：∀ {M : Type u_3} [inst : AddCommMonoid M] (
f : ℕ → M) (m n : ℕ),   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range (n - m), 
f (m + k)

--- 原说明 ---
The sum of a nonnegative, antitone function is bounded below by its integral.
-/
theorem AntitoneOn.integral_le_tsum_comp_add (N : ℕ) (anti : AntitoneOn f (Ici (N : ℝ)))
    (summable : Summable (fun (n : ℕ) ↦ f n)) (nonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ f t) :
    ∫ x in Ioi (N : ℝ), f x ≤ ∑' (n : ℕ),  f (n + N : ℕ) := by
  rw [← summable_nat_add_iff N] at summable
  have lim := summable.tendsto_sum_tsum_nat
  have  := tendsto_atTop_add_const_right atTop (N : ℝ) tendsto_natCast_atTop_atTop
  have integrable := anti.integrableOn_Ioi_of_summable_comp_add summable nonneg
  refine le_of_tendsto_of_tendsto (intervalIntegral_tendsto_integral_Ioi N integrable this) lim ?_
  filter_upwards with M
  calc
    _ ≤ ∑ n ∈ Finset.Ico N (N + M), f n := by
      convert!  AntitoneOn.integral_le_sum_Ico _ _ using 2 <;> grind [anti.mono]
    _ = _ := by
      rw [Finset.sum_Ico_eq_sum_range]
      grind

/-- The sum of a nonnegative, antitone function is bounded below by its integral. -/
/-
**AntitoneOn.integral_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.integral_le_tsum (anti : AntitoneOn f (Ici 0)) (summable : Summ
able (fun (n : Nat) => f n)) (nonneg : forall t in Ioi 0, 0 <= f t) : ∫ x in Ioi
 0, f x <= ∑' (n : Nat), f n
参数：anti : AntitoneOn f (Ici 0)；summable : Summable (fun (n : Nat) => f n)；nonneg
 : forall t in Ioi 0, 0 <= f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AntitoneOn.integral_le_tsum_comp_add`：AntitoneOn.integral_le_tsum_comp_a
dd (N : Nat) (anti : AntitoneOn f (Ici (N : Real))) (summable : Summable (fun (n
 : Nat) => f n)) (nonneg :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The sum of a nonnegative, antitone function is bounded below by its integral.
-/
theorem AntitoneOn.integral_le_tsum (anti : AntitoneOn f (Ici 0))
    (summable : Summable (fun (n : ℕ) ↦ f n)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∫ x in Ioi 0, f x ≤ ∑' (n : ℕ),  f n :=
  mod_cast AntitoneOn.integral_le_tsum_comp_add 0 (mod_cast anti) summable (mod_cast nonneg)
