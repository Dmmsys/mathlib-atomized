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

variable {R σ : Type*} (v : R → ℝ) (c : σ → ℝ) (f : MvPowerSeries σ R)

section Semiring

variable [Semiring R]

/-- Given a multivariate power series `f` in, a function `v : R → ℝ` and a tuple `c` of real
  numbers, the Gauss norm is defined as the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`. -/
/-
**MvPowerSeries.gaussNorm** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multivariate power series `f` in, a function `v : R → ℝ` and a tuple `c`
 of real
  numbers, the Gauss norm is defined as the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.
-/
noncomputable def gaussNorm : ℝ :=
   ⨆ t : σ →₀ ℕ, v (coeff t f) * t.prod (c · ^ ·)

/-- We say `f` HasGaussNorm if the values `v (coeff t f) * ∏ i : t.support, c i` is bounded above,
  that is `gaussNorm f` is finite. -/
/-
**MvPowerSeries.HasGaussNorm** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPowerSeries`。
形式化陈述：HasGaussNorm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `f` HasGaussNorm if the values `v (coeff t f) * ∏ i : t.support, c i` is 
bounded above,
  that is `gaussNorm f` is finite.
-/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : σ →₀ ℕ) ↦ (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]
/-
**MvPowerSeries.gaussNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0
参数：vZero : v 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 := by simp [gaussNorm, vZero]
/-
**MvPowerSeries.le_gaussNorm** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_gaussNorm (hbd : HasGaussNorm v c f) (t : σ ->₀ Nat) : v (coeff t f) * 
t.prod (c · ^ ·) <= gaussNorm v c f
参数：hbd : HasGaussNorm v c f；t : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : σ →₀ ℕ) :
    v (coeff t f) * t.prod (c · ^ ·) ≤ gaussNorm v c f := by
  apply le_ciSup hbd
/-
**MvPowerSeries.gaussNorm_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_nonneg (vNonneg : forall a, v a >= 0) : 0 <= gaussNorm v c f
参数：vNonneg : forall a, v a >= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.gaussNorm.eq_1`：∀ {R : Type u_1} {σ : Type u_2} (v : R → ℝ
) (c : σ → ℝ) (f : MvPowerSeries σ R) [inst : Semiring R],   MvPowerSeries.gauss
Norm v c f = ⨆ t, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MvPowerSeries.le_gaussNorm`：le_gaussNorm (hbd : HasGaussNorm v c f) (t :
 σ ->₀ Nat) : v (coeff t f) * t.prod (c · ^ ·) <= gaussNorm v c f
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
-/
lemma gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f := by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert! (le_gaussNorm v c f h 0)
      simp
  · simp [h]
/-
**MvPowerSeries.gaussNorm_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : forall a, v a >= 0) (h_
eq_zero : forall x : R, v x = 0 -> x = 0) (hc : forall i, 0 < c i) (hbd : HasGau
ssNorm v c f) : gaussNorm v c f = 0 ↔ f = 0
参数：vZero : v 0 = 0；vNonneg : forall a, v a >= 0；h_eq_zero : forall x : R, v x = 
0 -> x = 0；hc : forall i, 0 < c i；hbd : HasGaussNorm v c f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero`：ne_zero_iff_exists_coeff
_ne_zero (f : MvPowerSeries σ R) : f != 0 ↔ (exists d : σ ->₀ Nat, coeff d f != 
0)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用引理 `MvPowerSeries.le_gaussNorm`：le_gaussNorm (hbd : HasGaussNorm v c f) (t :
 σ ->₀ Nat) : v (coeff t f) * t.prod (c · ^ ·) <= gaussNorm v c f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.gaussNorm_zero`：gaussNorm_zero (vZero : v 0 = 0) : gaussNo
rm v c 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i ∈ n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a ↦ (fun i ↦ pow_pos (hc i) (n i)) i)
    specialize h_eq_zero (f.coeff n)
    grind
  _ ≤ _ := le_gaussNorm v c f hbd n
/-
**MvPowerSeries.gaussNorm_add_le_max** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_add_le_max (f g : MvPowerSeries σ R) (hc : 0 <= c) (vNonneg : fo
rall a, v a >= 0) (hv : IsNonarchimedean v) (hbfd : HasGaussNorm v c f) (hbgd : 
HasGaussNorm v c g) : gaussNorm v c (f + g) <= max (gaussNorm v c f) (gaussNorm 
v c g)
参数：f g : MvPowerSeries σ R；hc : 0 <= c；vNonneg : forall a, v a >= 0；hv : IsNonar
chimedean v；hbfd : HasGaussNorm v c f；hbgd : HasGaussNorm v c g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `max_choice`：∀ {α : Type u} [inst : LinearOrder α] (a b : α), max a b = a
 ∨ max a b = b
· 使用定理 `mul_le_mul_of_nonneg`：mul_le_mul_of_nonneg [PosMulMono α] [MulPosMono α]
 (h₁ : a <= b) (h₂ : c <= d) (a0 : 0 <= a) (d0 : 0 <= d) : a * c <= b * d
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Real.iSup_le`：∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), f i ≤ a)
 → 0 ≤ a → ⨆ i, f i ≤ a
· 使用引理 `MvPowerSeries.le_gaussNorm`：le_gaussNorm (hbd : HasGaussNorm v c f) (t :
 σ ->₀ Nat) : v (coeff t f) * t.prod (c · ^ ·) <= gaussNorm v c f
· 使用引理 `MvPowerSeries.gaussNorm_nonneg`：gaussNorm_nonneg (vNonneg : forall a, v 
a >= 0) : 0 <= gaussNorm v c f
-/
lemma gaussNorm_add_le_max (f g : MvPowerSeries σ R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : IsNonarchimedean v)
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
  have H (t : σ →₀ ℕ) : 0 ≤ ∏ i ∈ t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi ↦ pow_nonneg (hc i) (t i))
  have Final (t : σ →₀ ℕ) : v ((coeff t) (f + g)) * ∏ i ∈ t.support, c ↑i ^ t ↑i ≤
      max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
    specialize hv (coeff t f) (coeff t g)
    rcases max_choice (v ((coeff t) f)) (v ((coeff t) g)) with h | h
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_left]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_right]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
  refine Real.iSup_le ?_ ?_
  · refine fun t ↦ calc
    _ ≤ _ := Final t
    _ ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
      simp only [le_sup_iff]
      rcases max_choice (v ((coeff t) f) * ∏ i ∈ t.support, c i ^ t i)
        (v ((coeff t) g) * ∏ i ∈ t.support, c i ^ t i) with h | h
      · left
        simpa [h] using! le_gaussNorm v c f hbfd t
      · right
        simpa [h] using! le_gaussNorm v c g hbgd t
  · simp only [le_sup_iff]
    left
    exact gaussNorm_nonneg v c f vNonneg
/-
**MvPowerSeries.c_prod_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma c_prod_nonneg (hc : 0 ≤ c) (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hc i) (t i))
/-
**MvPowerSeries.gaussNorm_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_mul_le (f g : MvPowerSeries σ R) (hc : 0 <= c) (vNonneg : forall
 a, v a >= 0) (vMul : forall a b, v (a * b) <= v a * v b) (vna : IsNonarchimedea
n v) (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
 gaussNorm v c (f * g) <= gaussNorm v c f * gaussNorm v c g
参数：f g : MvPowerSeries σ R；hc : 0 <= c；vNonneg : forall a, v a >= 0；vMul : foral
l a b, v (a * b) <= v a * v b；vna : IsNonarchimedean v；vZero : v 0 = 0；hbfd : Ha
sGaussNorm v c f；hbgd : HasGaussNorm v c g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.iSup_le`：∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), f i ≤ a)
 → 0 ≤ a → ⨆ i, f i ≤ a
· 使用引理 `IsNonarchimedean.finset_image_add`：finset_image_add {α β : Type*} [AddCo
mmMonoid α] [Nonempty β] {f : α -> R} (f_zero : f 0 = 0) (f_nonneg : forall x, 0
 <= f x) (hna : IsNonar…
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_def`：nonempty_def {s : Finset α} : s.Nonempty ↔ exists x
, x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.GaussNorm.0.MvPowerSeries.c_pr
od_nonneg`：∀ {σ : Type u_2} (c : σ → ℝ), 0 ≤ c → ∀ (t : σ →₀ ℕ), 0 ≤ t.prod fun 
x1 x2 => c x1 ^ x2
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 36 条，此处仅展示前 30 条）
-/
lemma gaussNorm_mul_le (f g : MvPowerSeries σ R) (hc : 0 ≤ c) (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (vna : IsNonarchimedean v)
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) ≤ gaussNorm v c f * gaussNorm v c g := by
  classical
  refine Real.iSup_le ?_ ?_
  · intro t
    obtain ⟨k, hk, hsum⟩ := IsNonarchimedean.finset_image_add vZero vNonneg vna
      (fun a ↦ coeff a.1 f * coeff a.2 g) (Finset.antidiagonal t)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk (Finset.nonempty_def.mpr ⟨(t, 0), by simp⟩)
    have hprod : t.prod (c · ^ ·) = k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·) := by
      simp [← hk', Finsupp.prod_add_index' (h := (c · ^ ·)) (by grind) (by grind)]
    rw [hprod]
    refine (mul_le_mul hsum (by rfl) (mul_nonneg (c_prod_nonneg c hc k.1) (c_prod_nonneg c hc k.2))
      (vNonneg _)).trans ?_
    have : v ((coeff k.1) f * (coeff k.2) g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) ≤
        (v (coeff k.1 f) * k.1.prod (c · ^ ·)) * (v (coeff k.2 g) * k.2.prod (c · ^ ·)) := by
      calc
      _ ≤ v (coeff k.1 f) * v (coeff k.2 g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) :=
        mul_le_mul (vMul _ _) (by rfl) (mul_nonneg (c_prod_nonneg c hc k.1)
          (c_prod_nonneg c hc k.2)) (mul_nonneg (vNonneg _) (vNonneg _))
      _ = _ := by ring
    exact this.trans (mul_le_mul (le_gaussNorm v c f hbfd k.1) (le_gaussNorm v c g hbgd k.2)
      (mul_nonneg (vNonneg _) (c_prod_nonneg c hc k.2)) (gaussNorm_nonneg v c f vNonneg))
  · exact mul_nonneg (gaussNorm_nonneg v c f vNonneg) (gaussNorm_nonneg v c g vNonneg)

end Semiring

variable [Ring R]

/-- Predicate for when the gaussNorm is achieved by an index. -/
/-
**MvPowerSeries.AchievesGaussNorm** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPowerSeries`。
形式化陈述：AchievesGaussNorm (i : σ ->₀ Nat) : Prop
参数：i : σ ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for when the gaussNorm is achieved by an index.
-/
abbrev AchievesGaussNorm (i : σ →₀ ℕ) : Prop :=
  v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f
/-
**MvPowerSeries.gaussNorm_neg** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_neg (vNeg : forall x, v (-x) = v x) (f : MvPowerSeries σ R) : ga
ussNorm v c (-f) = gaussNorm v c f
参数：vNeg : forall x, v (-x) = v x；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussNorm_neg (vNeg : ∀ x, v (-x) = v x) (f : MvPowerSeries σ R) :
    gaussNorm v c (-f) = gaussNorm v c f  := by
  simp_rw [gaussNorm]
  have (t : σ →₀ ℕ) : (coeff t) (-f) = - (coeff t) f := by rfl
  simp_rw [this, vNeg]

section absoluteValue

variable {α S : Type*} [LinearOrder S] [AddCommGroup α] (f : α → S)

/-
**MvPowerSeries.ultrametric_strict** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：ultrametric_strict (na : IsNonarchimedean f) (Neg : forall a, f a = f (-a)
) {a b : α} (hne : f a != f b) : f (a + b) = max (f a) (f b)
参数：na : IsNonarchimedean f；Neg : forall a, f a = f (-a)；hne : f a != f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
lemma ultrametric_strict (na : IsNonarchimedean f)
    (Neg : ∀ a, f a = f (-a)) {a b : α} (hne : f a ≠ f b) : f (a + b) = max (f a) (f b) := by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (na a b)
  rcases le_max_iff.mp (na (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa [Neg b] using hab))

variable [Semiring S]
/-
**MvPowerSeries.Finset.Nonempty.map_sum_le_sup'_map** 是 Mathlib 中的一个定理，位于命名空间 `M
vPowerSeries.Finset.Nonempty`。
形式化陈述：∀ {α : Type u_5} {S : Type u_6} [inst : LinearOrder S] [inst_1 : AddCommMo
noid α] (g : α → S) {ι : Type u_7}   {s : Finset ι} (hs : s.Nonempty) (f : ι → α
),   (∀ (a b : α), g (a + b) ≤ max (g a) (g b)) → g (∑ i ∈ s, f i) ≤ s.sup' hs f
un x => g (f x)
参数：g : α → S；hs : s.Nonempty；f : ι → α；∀ (a b : α), g (a + b) ≤ max (g a) (g b)；
∑ i ∈ s, f i；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
lemma Finset.Nonempty.map_sum_le_sup'_map
    {α S : Type*} [LinearOrder S] [AddCommMonoid α] (g : α → S)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → α)
    (na : ∀ a b, g (a + b) ≤ max (g a) (g b)) :
    g (∑ i ∈ s, f i) ≤ s.sup' hs fun x ↦ g (f x) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total (g (∑ i ∈ s, f i)) (g (f j))).imp ?_ ?_ <;> intro h
      · exact (na _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (na _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

variable [DecidableEq σ] (f g : MvPowerSeries σ R)
/-
**MvPowerSeries.antidiagonal_dominant** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：antidiagonal_dominant (i j : σ ->₀ Nat) (vna : IsNonarchimedean v) (vMulEq
 : forall a b, v (a * b) = v a * v b) (vNeg : forall a, v a = v (-a)) (hdom : fo
rall p in Finset.antidiagonal (i + j), p != (i, j) -> v (coeff p.1 f * coeff p.2
 g) < v (coeff i f) * v (coeff j g)) : v (coeff (i + j) (f * g)) = v (coeff i f 
* coeff j g)
参数：i j : σ ->₀ Nat；vna : IsNonarchimedean v；vMulEq : forall a b, v (a * b) = v a
 * v b；vNeg : forall a, v a = v (-a)；hdom : forall p in Finset.antidiagonal (i +
 j), p != (i, j) -> v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用引理 `IsNonarchimedean.apply_sum_eq_of_lt`：apply_sum_eq_of_lt {α β : Type*} [A
ddCommGroup α] {f : α -> R} (fna : IsNonarchimedean f) (f_neg : forall a, f a = 
f (-a)) {s : Finset β} {l…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma antidiagonal_dominant (i j : σ →₀ ℕ) (vna : IsNonarchimedean v)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vNeg : ∀ a, v a = v (-a))
    (hdom : ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
      v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    v (coeff (i + j) (f * g))  = v (coeff i f * coeff j g) := by
  rw [← vMulEq] at hdom
  rw [coeff_mul, IsNonarchimedean.apply_sum_eq_of_lt vna (by grind) (k := (i, j))
    (s := Finset.antidiagonal (i + j)) (Finset.mem_antidiagonal.mpr rfl) hdom]
/-
**MvPowerSeries.gaussNorm_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_le_mul (vMulEq : forall a b, v (a * b) = v a * v b) (vna : IsNon
archimedean v) (vNeg : forall a, v a = v (-a)) (hbfg : HasGaussNorm v c (f * g))
 (hdom : exists i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧ for
all p in Finset.antidiagonal (i + j), p != (i, j) -> v (coeff p.1 f * coeff p.2 
g) < v (coeff i f) * v (coeff j g)) : gaussNorm v c f * gaussNorm v c g <= gauss
Norm v c (f * g)
参数：vMulEq : forall a b, v (a * b) = v a * v b；vna : IsNonarchimedean v；vNeg : fo
rall a, v a = v (-a)；hbfg : HasGaussNorm v c (f * g)；hdom : exists i j, Achieves
GaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧ forall p in Finset.antidiagonal 
(i + j), p != (i, j) -> v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff
 j g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用引理 `MvPowerSeries.antidiagonal_dominant`：antidiagonal_dominant (i j : σ ->₀ 
Nat) (vna : IsNonarchimedean v) (vMulEq : forall a b, v (a * b) = v a * v b) (vN
eg : forall a, v a = v (-…
· 使用引理 `MvPowerSeries.le_gaussNorm`：le_gaussNorm (hbd : HasGaussNorm v c f) (t :
 σ ->₀ Nat) : v (coeff t f) * t.prod (c · ^ ·) <= gaussNorm v c f
-/
lemma gaussNorm_le_mul (vMulEq : ∀ a b, v (a * b) = v a * v b)
    (vna : IsNonarchimedean v) (vNeg : ∀ a, v a = v (-a))
    (hbfg : HasGaussNorm v c (f * g))
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    gaussNorm v c f * gaussNorm v c g ≤ gaussNorm v c (f * g) := by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _  = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀, ← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          have hprod : (i₀ + j₀).prod (c · ^ ·) = i₀.prod (c · ^ ·) * j₀.prod (c · ^ ·) := by
            simp [Finsupp.prod_add_index', pow_add]
          rw [hprod]; ring
    _ = v (coeff i₀ f * coeff j₀ g) * (i₀ + j₀).prod (c · ^ ·) := by rw [vMulEq]
    _ = v (coeff (i₀ + j₀) (f * g)) * (i₀ + j₀).prod (c · ^ ·) := by
      rw [antidiagonal_dominant v f g i₀ j₀ vna vMulEq vNeg hdom']
    _ ≤ gaussNorm v c (f * g) := le_gaussNorm v c (f * g) hbfg (i₀ + j₀)
/-
**MvPowerSeries.gaussNorm_mul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：gaussNorm_mul_eq_mul (f g : MvPowerSeries σ R) (hf : HasGaussNorm v c f) (
hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g)) (vNonneg : forall a, v
 a >= 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v) (vMulEq : forall (a b : R)
, v (a * b) = v a * v b) (vNeg : forall (a : R), v (-a) = v a) (h_eq_zero : fora
ll (x : R), v x = 0 -> x = 0) (hc : forall (i : σ), 0 < c i) (hdom : exists i j,
 AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧ forall p in Finset.anti
diagonal (i + j), p != (i,
参数：f g : MvPowerSeries σ R；hf : HasGaussNorm v c f；hg : HasGaussNorm v c g；hfg :
 HasGaussNorm v c (f * g)；vNonneg : forall a, v a >= 0；vZero : v 0 = 0；vNA : IsN
onarchimedean v；vMulEq : forall (a b : R), v (a * b) = v a * v b；vNeg : forall (
a : R), v (-a) = v a；h_eq_zero : forall (x : R), v x = 0 -> x = 0；hc : forall (i
 : σ), 0 < c i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPowerSeries.gaussNorm_zero`：gaussNorm_zero (vZero : v 0 = 0) : gaussNo
rm v c 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `MvPowerSeries.gaussNorm_eq_zero_iff`：gaussNorm_eq_zero_iff (vZero : v 0 
= 0) (vNonneg : forall a, v a >= 0) (h_eq_zero : forall x : R, v x = 0 -> x = 0)
 (hc : forall i, 0 < c i)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ge_antisymm_iff`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a =
 b ↔ b ≤ a ∧ a ≤ b
· 使用引理 `MvPowerSeries.gaussNorm_le_mul`：gaussNorm_le_mul (vMulEq : forall a b, v
 (a * b) = v a * v b) (vna : IsNonarchimedean v) (vNeg : forall a, v a = v (-a))
 (hbfg : HasGaussNor…
· 使用引理 `MvPowerSeries.gaussNorm_mul_le`：gaussNorm_mul_le (f g : MvPowerSeries σ 
R) (hc : 0 <= c) (vNonneg : forall a, v a >= 0) (vMul : forall a b, v (a * b) <=
 v a * v b) (vna : I…
· 使用定理 `StrongLT.le`：∀ {ι : Type u_1} {π : ι → Type u_4} [inst : (i : ι) → Preor
der (π i)] {a b : (i : ι) → π i}, StrongLT a b → a ≤ b
-/
lemma gaussNorm_mul_eq_mul (f g : MvPowerSeries σ R) (hf : HasGaussNorm v c f)
    (hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g))
    (vNonneg : ∀ a, v a ≥ 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v)
    (vMulEq : ∀ (a b : R), v (a * b) = v a * v b) (vNeg : ∀ (a : R), v (-a) = v a)
    (h_eq_zero : ∀ (x : R), v x = 0 → x = 0) (hc : ∀ (i : σ), 0 < c i)
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) → v (coeff p.1 f * coeff p.2 g) <
      v (coeff i f) * v (coeff j g)) :
    gaussNorm v c (f * g) = gaussNorm v c f * gaussNorm v c g := by
  by_cases hf' : f = 0
  · simp [hf', gaussNorm_zero v c vZero]
  by_cases hg' : g = 0
  · simp [hg', gaussNorm_zero v c vZero]
  have hf1 : gaussNorm v c f ≠ 0 := by
    convert gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hf
    grind
  have hg1 : gaussNorm v c g ≠ 0 := by
    convert gaussNorm_eq_zero_iff v c g vZero vNonneg h_eq_zero hc hg
    grind
  apply ge_antisymm_iff.mpr
  constructor
  · exact gaussNorm_le_mul v c f g vMulEq vNA (by grind) hfg hdom
  · exact gaussNorm_mul_le v c f g (StrongLT.le hc) vNonneg (by grind) vNA vZero hf hg

end absoluteValue

end MvPowerSeries

