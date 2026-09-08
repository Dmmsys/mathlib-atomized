/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# The Logarithmic Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`.  Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The logarithmic counting function of a meromorphic function `f` is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole or zero-divisor of a meromorphic function.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the
  logarithmic counting function for arbitrary normed fields.

## TODO

- Discuss the logarithmic counting function for rational functions, add a forward reference to the
  upcoming converse, formulated in terms of the Nevanlinna height.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/--
Shorthand notation for the restriction of a function with locally finite support to the closed unit
ball of radius `r`.
-/
/-
**Function.locallyFinsuppWithin.toClosedBall** 是 Mathlib 中的一个定义，位于命名空间 `Function
.locallyFinsuppWithin`。
形式化陈述：toClosedBall (r : Real) : locallyFinsupp E Int ->+ locallyFinsuppWithin (c
losedBall (0 : E) |r|) Int
参数：r : Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Shorthand notation for the restriction of a function with locally finite support
 to the closed unit
ball of radius `r`.
-/
noncomputable def toClosedBall (r : ℝ) :
    locallyFinsupp E ℤ →+ locallyFinsuppWithin (closedBall (0 : E) |r|) ℤ := by
  apply restrictMonoidHom
  tauto

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Function.locallyFinsuppWithin.toClosedBall_eval_within** 是 Mathlib 中的一个引理，位于命名
空间 `Function.locallyFinsuppWithin`。
形式化陈述：toClosedBall_eval_within {r : Real} {z : E} (f : locallyFinsupp E Int) (ha
 : z in closedBall 0 |r|) : toClosedBall r f z = f z
参数：f : locallyFinsupp E Int；ha : z in closedBall 0 |r|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivial`：True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.restrictMonoidHom_apply`：restrictMonoidHom
_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subset
eq U) : restrictMonoidHom h D = D.restrict …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toClosedBall_eval_within {r : ℝ} {z : E} (f : locallyFinsupp E ℤ)
    (ha : z ∈ closedBall 0 |r|) :
    toClosedBall r f z = f z := by
  unfold toClosedBall
  simp_all [restrict_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Function.locallyFinsuppWithin.toClosedBall_divisor** 是 Mathlib 中的一个引理，位于命名空间 `
Function.locallyFinsuppWithin`。
形式化陈述：toClosedBall_divisor {r : Real} {f : Complex -> Complex} (h : Meromorphic 
f) : (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (div
isor f univ)
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trivial`：True
· 使用引理 `Function.locallyFinsuppWithin.restrictMonoidHom_apply`：restrictMonoidHom
_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subset
eq U) : restrictMonoidHom h D = D.restrict …
· 使用定理 `MeromorphicOn.divisor_restrict`：divisor_restrict {f : 𝕜 -> E} {V : Set 𝕜
} (hf : MeromorphicOn f U) (hV : V subseteq U) : (divisor f U).restrict hV = div
isor f V
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toClosedBall_divisor {r : ℝ} {f : ℂ → ℂ} (h : Meromorphic f) :
    (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ) := by
  simp_all [locallyFinsuppWithin.toClosedBall]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall** 是 Mathl
ib 中的一个引理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：toClosedBall_support_subset_closedBall {E : Type*} [NormedAddCommGroup E] 
{r : Real} (f : locallyFinsupp E Int) : (toClosedBall r f).support subseteq clos
edBall 0 |r|
参数：f : locallyFinsupp E Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `trivial`：True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.restrictMonoidHom_apply`：restrictMonoidHom
_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subset
eq U) : restrictMonoidHom h D = D.restrict …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma toClosedBall_support_subset_closedBall {E : Type*} [NormedAddCommGroup E] {r : ℝ}
    (f : locallyFinsupp E ℤ) :
    (toClosedBall r f).support ⊆ closedBall 0 |r| := by
  simp_all [toClosedBall, restrict_apply]

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function, as a group morphism mapping functions `D` with
locally finite support to maps `ℝ → ℝ`.  Given `D`, the result map `logCounting D` takes `r : ℝ` to
a logarithmically weighted measure of values that `D` takes within the disk `∣z∣ ≤ r`.

Implementation Note: In case where `z = 0`, the term `log (r * ‖z‖⁻¹)` evaluates to zero, which is
typically different from `log r - log ‖z‖ = log r`. The summand `(D 0) * log r` compensates this,
producing cleaner formulas when the logarithmic counting function is used in the main theorems of
Value Distribution Theory.  We refer the reader to page 164 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) for more details, and
to the lemma `countingFunction_finsum_eq_finsum_add` in
`Mathlib/Analysis/Complex/JensenFormula.lean` for a formal statement.
-/
/-
**Function.locallyFinsuppWithin.logCounting** 是 Mathlib 中的一个定义，位于命名空间 `Function.
locallyFinsuppWithin`。
形式化陈述：logCounting {E : Type*} [NormedAddCommGroup E] [ProperSpace E] : locallyFi
nsupp E Int ->+ (Real -> Real) where toFun D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of the logarithmic counting function, as a group morphism mapping fun
ctions `D` with
locally finite support to maps `ℝ → ℝ`.  Given `D`, the result map `logCounting 
D` takes `r : ℝ` to
a logarithmically weighted measure of values that `D` takes within the disk `∣z∣
 ≤ r`.

Implementation Note: In case where `z = 0`, the term `log (r * ‖z‖⁻¹)` evaluates
 to zero, which is
typically different from `log r - log ‖z‖ = log r`. The summand `(D 0) * log r` 
compensates this,
producing cleaner formulas when the logarithmic counting function is used in the
 main theorems of
Value Distribution Theory.  We refer the reader to page 164 of [Lang: Introducti
on to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) for
 more details, and
to the lemma `countingFunction_finsum_eq_finsum_add` in
`Mathlib/Analysis/Complex/JensenFormula.lean` for a formal statement.
-/
noncomputable def logCounting {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    locallyFinsupp E ℤ →+ (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
/-
**Function.locallyFinsuppWithin.logCounting_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Function.locallyFinsuppWithin`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : ProperSpace E] (D
 : Function.locallyFinsupp E ℤ),   Function.locallyFinsuppWithin.logCounting D 0
 = 0
参数：D : Function.locallyFinsupp E ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) :
    logCounting D 0 = 0 := by
  simp [logCounting]

set_option backward.isDefEq.respectTransparency.types false in
/--
The logarithmic counting function of a singleton indicator is asymptotically equal to
`log · - log ‖e‖`.
-/
/-
**Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const** 是 Mathlib 
中的一个定理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : DecidableEq E] [i
nst_2 : ProperSpace E] {e : E} {r : ℝ}   {n : ℤ},   ‖e‖ ≤ r →     Function.local
lyFinsuppWithin.logCounting (Function.locallyFinsuppWithin.single e n) r =      
 ↑n * (Real.log r - Real.log ‖e‖)
参数：Function.locallyFinsuppWithin.single e n；Real.log r - Real.log ‖e‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `trivial`：True
· 使用引理 `Function.locallyFinsuppWithin.restrictMonoidHom_apply`：restrictMonoidHom
_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subset
eq U) : restrictMonoidHom h D = D.restrict …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithmic counting function of a singleton indicator is asymptotically equ
al to
`log · - log ‖e‖`.
-/
@[simp] lemma logCounting_single_eq_log_sub_const [DecidableEq E] [ProperSpace E] {e : E} {r : ℝ}
    {n : ℤ} (hr : ‖e‖ ≤ r) :
    logCounting (single e n) r = n * (log r - log ‖e‖) := by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall, restrict_apply, single_apply])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_apply]
  · simp only [single_apply, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    grind

/-!
### Elementary Properties of Logarithmic Counting Functions
-/

set_option backward.isDefEq.respectTransparency.types false in
/--
The logarithmic counting function is even.
-/
/-
**Function.locallyFinsuppWithin.logCounting_even** 是 Mathlib 中的一个引理，位于命名空间 `Func
tion.locallyFinsuppWithin`。
形式化陈述：logCounting_even [ProperSpace E] (D : locallyFinsupp E Int) : (logCounting
 D).Even
参数：D : locallyFinsupp E Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `trivial`：True
· 使用引理 `Function.locallyFinsuppWithin.restrictMonoidHom_apply`：restrictMonoidHom
_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subset
eq U) : restrictMonoidHom h D = D.restrict …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `AddMonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Ad
dZero M] [inst_1 : AddZero N] (toZeroHom toZeroHom_1 : ZeroHom M N)   (e_toZeroH
om : toZeroHom =…
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic counting function is even.
-/
lemma logCounting_even [ProperSpace E] (D : locallyFinsupp E ℤ) :
    (logCounting D).Even := fun r ↦ by simp [logCounting, toClosedBall, restrict_apply]

/--
The logarithmic counting function is monotonous.
-/
/-
**Function.locallyFinsuppWithin.logCounting_mono** 是 Mathlib 中的一个引理，位于命名空间 `Func
tion.locallyFinsuppWithin`。
形式化陈述：logCounting_mono [ProperSpace E] {D : locallyFinsupp E Int} (hD : 0 <= D) 
: MonotoneOn (logCounting D) (Ioi 0)
参数：hD : 0 <= D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Set.mem_of_indicator_ne_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Ze
ro M] {s : Set α} {f : α → M} {a : α}, s.indicator f a ≠ 0 → a ∈ s
· 使用引理 `Function.locallyFinsuppWithin.toClosedBall_eval_within`：toClosedBall_eva
l_within {r : Real} {z : E} (f : locallyFinsupp E Int) (ha : z in closedBall 0 |
r|) : toClosedBall r f z = f z
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithmic counting function is monotonous.
-/
lemma logCounting_mono [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) :
    MonotoneOn (logCounting D) (Ioi 0) := by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    repeat rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z ∈ closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z ∈ closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

/--
The logarithmic counting function of a positive function with locally finite support is
asymptotically strictly monotone.
-/
/-
**Function.locallyFinsuppWithin.logCounting_strictMono** 是 Mathlib 中的一个引理，位于命名空间
 `Function.locallyFinsuppWithin`。
形式化陈述：logCounting_strictMono [DecidableEq E] [ProperSpace E] {D : locallyFinsupp
 E Int} {e : E} (hD : single e 1 <= D) : StrictMonoOn (logCounting D) (Ioi ‖e‖)
参数：hD : single e 1 <= D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `StrictMonoOn.add_monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α
] [inst_1 : Preorder α] [inst_2 : Preorder β] {f g : β → α} {s : Set β}   [AddLe
ftMono α] [AddR…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const`：∀ {E 
: Type u_1} [inst : NormedAddCommGroup E] [inst_1 : DecidableEq E] [inst_2 : Pro
perSpace E] {e : E} {r : ℝ}   {n : ℤ},   ‖e‖ ≤ r →     …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_lt_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dRightStrictMono α] {a b : α}, a < b → ∀ (c : α), a - c < b - c
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithmic counting function of a positive function with locally finite sup
port is
asymptotically strictly monotone.
-/
lemma logCounting_strictMono [DecidableEq E] [ProperSpace E] {D : locallyFinsupp E ℤ} {e : E}
    (hD : single e 1 ≤ D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  rw [(by aesop : logCounting D = logCounting (single e 1) + logCounting (D - single e 1))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le, logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
/-
**Function.locallyFinsuppWithin.logCounting_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction.locallyFinsuppWithin`。
形式化陈述：logCounting_nonneg {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {f :
 locallyFinsupp E Int} {r : Real} (h : 0 <= f) (hr : 1 <= r) : 0 <= logCounting 
f r
参数：h : 0 <= f；hr : 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
theorem logCounting_nonneg {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f : locallyFinsupp E ℤ} {r : ℝ} (h : 0 ≤ f) (hr : 1 ≤ r) :
    0 ≤ logCounting f r := by
  have h₃r : 0 < r := by linarith
  suffices ∀ z, 0 ≤ toClosedBall r f z * log (r * ‖z‖⁻¹) from
    add_nonneg (finsum_nonneg this) <| mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a ∈ closedBall 0 |r|
  · refine mul_nonneg ?_ <| log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

/--
For `1 ≤ r`, the logarithmic counting function respects the `≤` relation.
-/
/-
**Function.locallyFinsuppWithin.logCounting_le** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.locallyFinsuppWithin`。
形式化陈述：logCounting_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {f₁ f₂ :
 locallyFinsupp E Int} {r : Real} (h : f₁ <= f₂) (hr : 1 <= r) : logCounting f₁ 
r <= logCounting f₂ r
参数：h : f₁ <= f₂；hr : 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Function.locallyFinsuppWithin.logCounting_nonneg`：logCounting_nonneg {E 
: Type*} [NormedAddCommGroup E] [ProperSpace E] {f : locallyFinsupp E Int} {r : 
Real} (h : 0 <= f) (hr : 1 <= r) : 0 <…
· 使用定理 `Function.locallyFinsuppWithin.instIsOrderedAddMonoid`：∀ {X : Type u_1} [
inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommGroup Y] 
  [inst_2 : LinearOrder Y] [IsOrderedAddMo…

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function respects the `≤` relation.
-/
theorem logCounting_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 1 ≤ r) :
    logCounting f₁ r ≤ logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

/--
The logarithmic counting function respects the `≤` relation asymptotically.
-/
/-
**Function.locallyFinsuppWithin.logCounting_eventuallyLE** 是 Mathlib 中的一个定理，位于命名
空间 `Function.locallyFinsuppWithin`。
形式化陈述：logCounting_eventuallyLE {E : Type*} [NormedAddCommGroup E] [ProperSpace E
] {f₁ f₂ : locallyFinsupp E Int} (h : f₁ <= f₂) : logCounting f₁ <=ᶠ[atTop] logC
ounting f₂
参数：h : f₁ <= f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.locallyFinsuppWithin.logCounting_le`：logCounting_le {E : Type*}
 [NormedAddCommGroup E] [ProperSpace E] {f₁ f₂ : locallyFinsupp E Int} {r : Real
} (h : f₁ <= f₂) (hr : 1 <= r) : l…

--- 原说明 ---
The logarithmic counting function respects the `≤` relation asymptotically.
-/
theorem logCounting_eventuallyLE {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E ℤ} (h : f₁ ≤ f₂) :
    logCounting f₁ ≤ᶠ[atTop] logCounting f₂ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_le h hr

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The logarithmic counting function of a meromorphic function.

If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is any value, this is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.  In the special case where `a = ⊤`, it counts the poles of `f`.
-/
/-
**ValueDistribution.logCounting** 是 Mathlib 中的一个定义，位于命名空间 `ValueDistribution`。
形式化陈述：logCounting : Real -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic counting function of a meromorphic function.

If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is any value, this is a logari
thmically weighted
measure of the number of times the function `f` takes a given value `a` within t
he disk `∣z∣ ≤ r`,
taking multiplicities into account.  In the special case where `a = ⊤`, it count
s the poles of `f`.
-/
noncomputable def logCounting : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (f · - a.untop₀) univ)⁺.logCounting

/--
Relation between `ValueDistribution.logCounting` and `locallyFinsuppWithin.logCounting`.
-/
/-
**ValueDistribution._root_.locallyFinsuppWithin.logCounting_divisor** 是 Mathlib 
中的一个引理，位于命名空间 `ValueDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between `ValueDistribution.logCounting` and `locallyFinsuppWithin.logCo
unting`.
-/
lemma _root_.locallyFinsuppWithin.logCounting_divisor {f : ℂ → ℂ} :
    locallyFinsuppWithin.logCounting (divisor f univ) = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the logarithmic
counting function for the zeros of `f - a₀`.
-/
/-
**ValueDistribution.logCounting_coe** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution
`。
形式化陈述：logCounting_coe : logCounting f a₀ = (divisor (f · - a₀) univ)⁺.logCountin
g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is 
the logarithmic
counting function for the zeros of `f - a₀`.
-/
lemma logCounting_coe :
    logCounting f a₀ = (divisor (f · - a₀) univ)⁺.logCounting := by
  simp [logCounting]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equals the logarithmic
counting function for the zeros of `f - a₀`.
-/
/-
**ValueDistribution.logCounting_coe_eq_logCounting_sub_const_zero** 是 Mathlib 中的
一个引理，位于命名空间 `ValueDistribution`。
形式化陈述：logCounting_coe_eq_logCounting_sub_const_zero : logCounting f a₀ = logCoun
ting (f - fun _ => a₀) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equ
als the logarithmic
counting function for the zeros of `f - a₀`.
-/
lemma logCounting_coe_eq_logCounting_sub_const_zero :
    logCounting f a₀ = logCounting (f - fun _ ↦ a₀) 0 := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f 0` is the logarithmic counting function associated
with the zero-divisor of `f`.
-/
/-
**ValueDistribution.logCounting_zero** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistributio
n`。
形式化陈述：logCounting_zero : logCounting f 0 = (divisor f univ)⁺.logCounting
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic counting function `logCounting f 0` is the logarithmic counting 
function associated
with the zero-divisor of `f`.
-/
lemma logCounting_zero :
    logCounting f 0 = (divisor f univ)⁺.logCounting := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f ⊤` is the logarithmic counting function associated
with the pole-divisor of `f`.
-/
/-
**ValueDistribution.logCounting_top** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution
`。
形式化陈述：logCounting_top : logCounting f ⊤ = (divisor f univ)⁻.logCounting
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic counting function `logCounting f ⊤` is the logarithmic counting 
function associated
with the pole-divisor of `f`.
-/
lemma logCounting_top :
    logCounting f ⊤ = (divisor f univ)⁻.logCounting := by
  simp [logCounting]

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
/-
**ValueDistribution.logCounting_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistri
bution`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {E : Type u_2}   [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {
f : 𝕜 → E} {a : WithTop E},   ValueDistribution.logCounting f a 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.locallyFinsuppWithin.logCounting_eval_zero`：∀ {E : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : ProperSpace E] (D : Function.locallyFinsup
p E ℤ),   Function.locallyFinsuppWithin.l…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero :
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [logCounting, h]

/--
The logarithmic counting function associated with the divisor of `f` is the difference between
`logCounting f 0` and `logCounting f ⊤`.
-/
/-
**ValueDistribution.log_counting_zero_sub_logCounting_top** 是 Mathlib 中的一个定理，位于命
名空间 `ValueDistribution`。
形式化陈述：log_counting_zero_sub_logCounting_top {f : 𝕜 -> E} : (divisor f univ).logC
ounting = logCounting f 0 - logCounting f ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `posPart_sub_negPart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGr
oup α] [AddLeftMono α] (a : α), a⁺ - a⁻ = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Function.locallyFinsuppWithin.instIsOrderedAddMonoid`：∀ {X : Type u_1} [
inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommGroup Y] 
  [inst_2 : LinearOrder Y] [IsOrderedAddMo…
· 使用引理 `ValueDistribution.logCounting_zero`：logCounting_zero : logCounting f 0 =
 (divisor f univ)⁺.logCounting
· 使用引理 `ValueDistribution.logCounting_top`：logCounting_top : logCounting f ⊤ = (
divisor f univ)⁻.logCounting
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
The logarithmic counting function associated with the divisor of `f` is the diff
erence between
`logCounting f 0` and `logCounting f ⊤`.
-/
theorem log_counting_zero_sub_logCounting_top {f : 𝕜 → E} :
    (divisor f univ).logCounting = logCounting f 0 - logCounting f ⊤ := by
  rw [← posPart_sub_negPart (divisor f univ), logCounting_zero, logCounting_top, map_sub]

/--
The logarithmic counting function of a constant function is zero.
-/
/-
**ValueDistribution.logCounting_const** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistributi
on`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {E : Type u_2}   [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {
c : E} {e : WithTop E},   ValueDistribution.logCounting (fun x => c) e = 0
参数：fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeromorphicOn.divisor_const`：divisor_const (e : E) : divisor (fun _ => e
) U = 0
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Function.locallyFinsuppWithin.instIsOrderedAddMonoid`：∀ {X : Type u_1} [
inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommGroup Y] 
  [inst_2 : LinearOrder Y] [IsOrderedAddMo…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic counting function of a constant function is zero.
-/
@[simp] theorem logCounting_const {c : E} {e : WithTop E} :
    logCounting (fun _ ↦ c : 𝕜 → E) e = 0 := by
  simp [logCounting]

/--
The logarithmic counting function of the constant function zero is zero.
-/
/-
**ValueDistribution.logCounting_const_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistr
ibution`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {E : Type u_2}   [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {
e : WithTop E}, ValueDistribution.logCounting 0 e = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValueDistribution.logCounting_const`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {E : Type u_2}   [inst_2 : NormedAddCo
mmGroup E] [inst_3 : Norm…

--- 原说明 ---
The logarithmic counting function of the constant function zero is zero.
-/
@[simp] theorem logCounting_const_zero {e : WithTop E} :
    logCounting (0 : 𝕜 → E) e = 0 := logCounting_const

/--
The logarithmic counting function is even.
-/
/-
**ValueDistribution.logCounting_even** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistributio
n`。
形式化陈述：logCounting_even {f : 𝕜 -> E} {e : WithTop E} : (logCounting f e).Even
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.locallyFinsuppWithin.logCounting_even`：logCounting_even [Proper
Space E] (D : locallyFinsupp E Int) : (logCounting D).Even
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
The logarithmic counting function is even.
-/
theorem logCounting_even {f : 𝕜 → E} {e : WithTop E} :
    (logCounting f e).Even := by
  intro r
  by_cases h : e = ⊤ <;> simp [logCounting, h, locallyFinsuppWithin.logCounting_even _ r]

/--
The logarithmic counting function is monotonous.
-/
/-
**ValueDistribution.logCounting_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistr
ibution`。
形式化陈述：logCounting_monotoneOn {f : 𝕜 -> E} {e : WithTop E} : MonotoneOn (logCount
ing f e) (Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.locallyFinsuppWithin.logCounting_mono`：logCounting_mono [Proper
Space E] {D : locallyFinsupp E Int} (hD : 0 <= D) : MonotoneOn (logCounting D) (
Ioi 0)
· 使用定理 `negPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁻
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `posPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁺

--- 原说明 ---
The logarithmic counting function is monotonous.
-/
theorem logCounting_monotoneOn {f : 𝕜 → E} {e : WithTop E} :
    MonotoneOn (logCounting f e) (Ioi 0) := by
  by_cases h : e = ⊤ <;>
    simpa [logCounting, h] using locallyFinsuppWithin.logCounting_mono (by positivity)

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
/-
**ValueDistribution.logCounting_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribut
ion`。
形式化陈述：logCounting_nonneg {r : Real} {f : 𝕜 -> E} {e : WithTop E} (hr : 1 <= r) :
 0 <= logCounting f e r
参数：hr : 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.locallyFinsuppWithin.logCounting_nonneg`：logCounting_nonneg {E 
: Type*} [NormedAddCommGroup E] [ProperSpace E] {f : locallyFinsupp E Int} {r : 
Real} (h : 0 <= f) (hr : 1 <= r) : 0 <…
· 使用定理 `negPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁻
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `posPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁺

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
theorem logCounting_nonneg {r : ℝ} {f : 𝕜 → E} {e : WithTop E} (hr : 1 ≤ r) :
    0 ≤ logCounting f e r := by
  by_cases h : e = ⊤
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (negPart_nonneg (divisor f univ)) hr]
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (posPart_nonneg (divisor (f · - e.untop₀) univ)) hr]

/--
The logarithmic counting function is asymptotically non-negative.
-/
/-
**ValueDistribution.logCounting_eventually_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Val
ueDistribution`。
形式化陈述：logCounting_eventually_nonneg {f : 𝕜 -> E} {e : WithTop E} : 0 <=ᶠ[atTop] 
logCounting f e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ValueDistribution.logCounting_nonneg`：logCounting_nonneg {r : Real} {f :
 𝕜 -> E} {e : WithTop E} (hr : 1 <= r) : 0 <= logCounting f e r

--- 原说明 ---
The logarithmic counting function is asymptotically non-negative.
-/
theorem logCounting_eventually_nonneg {f : 𝕜 → E} {e : WithTop E} :
    0 ≤ᶠ[atTop] logCounting f e := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ by simp [logCounting_nonneg hr]

/-!
## Elementary Properties of the Logarithmic Counting Function
-/

/--
If two functions differ only on a discrete set, then their logarithmic counting
functions agree.
-/
/-
**ValueDistribution.logCounting_congr_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 `Valu
eDistribution`。
形式化陈述：logCounting_congr_codiscrete [NormedSpace Complex E] {f g : Complex -> E} 
(hfg : f =ᶠ[codiscrete Complex] g) : logCounting f = logCounting g
参数：hfg : f =ᶠ[codiscrete Complex] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MeromorphicOn.divisor_congr_codiscreteWithin`：divisor_congr_codiscreteWi
thin {f₁ f₂ : 𝕜 -> E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : IsOpen U) : divi
sor f₁ U = divisor f₂ U
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If two functions differ only on a discrete set, then their logarithmic counting
functions agree.
-/
theorem logCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E} (hfg : f =ᶠ[codiscrete ℂ] g) :
    logCounting f = logCounting g := by
  ext a : 1
  by_cases h : a = ⊤
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    exact divisor_congr_codiscreteWithin hfg isOpen_univ
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    apply divisor_congr_codiscreteWithin _ isOpen_univ
    filter_upwards [hfg] using by simp

/--
Relation between the logarithmic counting functions of `f` and of `f⁻¹`.
-/
/-
**ValueDistribution.logCounting_inv** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {f : 𝕜 → 𝕜},   ValueDistribution.logCounting f⁻¹ ⊤ = ValueDistribution.logCou
nting f 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValueDistribution.logCounting_top`：logCounting_top : logCounting f ⊤ = (
divisor f univ)⁻.logCounting
· 使用定理 `MeromorphicOn.divisor_inv`：divisor_inv {f : 𝕜 -> 𝕜} : divisor f⁻¹ U = -d
ivisor f U
· 使用定理 `negPart_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), (-a)⁻ = a⁺
· 使用引理 `ValueDistribution.logCounting_zero`：logCounting_zero : logCounting f 0 =
 (divisor f univ)⁺.logCounting
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Relation between the logarithmic counting functions of `f` and of `f⁻¹`.
-/
@[simp] theorem logCounting_inv {f : 𝕜 → 𝕜} :
     logCounting f⁻¹ ⊤ = logCounting f 0 := by
  simp [logCounting_zero, logCounting_top]

/--
Adding an analytic function does not change the logarithmic counting function for the poles.
-/
/-
**ValueDistribution.logCounting_add_analyticOn** 是 Mathlib 中的一个定理，位于命名空间 `ValueD
istribution`。
形式化陈述：logCounting_add_analyticOn (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ)
 : logCounting (f + g) ⊤ = logCounting f ⊤
参数：hf : Meromorphic f；hg : AnalyticOn 𝕜 g univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right`：negPart_diviso
r_add_of_analyticNhdOn_right {f₁ f₂ : 𝕜 -> E} (hf₁ : MeromorphicOn f₁ U) (hf₂ : 
AnalyticOnNhd 𝕜 f₂ U) : (divisor (f₁ + f₂) U)⁻…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsOpen.analyticOn_iff_analyticOnNhd`：IsOpen.analyticOn_iff_analyticOnNhd
 {f : E -> F} {s : Set E} (hs : IsOpen s) : AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f
 s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
Adding an analytic function does not change the logarithmic counting function fo
r the poles.
-/
theorem logCounting_add_analyticOn (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.meromorphicOn.negPart_divisor_add_of_analyticNhdOn_right
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
Special case of `logCounting_add_analyticOn`: Adding a constant does not change the logarithmic
counting function for the poles.
-/
/-
**ValueDistribution.logCounting_add_const** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistri
bution`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {E : Type u_2}   [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {
f : 𝕜 → E} {a₀ : E},   Meromorphic f → ValueDistribution.logCounting (f + fun x 
=> a₀) ⊤ = ValueDistribution.logCounting f ⊤
参数：f + fun x => a₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValueDistribution.logCounting_add_analyticOn`：logCounting_add_analyticOn
 (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ) : logCounting (f + g) ⊤ = logCo
unting f ⊤
· 使用定理 `analyticOn_const`：analyticOn_const {v : F} {s : Set E} : AnalyticOn 𝕜 (f
un _ => v) s

--- 原说明 ---
Special case of `logCounting_add_analyticOn`: Adding a constant does not change 
the logarithmic
counting function for the poles.
-/
@[simp] theorem logCounting_add_const (hf : Meromorphic f) :
    logCounting (f + fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn hf analyticOn_const

/--
Special case of `logCounting_add_analyticOn`: Subtracting a constant does not change the logarithmic
counting function for the poles.
-/
/-
**ValueDistribution.logCounting_sub_const** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistri
bution`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {E : Type u_2}   [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {
f : 𝕜 → E} {a₀ : E},   Meromorphic f → ValueDistribution.logCounting (f - fun x 
=> a₀) ⊤ = ValueDistribution.logCounting f ⊤
参数：f - fun x => a₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ValueDistribution.logCounting_add_const`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {E : Type u_2}   [inst_2 : NormedA
ddCommGroup E] [inst_3 : Norm…

--- 原说明 ---
Special case of `logCounting_add_analyticOn`: Subtracting a constant does not ch
ange the logarithmic
counting function for the poles.
-/
@[simp] theorem logCounting_sub_const (hf : Meromorphic f) :
    logCounting (f - fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  simpa [sub_eq_add_neg] using! logCounting_add_const hf

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f + g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
/-
**ValueDistribution.logCounting_add_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistr
ibution`。
形式化陈述：logCounting_add_top_le {f₁ f₂ : 𝕜 -> E} {r : Real} (h₁f₁ : Meromorphic f₁)
 (h₁f₂ : Meromorphic f₂) (hr : 1 <= r) : logCounting (f₁ + f₂) ⊤ r <= (logCounti
ng f₁ ⊤ + logCounting f₂ ⊤) r
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂；hr : 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `Function.locallyFinsuppWithin.logCounting_le`：logCounting_le {E : Type*}
 [NormedAddCommGroup E] [ProperSpace E] {f₁ f₂ : locallyFinsupp E Int} {r : Real
} (h : f₁ <= f₂) (hr : 1 <= r) : l…
· 使用定理 `MeromorphicOn.negPart_divisor_add_le_add`：negPart_divisor_add_le_add {f₁
 f₂ : 𝕜 -> E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) 
: (divisor (f₁ + f₂) U)⁻ <= (d…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function for the poles of `f + g` is less 
than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respecti
vely.
-/
theorem logCounting_add_top_le {f₁ f₂ : 𝕜 → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    logCounting (f₁ + f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (negPart_divisor_add_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

/--
Asymptotically, the logarithmic counting function for the poles of `f + g` is less than or equal to
the sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
/-
**ValueDistribution.logCounting_add_top_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 `
ValueDistribution`。
形式化陈述：logCounting_add_top_eventuallyLE {f₁ f₂ : 𝕜 -> E} (h₁f₁ : Meromorphic f₁) 
(h₁f₂ : Meromorphic f₂) : logCounting (f₁ + f₂) ⊤ <=ᶠ[atTop] logCounting f₁ ⊤ + 
logCounting f₂ ⊤
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.logCounting_add_top_le`：logCounting_add_top_le {f₁ f₂ 
: 𝕜 -> E} {r : Real} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) (hr : 1 <= 
r) : logCounting (f₁ + f₂) ⊤ r…

--- 原说明 ---
Asymptotically, the logarithmic counting function for the poles of `f + g` is le
ss than or equal to
the sum of the logarithmic counting functions for the poles of `f` and `g`, resp
ectively.
-/
theorem logCounting_add_top_eventuallyLE {f₁ f₂ : 𝕜 → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    logCounting (f₁ + f₂) ⊤ ≤ᶠ[atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than or
equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
-/
/-
**ValueDistribution.logCounting_sum_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistr
ibution`。
形式化陈述：logCounting_sum_top_le {α : Type*} (s : Finset α) (f : α -> 𝕜 -> E) {r : R
eal} (h₁f : forall a in s, Meromorphic (f a)) (hr : 1 <= r) : logCounting (∑ a i
n s, f a) ⊤ r <= (∑ a in s, (logCounting (f a) ⊤)) r
参数：s : Finset α；f : α -> 𝕜 -> E；h₁f : forall a in s, Meromorphic (f a)；hr : 1 <=
 r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ValueDistribution.logCounting_const_zero`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {E : Type u_2}   [inst_2 : Normed
AddCommGroup E] [inst_3 : Norm…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `ValueDistribution.logCounting_add_top_le`：logCounting_add_top_le {f₁ f₂ 
: 𝕜 -> E} {r : Real} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) (hr : 1 <= 
r) : logCounting (f₁ + f₂) ⊤ r…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Meromorphic.sum`：sum (h : forall σ in s, Meromorphic (G σ)) : Meromorphi
c (∑ n in s, G n)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function for the poles of a sum `∑ a ∈ s, 
f a` is less than or
equal to the sum of the logarithmic counting functions for the poles of the `f ·
`.
-/
theorem logCounting_sum_top_le {α : Type*} (s : Finset α) (f : α → 𝕜 → E) {r : ℝ}
    (h₁f : ∀ a ∈ s, Meromorphic (f a)) (hr : 1 ≤ r) :
    logCounting (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc logCounting (f a + ∑ x ∈ s, f x) ⊤ r
      _ ≤ (logCounting (f a) ⊤ + logCounting (∑ x ∈ s, f x) ⊤) r :=
        logCounting_add_top_le (h₁f a (Finset.mem_insert_self a s))
          (Meromorphic.sum (fun σ hσ ↦ h₁f σ (Finset.mem_insert_of_mem hσ))) hr
      _ ≤ (logCounting (f a) ⊤ + ∑ x ∈ s, logCounting (f x) ⊤) r :=
        add_le_add (by trivial) (hs (fun a ha ↦ h₁f a (Finset.mem_insert_of_mem ha)))

/--
Asymptotically, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than
or equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
-/
/-
**ValueDistribution.logCounting_sum_top_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 `
ValueDistribution`。
形式化陈述：logCounting_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α -> 𝕜 ->
 E) (h₁f : forall a in s, Meromorphic (f a)) : logCounting (∑ a in s, f a) ⊤ <=ᶠ
[atTop] ∑ a in s, (logCounting (f a) ⊤)
参数：s : Finset α；f : α -> 𝕜 -> E；h₁f : forall a in s, Meromorphic (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.logCounting_sum_top_le`：logCounting_sum_top_le {α : Ty
pe*} (s : Finset α) (f : α -> 𝕜 -> E) {r : Real} (h₁f : forall a in s, Meromorph
ic (f a)) (hr : 1 <= r) : logC…

--- 原说明 ---
Asymptotically, the logarithmic counting function for the poles of a sum `∑ a ∈ 
s, f a` is less than
or equal to the sum of the logarithmic counting functions for the poles of the `
f ·`.
-/
theorem logCounting_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    (h₁f : ∀ a ∈ s, Meromorphic (f a)) :
    logCounting (∑ a ∈ s, f a) ⊤ ≤ᶠ[atTop] ∑ a ∈ s, (logCounting (f a) ⊤) := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_sum_top_le s f h₁f hr

/--
For `1 ≤ r`, the logarithmic counting function for the zeros of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.

Note: The statement proven here is found at the top of page 169 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) where it is written as
an inequality between functions. This could be interpreted as claiming that the inequality holds for
ALL values of `r`, which is not true. For a counterexample, take `f₁ : z → z` and `f₂ : z → z⁻¹`.
Then,

- `logCounting f₁ 0 = log`
- `logCounting f₂ 0 = 0`
- `logCounting (f₁ * f₂) 0 = 0`

But `log r` is negative for small `r`.
-/
/-
**ValueDistribution.logCounting_mul_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDist
ribution`。
形式化陈述：logCounting_mul_zero_le {f₁ f₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r) (h₁f₁ : 
Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h₁f₂ : Meromorp
hic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) : logCounting (f₁ * f₂) 
0 r <= (logCounting f₁ 0 + logCounting f₂ 0) r
参数：hr : 1 <= r；h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z !=
 ⊤；h₁f₂ : Meromorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeromorphicOn.divisor_mul`：divisor_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : Meromorp
hicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderA
t f₁ z != ⊤) (h…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `Function.locallyFinsuppWithin.logCounting_le`：logCounting_le {E : Type*}
 [NormedAddCommGroup E] [ProperSpace E] {f₁ f₂ : locallyFinsupp E Int} {r : Real
} (h : f₁ <= f₂) (hr : 1 <= r) : l…
· 使用定理 `Function.locallyFinsuppWithin.posPart_add`：posPart_add (f₁ f₂ : Function
.locallyFinsuppWithin U Y) : (f₁ + f₂)⁺ <= f₁⁺ + f₂⁺

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function for the zeros of `f * g` is less 
than or equal to the
sum of the logarithmic counting functions for the zeros of `f` and `g`, respecti
vely.

Note: The statement proven here is found at the top of page 169 of [Lang: Introd
uction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) whe
re it is written as
an inequality between functions. This could be interpreted as claiming that the 
inequality holds for
ALL values of `r`, which is not true. For a counterexample, take `f₁ : z → z` an
d `f₂ : z → z⁻¹`.
Then,

- `logCounting f₁ 0 = log`
- `logCounting f₂ 0 = 0`
- `logCounting (f₁ * f₂) 0 = 0`

But `log r` is negative for small `r`.
-/
theorem logCounting_mul_zero_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 r ≤ (logCounting f₁ 0 + logCounting f₂ 0) r := by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ ↦ h₂f₁ z) (fun z _ ↦ h₂f₂ z),
    ← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.posPart_add

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
-/
/-
**ValueDistribution.logCounting_mul_zero_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 
`ValueDistribution`。
形式化陈述：logCounting_mul_zero_eventuallyLE {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : Meromorphic f₁)
 (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h₁f₂ : Meromorphic f₂) (h₂f₂ :
 forall z, meromorphicOrderAt f₂ z != ⊤) : logCounting (f₁ * f₂) 0 <=ᶠ[atTop] lo
gCounting f₁ 0 + logCounting f₂ 0
参数：h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤；h₁f₂ : Me
romorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.logCounting_mul_zero_le`：logCounting_mul_zero_le {f₁ f
₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r) (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, m
eromorphicOrderAt f₁ z != ⊤) (h…

--- 原说明 ---
Asymptotically, the logarithmic counting function for the zeros of `f * g` is le
ss than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, resp
ectively.
-/
theorem logCounting_mul_zero_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 ≤ᶠ[atTop] logCounting f₁ 0 + logCounting f₂ 0 := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr ↦ logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
/-
**ValueDistribution.logCounting_mul_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistr
ibution`。
形式化陈述：logCounting_mul_top_le {f₁ f₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r) (h₁f₁ : M
eromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h₁f₂ : Meromorph
ic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) : logCounting (f₁ * f₂) ⊤
 r <= (logCounting f₁ ⊤ + logCounting f₂ ⊤) r
参数：hr : 1 <= r；h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z !=
 ⊤；h₁f₂ : Meromorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeromorphicOn.divisor_mul`：divisor_mul {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : Meromorp
hicOn f₁ U) (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : forall z in U, meromorphicOrderA
t f₁ z != ⊤) (h…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `Function.locallyFinsuppWithin.logCounting_le`：logCounting_le {E : Type*}
 [NormedAddCommGroup E] [ProperSpace E] {f₁ f₂ : locallyFinsupp E Int} {r : Real
} (h : f₁ <= f₂) (hr : 1 <= r) : l…
· 使用定理 `Function.locallyFinsuppWithin.negPart_add`：negPart_add (f₁ f₂ : Function
.locallyFinsuppWithin U Y) : (f₁ + f₂)⁻ <= f₁⁻ + f₂⁻

--- 原说明 ---
For `1 ≤ r`, the logarithmic counting function for the poles of `f * g` is less 
than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respecti
vely.
-/
theorem logCounting_mul_top_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ ↦ h₂f₁ z) (fun z _ ↦ h₂f₂ z),
    ← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.negPart_add

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
-/
/-
**ValueDistribution.logCounting_mul_top_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 `
ValueDistribution`。
形式化陈述：logCounting_mul_top_eventuallyLE {f₁ f₂ : 𝕜 -> 𝕜} (h₁f₁ : Meromorphic f₁) 
(h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h₁f₂ : Meromorphic f₂) (h₂f₂ : 
forall z, meromorphicOrderAt f₂ z != ⊤) : logCounting (f₁ * f₂) ⊤ <=ᶠ[atTop] log
Counting f₁ ⊤ + logCounting f₂ ⊤
参数：h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤；h₁f₂ : Me
romorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.logCounting_mul_top_le`：logCounting_mul_top_le {f₁ f₂ 
: 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r) (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, mer
omorphicOrderAt f₁ z != ⊤) (h₁…

--- 原说明 ---
Asymptotically, the logarithmic counting function for the zeros of `f * g` is le
ss than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, resp
ectively.
-/
theorem logCounting_mul_top_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ ≤ᶠ[atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr ↦ logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For natural numbers `n`, the logarithmic counting function for the zeros of `f ^ n` equals `n`
times the logarithmic counting function for the zeros of `f`.
-/
/-
**ValueDistribution.logCounting_pow_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistrib
ution`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {f : 𝕜 → 𝕜} {n : ℕ},   Meromorphic f → ValueDistribution.logCounting (f ^ n) 
0 = n • ValueDistribution.logCounting f 0
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeromorphicOn.divisor_fun_pow`：divisor_fun_pow {f : 𝕜 -> 𝕜} (hf : Meromo
rphicOn f U) (n : Nat) : divisor (fun z => f z ^ n) U = n • divisor f U
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Function.locallyFinsuppWithin.nsmul_posPart`：nsmul_posPart (n : Nat) (f 
: locallyFinsuppWithin U Y) : (n • f)⁺ = n • f⁺
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For natural numbers `n`, the logarithmic counting function for the zeros of `f ^
 n` equals `n`
times the logarithmic counting function for the zeros of `f`.
-/
@[simp] theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : Meromorphic f) :
    logCounting (f ^ n) 0 = n • logCounting f 0 := by
  simp [logCounting, divisor_fun_pow hf.meromorphicOn n]

/--
For natural numbers `n`, the logarithmic counting function for the poles of `f ^ n` equals `n` times
the logarithmic counting function for the poles of `f`.
-/
/-
**ValueDistribution.logCounting_pow_top** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribu
tion`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : ProperSpace 
𝕜] {f : 𝕜 → 𝕜} {n : ℕ},   Meromorphic f → ValueDistribution.logCounting (f ^ n) 
⊤ = n • ValueDistribution.logCounting f ⊤
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeromorphicOn.divisor_pow`：divisor_pow {f : 𝕜 -> 𝕜} (hf : MeromorphicOn 
f U) (n : Nat) : divisor (f ^ n) U = n • divisor f U
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Function.locallyFinsuppWithin.nsmul_negPart`：nsmul_negPart (n : Nat) (f 
: locallyFinsuppWithin U Y) : (n • f)⁻ = n • f⁻
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a

--- 原说明 ---
For natural numbers `n`, the logarithmic counting function for the poles of `f ^
 n` equals `n` times
the logarithmic counting function for the poles of `f`.
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : Meromorphic f) :
    logCounting (f ^ n) ⊤ = n • logCounting f ⊤ := by
  simp [logCounting, divisor_pow hf.meromorphicOn n]

end ValueDistribution

/-!
## Representation by Integrals

For `𝕜 = ℂ`, the theorems below describe the logarithmic counting function in terms of circle
averages.
-/

/--
Over the complex numbers, present the logarithmic counting function attached to the divisor of a
meromorphic function `f` as a circle average over `log ‖f ·‖`.

This is a reformulation of Jensen's formula of complex analysis. See
`MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original context.
-/
/-
**Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const**
 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_con
st {R : Real} {f : Complex -> Complex} (h : Meromorphic f) (hR : R != 0) : logCo
unting (divisor f univ) R = circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrai
lingCoeffAt f 0‖
参数：h : Meromorphic f；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeromorphicOn.circleAverage_log_norm`：MeromorphicOn.circleAverage_log_no
rm {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0) (h₁f : Meromo
rphicOn f (closedBall c |R…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Function.locallyFinsuppWithin.toClosedBall_divisor`：toClosedBall_divisor
 {r : Real} {f : Complex -> Complex} (h : Meromorphic f) : (divisor f (closedBal
l 0 |r|)) = (locallyFinsuppWithin.toClos…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeromorphicOn.divisor_apply`：divisor_apply {f : 𝕜 -> E} (hf : Meromorphi
cOn f U) (hz : z in U) : divisor f U z = (meromorphicOrderAt f z).untop₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Over the complex numbers, present the logarithmic counting function attached to 
the divisor of a
meromorphic function `f` as a circle average over `log ‖f ·‖`.

This is a reformulation of Jensen's formula of complex analysis. See
`MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original cont
ext.
-/
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f) (hR : R ≠ 0) :
    logCounting (divisor f univ) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, logCounting, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

/--
Variant of `locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`, using
`ValueDistribution.logCounting` instead of `locallyFinsuppWithin.logCounting`.
-/
/-
**ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_co
nst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_su
b_const {R : Real} {f : Complex -> Complex} (h : Meromorphic f) (hR : R != 0) : 
(logCounting f 0 - logCounting f ⊤) R = circleAverage (log ‖f ·‖) 0 R - log ‖mer
omorphicTrailingCoeffAt f 0‖
参数：h : Meromorphic f；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `locallyFinsuppWithin.logCounting_divisor`：∀ {f : ℂ → ℂ},   Function.loca
llyFinsuppWithin.logCounting (MeromorphicOn.divisor f Set.univ) =     ValueDistr
ibution.logCounting f 0 - Valu…
· 使用定理 `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_c
onst`：Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_con
st {R : Real} {f : Complex -> Complex} (h : Meromorphic f) (hR : R…

--- 原说明 ---
Variant of `locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`
, using
`ValueDistribution.logCounting` instead of `locallyFinsuppWithin.logCounting`.
-/
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f) (hR : R ≠ 0) :
    (logCounting f 0 - logCounting f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR
