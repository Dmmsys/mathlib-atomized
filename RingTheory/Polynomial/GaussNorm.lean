/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss norm for polynomials

This file defines the Gauss norm for polynomials. Given a polynomial `p` in `R[X]`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (p.coeff i) * c ^ i` for all `i` in the support of `p`.

This is mostly useful when `v` is an absolute value on `R` and `c` is set to be `1`, in which case
the Gauss norm corresponds to the maximum of the absolute values of the coefficients of `p`. When
`R` is a subring of `ℂ` and `v` is the standard absolute value, this is sometimes called the
"height" of `p`.

In the file `Mathlib/RingTheory/PowerSeries/GaussNorm.lean`, the Gauss norm is defined for power
series. This is a generalization of the Gauss norm defined in this file in case `v` is a
nonnegative function with `v 0 = 0` and `c ≥ 0`.

## Main Definitions and Results
* `Polynomial.gaussNorm` is the supremum of the set of all values of `v (p.coeff i) * c ^ i`
  for all `i` in the support of `p`, where `p` is a polynomial in `R[X]`, `v : R → ℝ` is a function
  and `c` is a real number.
* `Polynomial.gaussNorm_coe_powerSeries`: if `v` is a nonnegative function with `v 0 = 0` and `c`
  is nonnegative, the Gauss norm of a polynomial is equal to its Gauss norm as a power series.
* `Polynomial.exists_min_eq_gaussNorm`: if `v` is a nonnegative function with `v 0 = 0` and `c`
  is nonnegative, there exists a minimal index `i` such that the Gauss norm of `p` at `c` is
  attained at `i`.
* `Polynomial.isNonarchimedean_gaussNorm`: if `v` is a nonnegative nonarchimedean function with
  `v 0 = 0` and `c` is nonnegative, the Gauss norm is nonarchimedean.
* `Polynomial.gaussNorm_mul`: if `v` is a nonarchimedean absolute value, then the Gauss norm is
  multiplicative.
* `Polynomial.gaussNorm_isAbsoluteValue`: if `v` is a nonarchimedean absolute value, then the
  Gauss norm is an absolute value.
-/

@[expose] public section
variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

variable (p : R[X])

/-- Given a polynomial `p` in `R[X]`, a function `v : R → ℝ` and a real number `c`, the Gauss norm
is defined as the supremum of the set of all values of `v (p.coeff i) * c ^ i` for all `i` in the
support of `p`. -/
/-
**Polynomial.gaussNorm** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm : Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1

--- 原说明 ---
Given a polynomial `p` in `R[X]`, a function `v : R → ℝ` and a real number `c`, 
the Gauss norm
is defined as the supremum of the set of all values of `v (p.coeff i) * c ^ i` f
or all `i` in the
support of `p`.
-/
def gaussNorm : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
/-
**Polynomial.gaussNorm_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_zero : gaussNorm v c 0 = 0
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
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussNorm_zero : gaussNorm v c 0 = 0 := by simp [gaussNorm]

variable [ZeroHomClass F R ℝ]
/-
**Polynomial.exists_eq_gaussNorm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_eq_gaussNorm : exists i, p.gaussNorm v c = v (p.coeff i) * c ^ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem exists_eq_gaussNorm : ∃ i, p.gaussNorm v c = v (p.coeff i) * c ^ i := by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNorm, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i ↦ (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

@[simp]
/-
**Polynomial.gaussNorm_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_C (r : R) : (C r).gaussNorm v c = v r
参数：r : R。
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
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.support_C`：support_C {a : R} (h : a != 0) : (C a).support = s
ingleton 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma gaussNorm_C (r : R) : (C r).gaussNorm v c = v r := by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_C, hr]

@[simp]
/-
**Polynomial.gaussNorm_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_monomial (n : Nat) (r : R) : (monomial n r).gaussNorm v c = v r 
* c ^ n
参数：n : Nat；r : R。
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
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
-/
theorem gaussNorm_monomial (n : ℕ) (r : R) :
    (monomial n r).gaussNorm v c = v r * c ^ n := by
  by_cases hr : r = 0 <;> simp [gaussNorm, support_monomial, hr]

variable {c}

omit [ZeroHomClass F R ℝ] in
/-
**Polynomial.sup'_nonneg_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sup'_nonneg_of_ne_zero [NonnegHomClass F R ℝ] {p : R[X]} (h : p.support.Nonempty)
    (hc : 0 ≤ c) : 0 ≤ p.support.sup' h fun i ↦ (v (p.coeff i) * c ^ i) := by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity
/-
**Polynomial.aux_bdd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_bdd : BddAbove {x | ∃ i, v (p.coeff i) * c ^ i = x} := by
  let f : p.support → ℝ := fun i ↦ v (p.coeff i) * c ^ i.val
  have h_fin : (f '' ⊤ ∪ {0}).Finite := by
    apply Set.Finite.union _ <| Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ, Set.finite_univ_iff, ← @Finset.coe_sort_coe]
    exact Finite.of_fintype p.support
  refine Set.Finite.bddAbove <| Set.Finite.subset h_fin fun _ ↦ ?_
  simp only [Set.top_eq_univ, Set.image_univ, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_range, Subtype.exists, mem_support_iff]
  grind

variable [NonnegHomClass F R ℝ]

/-- If `v` is a nonnegative function with `v 0 = 0` and `c` is nonnegative, the Gauss norm of a
polynomial is equal to its Gauss norm as a power series. -/
@[simp]
/-
**Polynomial.gaussNorm_coe_powerSeries** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_coe_powerSeries (hc : 0 <= c) : (p.toPowerSeries).gaussNorm v c 
= p.gaussNorm v c
参数：hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.gaussNorm_zero`：gaussNorm_zero (vZero : v 0 = 0) : gaussNo
rm v c 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `PowerSeries.gaussNorm_eq`：gaussNorm_eq : gaussNorm v c f = ⨆ i : Nat, v 
(f.coeff i) * c ^ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.GaussNorm.0.Polynomial.sup'_nonne
g_of_ne_zero`：∀ {R : Type u_1} {F : Type u_2} [inst : Semiring R] [inst_1 : FunL
ike F R ℝ] (v : F) {c : ℝ} [NonnegHomClass F R ℝ]   {p : Polynomial R} (h …
· 使用定理 `Polynomial.exists_eq_gaussNorm`：exists_eq_gaussNorm : exists i, p.gaussN
orm v c = v (p.coeff i) * c ^ i
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.GaussNorm.0.Polynomial.aux_bdd`：∀
 {R : Type u_1} {F : Type u_2} [inst : Semiring R] [inst_1 : FunLike F R ℝ] (v :
 F) {c : ℝ} (p : Polynomial R)   [ZeroHomClass F R ℝ], BddA…

--- 原说明 ---
If `v` is a nonnegative function with `v 0 = 0` and `c` is nonnegative, the Gaus
s norm of a
polynomial is equal to its Gauss norm as a power series.
-/
theorem gaussNorm_coe_powerSeries (hc : 0 ≤ c) :
    (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c := by
  by_cases hp : p = 0
  · simp [hp]
  · simp only [PowerSeries.gaussNorm_eq, coeff_coe, gaussNorm, support_nonempty, ne_eq, hp,
      not_false_eq_true, ↓reduceDIte]
    apply le_antisymm
    · apply ciSup_le
      intro n
      by_cases h : n ∈ p.support
      · exact Finset.le_sup' (fun j ↦ v (p.coeff j) * c ^ j) h
      · simp_all [sup'_nonneg_of_ne_zero v (support_nonempty.mpr hp) hc]
    · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
      simp only [gaussNorm, support_nonempty.mpr hp, ↓reduceDIte] at hi
      rw [hi]
      exact le_ciSup (aux_bdd v p) i

/-- If `v x = 0 → x = 0` for all `x : R` and `v` is nonnegative, then the Gauss norm is zero if and
only if the polynomial is zero. -/
@[simp]
/-
**Polynomial.gaussNorm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_eq_zero_iff (h_eq_zero : forall x : R, v x = 0 -> x = 0) (hc : 0
 < c) : p.gaussNorm v c = 0 ↔ p = 0
参数：h_eq_zero : forall x : R, v x = 0 -> x = 0；hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.gaussNorm_coe_powerSeries`：gaussNorm_coe_powerSeries (hc : 0 
<= c) : (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Polynomial.coe_eq_zero_iff`：coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ 
φ = 0
· 使用引理 `PowerSeries.gaussNorm_eq_zero_iff`：gaussNorm_eq_zero_iff (vZero : v 0 = 
0) (vNonneg : forall a, v a >= 0) (h_eq_zero : forall x : R, v x = 0 -> x = 0) (
hc : 0 < c) (hbd : HasG…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.GaussNorm.0.Polynomial.aux_bdd`：∀
 {R : Type u_1} {F : Type u_2} [inst : Semiring R] [inst_1 : FunLike F R ℝ] (v :
 F) {c : ℝ} (p : Polynomial R)   [ZeroHomClass F R ℝ], BddA…

--- 原说明 ---
If `v x = 0 → x = 0` for all `x : R` and `v` is nonnegative, then the Gauss norm
 is zero if and
only if the polynomial is zero.
-/
theorem gaussNorm_eq_zero_iff (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) :
    p.gaussNorm v c = 0 ↔ p = 0 := by
  rw [← gaussNorm_coe_powerSeries _ _ (le_of_lt hc)]
  convert PowerSeries.gaussNorm_eq_zero_iff v c p (by grind) (by simp) h_eq_zero hc
    (by simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p)
  exact Iff.symm coe_eq_zero_iff

omit [ZeroHomClass F R ℝ] in
/-- If `v` is a nonnegative function, then the Gauss norm is nonnegative. -/
/-
**Polynomial.gaussNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_nonneg (hc : 0 <= c) : 0 <= p.gaussNorm v c
参数：hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯

--- 原说明 ---
If `v` is a nonnegative function, then the Gauss norm is nonnegative.
-/
theorem gaussNorm_nonneg (hc : 0 ≤ c) : 0 ≤ p.gaussNorm v c := by
  by_cases hp : p.support.Nonempty <;>
  simp_all [gaussNorm, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]
/-
**Polynomial.le_gaussNorm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：le_gaussNorm (hc : 0 <= c) (i : Nat) : v (p.coeff i) * c ^ i <= p.gaussNor
m v c
参数：hc : 0 <= c；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.gaussNorm_coe_powerSeries`：gaussNorm_coe_powerSeries (hc : 0 
<= c) : (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用引理 `PowerSeries.le_gaussNorm`：le_gaussNorm (hbd : HasGaussNorm v c f) (t : N
at) : v (coeff t f) * c ^ t <= gaussNorm v c f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.GaussNorm.0.Polynomial.aux_bdd`：∀
 {R : Type u_1} {F : Type u_2} [inst : Semiring R] [inst_1 : FunLike F R ℝ] (v :
 F) {c : ℝ} (p : Polynomial R)   [ZeroHomClass F R ℝ], BddA…
-/
lemma le_gaussNorm (hc : 0 ≤ c) (i : ℕ) : v (p.coeff i) * c ^ i ≤ p.gaussNorm v c := by
  rw [← gaussNorm_coe_powerSeries _ _ hc, ← coeff_coe]
  apply PowerSeries.le_gaussNorm
  simpa [PowerSeries.HasGaussNorm] using! aux_bdd v p

@[simp]
/-
**Polynomial.gaussNorm_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_zero_right : p.gaussNorm v 0 = v (p.coeff 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Finset.sup'.congr_simp`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatt
iceSup α] (s s_1 : Finset β) (e_s : s = s_1) (H : s.Nonempty)   (f f_1 : β → α),
 f = f_1 → s…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Finset.sup'_const`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) (a : α),   (s.sup' H fun x => a) = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma gaussNorm_zero_right : p.gaussNorm v 0 = v (p.coeff 0) := by
  have : (fun i ↦ v (p.coeff i) * 0 ^ i) = fun i ↦ if i = 0 then v (p.coeff 0) else 0 := by
    aesop
  rcases eq_or_ne (p.coeff 0) 0 with _ | hcoeff0
  · simp_all [gaussNorm]
  · apply le_antisymm
    · aesop (add norm (by simp [gaussNorm, Finset.sup'_le_iff]))
    · grind [p.le_gaussNorm v (le_refl 0) 0]

set_option backward.isDefEq.respectTransparency false in
/-- If `v` is a nonnegative function with `v 0 = 0` and `c` is nonnegative, there exists a minimal
index `i` such that the Gauss norm of `p` at `c` is attained at `i`. -/
/-
**Polynomial.exists_min_eq_gaussNorm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：exists_min_eq_gaussNorm (p : R[X]) (hc : 0 <= c) : exists i, p.gaussNorm v
 c = v (p.coeff i) * c ^ i ∧ forall j, j < i -> v (p.coeff j) * c ^ j < p.gaussN
orm v c
参数：p : R[X]；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_eq_gaussNorm`：exists_eq_gaussNorm : exists i, p.gaussN
orm v c = v (p.coeff i) * c ^ i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `Polynomial.le_gaussNorm`：le_gaussNorm (hc : 0 <= c) (i : Nat) : v (p.coe
ff i) * c ^ i <= p.gaussNorm v c
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `v` is a nonnegative function with `v 0 = 0` and `c` is nonnegative, there ex
ists a minimal
index `i` such that the Gauss norm of `p` at `c` is attained at `i`.
-/
lemma exists_min_eq_gaussNorm (p : R[X]) (hc : 0 ≤ c) :
    ∃ i, p.gaussNorm v c = v (p.coeff i) * c ^ i ∧
    ∀ j, j < i → v (p.coeff j) * c ^ j < p.gaussNorm v c := by
  have h_nonempty : {i | gaussNorm v c p = v (p.coeff i) * c ^ i}.Nonempty := by
    obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
    exact ⟨i, Set.mem_ofPred.mpr hi⟩
  refine ⟨Nat.find h_nonempty, Nat.find_spec h_nonempty, ?_⟩
  intro j hj_lt
  simp only [Nat.lt_find_iff, Set.mem_ofPred_eq] at hj_lt
  exact lt_of_le_of_ne (le_gaussNorm v _ hc j) fun a ↦ hj_lt j (Nat.le_refl j) a.symm

/-- If `v` is a nonnegative nonarchimedean function with `v 0 = 0` and `c` is nonnegative, the
Gauss norm is nonarchimedean. -/
/-
**Polynomial.isNonarchimedean_gaussNorm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isNonarchimedean_gaussNorm (hna : IsNonarchimedean v) {c : Real} (hc : 0 <
= c) : IsNonarchimedean (gaussNorm v c)
参数：hna : IsNonarchimedean v；hc : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `max_mul_of_nonneg`：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <=
 c) : max a b * c = max (a * c) (b * c)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用引理 `Polynomial.le_gaussNorm`：le_gaussNorm (hc : 0 <= c) (i : Nat) : v (p.coe
ff i) * c ^ i <= p.gaussNorm v c

--- 原说明 ---
If `v` is a nonnegative nonarchimedean function with `v 0 = 0` and `c` is nonneg
ative, the
Gauss norm is nonarchimedean.
-/
theorem isNonarchimedean_gaussNorm (hna : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) :
    IsNonarchimedean (gaussNorm v c) := by
  intro p q
  rcases eq_or_ne p 0 with hp | _
  · simp [hp]
  rcases eq_or_ne q 0 with hq | _
  · simp [hq]
  rcases eq_or_ne (p + q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg]
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte,
    Finset.sup'_le_iff]
  intro i _
  calc
  v ((p + q).coeff i) * c ^ i
    ≤ max (v (p.coeff i)) (v (q.coeff i)) * c ^ i := by
    rw [coeff_add]
    gcongr
    exact hna (p.coeff i) (q.coeff i)
  _ = max (v (p.coeff i) * c ^ i) (v (q.coeff i) * c ^ i) := by
    rw [max_mul_of_nonneg _ _ (pow_nonneg hc _)]
  _ ≤ max (gaussNorm v c p) (gaussNorm v c q) := by
    apply max_le_max <;>
    exact le_gaussNorm v _ hc i

open Finset in
/-- If `v` is a nonnegative nonarchimedean multiplicative function with `v 0 = 0` and `c` is
nonnegative, then the Gauss norm is submultiplicative. -/
/-
**Polynomial.gaussNorm_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_mul_le [MulHomClass F R Real] (hna : IsNonarchimedean v) (p q : 
R[X]) (hc : 0 <= c) : (p * q).gaussNorm v c <= p.gaussNorm v c * q.gaussNorm v c
参数：hna : IsNonarchimedean v；p q : R[X]；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.support_nonempty`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.support.Nonempty ↔ p ≠ 0
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsNonarchimedean.finset_image_add_of_nonempty`：finset_image_add_of_nonem
pty {α β : Type*} [AddCommMonoid α] {f : α -> R} (hna : IsNonarchimedean f) (g :
 β -> α) {t : Finset β} (ht : t.Non…
· 使用定理 `Finset.nonempty_range_add_one`：nonempty_range_add_one : (range <| n + 1)
.Nonempty
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `v` is a nonnegative nonarchimedean multiplicative function with `v 0 = 0` an
d `c` is
nonnegative, then the Gauss norm is submultiplicative.
-/
theorem gaussNorm_mul_le [MulHomClass F R ℝ] (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 ≤ c) :
    (p * q).gaussNorm v c ≤ p.gaussNorm v c * q.gaussNorm v c := by
  rcases eq_or_ne (p * q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg, mul_nonneg]
  have h_supp_p : p.support.Nonempty := support_nonempty.mpr <| left_ne_zero_of_mul hpq
  have h_supp_q : q.support.Nonempty := support_nonempty.mpr <| right_ne_zero_of_mul hpq
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, h_supp_p,
    h_supp_q, sup'_le_iff, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  intro i _
  obtain ⟨j, _, _⟩ := IsNonarchimedean.finset_image_add_of_nonempty hna _ nonempty_range_add_one
  calc
  v (∑ j ∈ range (i + 1), p.coeff j * q.coeff (i - j)) * c ^ i
  _ ≤ v (p.coeff j * q.coeff (i - j)) * c ^ i := by gcongr
  _ = (v (p.coeff j) * c ^ j) * (v (q.coeff (i - j)) * c ^ (i - j)) := by
      have : c ^ j * c ^ (i - j) = c ^ i := by simp_all [← pow_add]
      grind
  _ ≤ (p.support.sup' _ fun i ↦ v (p.coeff i) * c ^ i)
    * q.support.sup' _ fun i ↦ v (q.coeff i) * c ^ i := by
      have hp_le := p.le_gaussNorm v hc j
      have hq_le := q.le_gaussNorm v hc (i - j)
      have := p.gaussNorm_nonneg v hc
      simp_all only [gaussNorm, ↓reduceDIte]
      gcongr

section AbsoluteValue

variable {R : Type*} [Ring R] {v : AbsoluteValue R ℝ} (hna : IsNonarchimedean v) (hc : 0 < c)

open Finset in
include hna hc in
/-
**Polynomial.mul_gaussNorm_le_gaussNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_gaussNorm_le_gaussNorm_mul (p q : R[X]) :
    p.gaussNorm v c * q.gaussNorm v c ≤ (p * q).gaussNorm v c := by
  have hc0 : 0 ≤ c := le_of_lt hc
  obtain ⟨i, hi_p, hlt_p⟩ := p.exists_min_eq_gaussNorm v hc0
  obtain ⟨j, hj_q, hlt_q⟩ := q.exists_min_eq_gaussNorm v hc0
  -- i and j are the minimal indices where the gauss norms are attained
  wlog hvpq : v (p.coeff i) ≠ 0 ∧ v (q.coeff j) ≠ 0
  · grind [mul_mul_mul_comm, gaussNorm_nonneg]
  have := hvpq.1
  have := hvpq.2
  apply le_of_eq_of_le _ <| (p * q).le_gaussNorm v hc0 (i + j)
  -- gaussNorm v c p * gaussNorm v c q is actually equal to v ((p * q).coeff (i + j)) * c ^ (i + j)
  rw [hi_p, hj_q, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    IsNonarchimedean.apply_sum_eq_of_lt hna (k := i) (by simp) (by simp)]
  /- IsNonarchimedean.apply_sum_eq_of_lt makes the goal almost trivial so we are left to prove
  the hmax hypothesis -/
  · grind
  intro x hx hneq
  apply lt_of_mul_lt_mul_right _ <| pow_nonneg hc0 (i + j)
  have : x + (i + j - x) = i + j := by simp_all
  convert_to! v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) <
    v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j)
  · grind
  · grind
  -- we need to distinguish two cases depending on whether x < i or x > i
  rcases lt_or_gt_of_ne hneq
  · calc
    v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
    _ ≤ v (p.coeff x) * c ^ x * gaussNorm v c q := by
        gcongr
        exact q.le_gaussNorm v hc0 (i + j - x)
    _ = v (p.coeff x) * c ^ x * (v (q.coeff j) * c ^ j) := by
        rw [hj_q]
    _ < v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j) := by
        gcongr 1
        grind
  · calc
    v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
    _ ≤ gaussNorm v c p * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
        gcongr
        exact p.le_gaussNorm v hc0 x
    _ = v (p.coeff i) * c ^ i * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
        rw [hi_p]
    _ < v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j) := by
        gcongr 1
        grind

include hna hc in
/-- If `v` is a nonarchimedean absolute value, then the Gauss norm is multiplicative. -/
/-
**Polynomial.gaussNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_mul (p q : R[X]) : (p * q).gaussNorm v c = p.gaussNorm v c * q.g
aussNorm v c
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.gaussNorm_mul_le`：gaussNorm_mul_le [MulHomClass F R Real] (hn
a : IsNonarchimedean v) (p q : R[X]) (hc : 0 <= c) : (p * q).gaussNorm v c <= p.
gaussNorm v c * q…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.GaussNorm.0.Polynomial.mul_gaussN
orm_le_gaussNorm_mul`：∀ {c : ℝ} {R : Type u_3} [inst : Ring R] {v : AbsoluteValu
e R ℝ},   IsNonarchimedean ⇑v →     0 < c →       ∀ (p q : Polynomial R), Polyno
mi…

--- 原说明 ---
If `v` is a nonarchimedean absolute value, then the Gauss norm is multiplicative
.
-/
theorem gaussNorm_mul (p q : R[X]) :
    (p * q).gaussNorm v c = p.gaussNorm v c * q.gaussNorm v c :=
  le_antisymm (gaussNorm_mul_le v hna p q (le_of_lt hc))
  <| mul_gaussNorm_le_gaussNorm_mul hna hc p q

include hna hc in
/-- If `v` is a nonarchimedean absolute value, then the Gauss norm is an absolute value. -/
/-
**Polynomial.gaussNorm_isAbsoluteValue** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gaussNorm_isAbsoluteValue : IsAbsoluteValue (gaussNorm v c) where abv_nonn
eg' p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.gaussNorm_nonneg`：gaussNorm_nonneg (hc : 0 <= c) : 0 <= p.gau
ssNorm v c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.gaussNorm_eq_zero_iff`：gaussNorm_eq_zero_iff (h_eq_zero : for
all x : R, v x = 0 -> x = 0) (hc : 0 < c) : p.gaussNorm v c = 0 ↔ p = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AbsoluteValue.eq_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, abv…
· 使用定理 `Polynomial.gaussNorm_mul`：gaussNorm_mul (p q : R[X]) : (p * q).gaussNorm
 v c = p.gaussNorm v c * q.gaussNorm v c

--- 原说明 ---
If `v` is a nonarchimedean absolute value, then the Gauss norm is an absolute va
lue.
-/
theorem gaussNorm_isAbsoluteValue :
    IsAbsoluteValue (gaussNorm v c) where
  abv_nonneg' p := p.gaussNorm_nonneg v <| le_of_lt hc
  abv_eq_zero' := gaussNorm_eq_zero_iff v _ (fun _ hx ↦ (AbsoluteValue.eq_zero v).mp hx) hc
  abv_add' p q := by
    grind [isNonarchimedean_gaussNorm v hna (le_of_lt hc) p q, gaussNorm_nonneg]
  abv_mul' p q := gaussNorm_mul hna hc p q

end AbsoluteValue

end Polynomial

namespace PowerSeries

variable {c} (r : R)

@[simp]
/-
**PowerSeries.gaussNorm_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_C [ZeroHomClass F R Real] [NonnegHomClass F R Real] (hc : 0 <= c
) : (C r).gaussNorm v c = v r
参数：hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.gaussNorm_coe_powerSeries`：gaussNorm_coe_powerSeries (hc : 0 
<= c) : (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c
· 使用引理 `Polynomial.gaussNorm_C`：gaussNorm_C (r : R) : (C r).gaussNorm v c = v r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gaussNorm_C [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (hc : 0 ≤ c) :
    (C r).gaussNorm v c = v r := by
  simp [← Polynomial.coe_C, hc]

@[simp]
/-
**PowerSeries.gaussNorm_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：gaussNorm_monomial [ZeroHomClass F R Real] [NonnegHomClass F R Real] (hc :
 0 <= c) (n : Nat) : (monomial n r).gaussNorm v c = v r * c ^ n
参数：hc : 0 <= c；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.gaussNorm_coe_powerSeries`：gaussNorm_coe_powerSeries (hc : 0 
<= c) : (p.toPowerSeries).gaussNorm v c = p.gaussNorm v c
· 使用定理 `Polynomial.gaussNorm_monomial`：gaussNorm_monomial (n : Nat) (r : R) : (m
onomial n r).gaussNorm v c = v r * c ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gaussNorm_monomial [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (hc : 0 ≤ c) (n : ℕ) :
    (monomial n r).gaussNorm v c = v r * c ^ n := by
  simp [← Polynomial.coe_monomial, hc]

end PowerSeries

