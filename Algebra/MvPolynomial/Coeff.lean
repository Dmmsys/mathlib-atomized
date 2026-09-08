/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Formulas for coefficients of multivariate polynomials

## Main Results

* `MvPolynomial.coeff_add_pow`: the formula for the `d`th coefficient of `(X 0 + X 1) ^ n`.

-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

variable {R σ : Type*} [CommSemiring R] {s : σ →₀ ℕ}

/-
**MvPolynomial.coeff_linearCombination_X_pow_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `Mv
Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coeff_linearCombination_X_pow_of_eq (a : σ →₀ R) {n : ℕ}
    (hs : s.sum (fun _ m ↦ m) = n) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      s.multinomial * s.prod (fun r m ↦ a r ^ m) := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s : σ → ℕ)]
  · simp_rw [eq_indicator_self_iff]
    split_ifs with hs'
    · rw [prod_of_support_subset _ hs' _ (by simp), Finsupp.multinomial_of_support_subset hs']
    · rw [Finset.subset_iff] at hs'
      simp only [Finsupp.mem_support_iff, ne_eq, not_forall, Decidable.not_not] at hs'
      obtain ⟨i, hsi, hai⟩ := hs'
      rw [← mul_prod_erase _ i _ (by simpa), hai, zero_pow hsi, zero_mul, mul_zero]
  · simp only [Finset.mem_piAntidiag, ne_eq, Finsupp.mem_support_iff, ite_eq_right_iff, and_imp]
    intro _ _ _ _ hed
    simp [Finsupp.ext_iff] at hed
    grind
  · simp_rw [ite_eq_right_iff]
    intro hs' hs''
    rw [eq_indicator_self_iff] at hs''
    exfalso
    rw [Finset.mem_piAntidiag, not_and_or] at hs'
    rcases hs' with hs' | hs'
    · apply hs'
      rw [← hs, sum_of_support_subset _ hs'' _ (by simp)]
    · grind
/-
**MvPolynomial.coeff_linearCombination_X_pow_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Mv
Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coeff_linearCombination_X_pow_of_ne (a : σ →₀ R) {n : ℕ}
    (hs : s.sum (fun _ m ↦ m) ≠ n) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) = 0 := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum, ← map_pow,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_prod,
    coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero (fun x hx ↦ ?_)
  rw [if_neg]
  rintro ⟨rfl⟩
  apply hs
  simp only [Finset.mem_piAntidiag] at hx
  rw [sum_of_support_subset _ (support_indicator_subset a.support _) _ (by simp), ← hx.1]
  congr
  ext i
  by_cases hi : i ∈ a.support
  · simp [Finsupp.indicator_of_mem hi]
  · grind [Finsupp.indicator_of_notMem hi]
/-
**MvPolynomial.coeff_linearCombination_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `MvPolyno
mial`。
形式化陈述：coeff_linearCombination_X_pow (a : σ ->₀ R) (s : σ ->₀ Nat) (n : Nat) : co
eff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) = if s.sum (fun _ m =
> m) = n then s.multinomial * s.prod (fun r m => a r ^ m) else 0
参数：a : σ ->₀ R；s : σ ->₀ Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `_private.Mathlib.Algebra.MvPolynomial.Coeff.0.MvPolynomial.coeff_linearC
ombination_X_pow_of_eq`：∀ {R : Type u_1} {σ : Type u_2} [inst : CommSemiring R] 
{s : σ →₀ ℕ} (a : σ →₀ R) {n : ℕ},   (s.sum fun x m => m) = n →     MvPolynomial
.coe…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `_private.Mathlib.Algebra.MvPolynomial.Coeff.0.MvPolynomial.coeff_linearC
ombination_X_pow_of_ne`：∀ {R : Type u_1} {σ : Type u_2} [inst : CommSemiring R] 
{s : σ →₀ ℕ} (a : σ →₀ R) {n : ℕ},   (s.sum fun x m => m) ≠ n → MvPolynomial.coe
ff s…
-/
lemma coeff_linearCombination_X_pow (a : σ →₀ R) (s : σ →₀ ℕ) (n : ℕ) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      if s.sum (fun _ m ↦ m) = n then s.multinomial * s.prod (fun r m ↦ a r ^ m) else 0 := by
  split_ifs with hs
  · exact coeff_linearCombination_X_pow_of_eq a hs
  · exact coeff_linearCombination_X_pow_of_ne a hs
/-
**MvPolynomial.coeff_linearCombination_X_pow_of_fintype** 是 Mathlib 中的一个引理，位于命名空
间 `MvPolynomial`。
形式化陈述：coeff_linearCombination_X_pow_of_fintype [Fintype σ] (a : σ -> R) (s : σ -
>₀ Nat) (n : Nat) : coeff s (((∑ i, a i • X i : MvPolynomial σ R)) ^ n) = if s.s
um (fun _ m => m) = n then s.multinomial * s.prod (fun r m => a r ^ m) else 0
参数：a : σ -> R；s : σ ->₀ Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.ofSupportFinite_coe`：ofSupportFinite_coe {f : α -> M} {hf : (Fun
ction.support f).Finite} : (ofSupportFinite f hf : α -> M) = f
· 使用定理 `Finsupp.prod_congr`：prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : 
forall x in f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2
· 使用引理 `MvPolynomial.coeff_linearCombination_X_pow`：coeff_linearCombination_X_po
w (a : σ ->₀ R) (s : σ ->₀ Nat) (n : Nat) : coeff s (((a.linearCombination R X :
 MvPolynomial σ R)) ^ n) = if s.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coeff_linearCombination_X_pow_of_fintype [Fintype σ] (a : σ → R) (s : σ →₀ ℕ) (n : ℕ) :
    coeff s (((∑ i, a i • X i : MvPolynomial σ R)) ^ n) =
      if s.sum (fun _ m ↦ m) = n then s.multinomial * s.prod (fun r m ↦ a r ^ m) else 0 := by
  rw [← ofSupportFinite_coe (f := a) (hf := Set.toFinite _),
    prod_congr (fun r _ ↦ rfl), ← coeff_linearCombination_X_pow]
  simp [linearCombination_apply, sum_of_support_subset (s := Finset.univ)]
/-
**MvPolynomial.coeff_sum_X_pow_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomia
l`。
形式化陈述：coeff_sum_X_pow_of_fintype [Fintype σ] (d : σ ->₀ Nat) (n : Nat) : coeff d
 (((∑ i, X i : MvPolynomial σ R)) ^ n) = if d.sum (fun _ m => m) = n then d.mult
inomial else 0
参数：d : σ ->₀ Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.coeff_linearCombination_X_pow_of_fintype`：coeff_linearCombi
nation_X_pow_of_fintype [Fintype σ] (a : σ -> R) (s : σ ->₀ Nat) (n : Nat) : coe
ff s (((∑ i, a i • X i : MvPolynomial σ R))…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `Finsupp.prod_fun_one`：prod_fun_one (f : α ->₀ M) : f.prod (fun _ _ => (1
 : N)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma coeff_sum_X_pow_of_fintype [Fintype σ] (d : σ →₀ ℕ) (n : ℕ) :
    coeff d (((∑ i, X i : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m ↦ m) = n then d.multinomial else 0 := by
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, (1 : σ → R) i • X i := by simp
  simp [this, coeff_linearCombination_X_pow_of_fintype]

/-- The formula for the `d`th coefficient of `(X 0 + X 1) ^ n`. -/
/-
**MvPolynomial.coeff_add_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_add_pow (d : Fin 2 ->₀ Nat) (n : Nat) : coeff d ((X 0 + X 1 : MvPoly
nomial (Fin 2) R) ^ n) = if (d 0, d 1) in Finset.antidiagonal n then n.choose (d
 0) else 0
参数：d : Fin 2 ->₀ Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用引理 `MvPolynomial.coeff_sum_X_pow_of_fintype`：coeff_sum_X_pow_of_fintype [Fin
type σ] (d : σ ->₀ Nat) (n : Nat) : coeff d (((∑ i, X i : MvPolynomial σ R)) ^ n
) = if d.sum (fun _ m => m) =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finsupp.multinomial_eq_of_support_subset`：multinomial_eq_of_support_subs
et {f : α ->₀ Nat} {s : Finset α} (h : f.support subseteq s) : f.multinomial = N
at.multinomial s f
· 使用定理 `Finset.univ_fin2`：Finset.univ_fin2 : (univ : Finset (Fin 2)) = {0, 1}
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.binomial_eq_choose`：binomial_eq_choose [DecidableEq α] (h : a != b) 
: multinomial {a, b} f = (f a + f b).choose (f a)
· 使用定理 `Fin.zero_ne_one`：∀ {n : ℕ}, 0 ≠ 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
The formula for the `d`th coefficient of `(X 0 + X 1) ^ n`.
-/
theorem coeff_add_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    coeff d ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) =
      if (d 0, d 1) ∈ Finset.antidiagonal n then n.choose (d 0) else 0 := by
  rw [← Fin.sum_univ_two, coeff_sum_X_pow_of_fintype]
  congr 1
  have : d.sum (fun x m ↦ m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  simp only [Finset.mem_antidiagonal, this]
  split_ifs with hd
  · rw [multinomial_eq_of_support_subset (Finset.subset_univ d.support), Finset.univ_fin2,
      Nat.binomial_eq_choose Fin.zero_ne_one, hd]
  · rfl

/-- A monomial in two variables equals `C a * X 0 ^ d 0 * X 1 ^ d 1`. -/
/-
**MvPolynomial.monomial_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_fin_two (d : Fin 2 ->₀ Nat) (a : R) : monomial d a = C a * X 0 ^ 
d 0 * X 1 ^ d 1
参数：d : Fin 2 ->₀ Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finsupp.prod_fintype`：prod_fintype [Fintype α] (f : α ->₀ M) (g : α -> M
 -> N) (h : forall i, g i 0 = 1) : f.prod g = ∏ i, g i (f i)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1

--- 原说明 ---
A monomial in two variables equals `C a * X 0 ^ d 0 * X 1 ^ d 1`.
-/
theorem monomial_fin_two (d : Fin 2 →₀ ℕ) (a : R) :
    monomial d a = C a * X 0 ^ d 0 * X 1 ^ d 1 := by
  rw [monomial_eq, mul_assoc, d.prod_fintype _ fun _ ↦ pow_zero _, Fin.prod_univ_two]

end MvPolynomial

