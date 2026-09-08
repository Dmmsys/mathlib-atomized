/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.FinCases

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

@[expose] public section

namespace PMF

open ENNReal NNReal
/-- The binomial `PMF`: the probability of observing exactly `i` “heads” in a sequence of `n`
independent coin tosses, each having probability `p` of coming up “heads”. -/
@[deprecated ProbabilityTheory.binomial (since := "2026-04-07")]
/-
**PMF.binomial** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：binomial (p : Real>=0) (h : p <= 1) (n : Nat) : PMF (Fin (n + 1))
参数：p : Real>=0；h : p <= 1；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binomial `PMF`: the probability of observing exactly `i` “heads” in a sequen
ce of `n`
independent coin tosses, each having probability `p` of coming up “heads”.
-/
def binomial (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i =>
      ↑(p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ))) (by
    norm_cast
    convert! (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    · rw [add_tsub_cancel_of_le (mod_cast h), one_pow])

@[deprecated ProbabilityTheory.binomial_real_singleton (since := "2026-04-07")]
/-
**PMF.binomial_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：binomial_apply (p : Real>=0) (h : p <= 1) (n : Nat) (i : Fin (n + 1)) : bi
nomial p h n i = p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - i) : Nat) * (n.choose 
i : Nat)
参数：p : Real>=0；h : p <= 1；n : Nat；i : Fin (n + 1)。
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
· 使用定理 `ENNReal.coe_sub`：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
· 使用定理 `PMF.ofFintype.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] (f f_1 : α
 → ENNReal) (e_f : f = f_1) (h : ∑ a, f a = 1),   PMF.ofFintype f h = PMF.ofFint
ype f_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomial_apply (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    binomial p h n i = p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ) := by
  simp [binomial]

@[deprecated ProbabilityTheory.binomial_real_zero (since := "2026-04-07")]
/-
**PMF.binomial_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：binomial_apply_zero (p : Real>=0) (h : p <= 1) (n : Nat) : binomial p h n 
0 = (1 - p) ^ n
参数：p : Real>=0；h : p <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.binomial_apply`：binomial_apply (p : Real>=0) (h : p <= 1) (n : Nat) 
(i : Fin (n + 1)) : binomial p h n i = p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - 
i) : Nat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomial_apply_zero (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n 0 = (1 - p) ^ n := by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]
/-
**PMF.binomial_apply_last** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：binomial_apply_last (p : Real>=0) (h : p <= 1) (n : Nat) : binomial p h n 
(.last n) = p ^ n
参数：p : Real>=0；h : p <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.binomial_apply`：binomial_apply (p : Real>=0) (h : p <= 1) (n : Nat) 
(i : Fin (n + 1)) : binomial p h n i = p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - 
i) : Nat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomial_apply_last (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p ^ n := by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]
/-
**PMF.binomial_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：binomial_apply_self (p : Real>=0) (h : p <= 1) (n : Nat) : binomial p h n 
(.last n) = p ^ n
参数：p : Real>=0；h : p <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.binomial_apply_last`：binomial_apply_last (p : Real>=0) (h : p <= 1) 
(n : Nat) : binomial p h n (.last n) = p ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomial_apply_self (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) :
    binomial p h n (.last n) = p ^ n := by simp [binomial_apply_last]

/-- The binomial distribution on one coin is the Bernoulli distribution. -/
@[deprecated ProbabilityTheory.binomial_one_eq_bernoulliMeasure (since := "2026-05-31")]
/-
**PMF.binomial_one_eq_bernoulli** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：binomial_one_eq_bernoulli (p : Real>=0) (h : p <= 1) : binomial p h 1 = (b
ernoulli p h).map (cond · 1 0)
参数：p : Real>=0；h : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.ext`：∀ {α : Type u_1} {p q : PMF α}, (∀ (x : α), p x = q x) → p = q
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.binomial_apply`：binomial_apply (p : Real>=0) (h : p <= 1) (n : Nat) 
(i : Fin (n + 1)) : binomial p h n i = p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - 
i) : Nat…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.choose_succ_self_right`：∀ (n : ℕ), (n + 1).choose n = n + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PMF.map_apply`：map_apply : (map f p) b = ∑' a, if b = f a then p a else 
0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `PMF.bernoulli_apply`：bernoulli_apply : bernoulli p h b = cond b p (1 - p
)
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The binomial distribution on one coin is the Bernoulli distribution.
-/
theorem binomial_one_eq_bernoulli (p : ℝ≥0) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [binomial_apply, bernoulli_apply]

@[deprecated ProbabilityTheory.binomial_singleton (since := "2026-04-07")]
/-
**PMF.binomial_apply_of_le** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：binomial_apply_of_le {k b : Nat} (hb : k <= b) {x : Real>=0} (h : x <= 1) 
: ENNReal.ofReal ((b.choose k) * x ^ k * (1 - x) ^ (b - k)) = PMF.binomial x h b
 (Fin.ofNat (b + 1) k)
参数：hb : k <= b；h : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.ofNat_eq_cast`：ofNat_eq_cast (n : Nat) [NeZero n] (a : Nat) : Fin.of
Nat n a = (a : Fin n)
· 使用定理 `PMF.binomial_apply`：binomial_apply (p : Real>=0) (h : p <= 1) (n : Nat) 
(i : Fin (n + 1)) : binomial p h n i = p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - 
i) : Nat…
· 使用定理 `Fin.val_natCast`：∀ (a n : ℕ) [inst : NeZero n], ↑↑a = a % n
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
-/
theorem binomial_apply_of_le {k b : ℕ} (hb : k ≤ b) {x : ℝ≥0} (h : x ≤ 1) :
    ENNReal.ofReal ((b.choose k) * x ^ k * (1 - x) ^ (b - k))
    = PMF.binomial x h b (Fin.ofNat (b + 1) k) := by
  have eq0 : k % (b + 1) = k := by simpa using Order.lt_add_one_iff.mpr hb
  have eq1 : 1 - (x : ℝ≥0∞) = ENNReal.ofReal (1 - x : ℝ) := by norm_cast
  have : (1 - (x : ℝ)) ≥ 0 := by simpa
  rwa [Fin.ofNat_eq_cast, PMF.binomial_apply, Fin.val_natCast, Fin.val_last, eq0, eq1,
    coe_nnreal_eq x, mul_rotate, ofReal_mul, ofReal_mul, ofReal_pow, ofReal_pow, ofReal_natCast]
  all_goals positivity

end PMF

