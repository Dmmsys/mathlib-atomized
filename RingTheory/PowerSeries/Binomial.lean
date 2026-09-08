/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.SuppressCompilation

/-!
# Binomial Power Series

We introduce formal power series of the form `(1 + X) ^ r`, where `r` is an element of a
commutative binomial ring `R`.

## Main Definitions
* `PowerSeries.binomialSeries`: A power series expansion of `(1 + X) ^ r`, where `r` is an element
  of a commutative binomial ring `R`.

## Main Results
* `PowerSeries.binomial_add`: Adding exponents yields multiplication of series.
* `PowerSeries.binomialSeries_nat`: when `r` is a natural number, we get `(1 + X) ^ r`.
* `PowerSeries.rescale_neg_one_invOneSubPow`: The image of `(1 - X) ^ (-d)` under the map
  `X ↦ (-X)` is `(1 + X) ^ (-d)`

## TODO
* When `A` is a commutative `R`-algebra, the exponentiation action makes the multiplicative group
  `1 + XA[[X]]` into an `R`-module.

-/

@[expose] public section

open Finset

suppress_compilation

variable {R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

/-- The power series for `(1 + X) ^ r`. -/
/-
**PowerSeries.binomialSeries** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A
参数：A；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series for `(1 + X) ^ r`.
-/
def binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A :=
  mk fun n => Ring.choose r n • 1

@[simp]
/-
**PowerSeries.binomialSeries_coeff** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：binomialSeries_coeff [Semiring A] [SMul R A] (r : R) (n : Nat) : coeff n (
binomialSeries A r) = Ring.choose r n • 1
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
lemma binomialSeries_coeff [Semiring A] [SMul R A] (r : R) (n : ℕ) :
    coeff n (binomialSeries A r) = Ring.choose r n • 1 :=
  coeff_mk n fun n ↦ Ring.choose r n • 1

@[simp]
/-
**PowerSeries.binomialSeries_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：binomialSeries_constantCoeff [Ring A] [Algebra R A] (r : R) : constantCoef
f (binomialSeries A r) = 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma binomialSeries_constantCoeff [Ring A] [Algebra R A] (r : R) :
    constantCoeff (binomialSeries A r) = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]
/-
**PowerSeries.binomialSeries_add** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：binomialSeries_add [Ring A] [Algebra R A] (r s : R) : binomialSeries A (r 
+ s) = binomialSeries A r * binomialSeries A s
参数：r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.add_choose_eq`：add_choose_eq [Ring R] [BinomialRing R] {r s : R} (k
 : Nat) (h : Commute r s) : choose (r + s) k = ∑ ij in antidiagonal k, choose r 
ij.1 * c…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma binomialSeries_add [Ring A] [Algebra R A] (r s : R) :
    binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s := by
  ext n
  simp only [binomialSeries_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm, mul_smul]

@[simp]
/-
**PowerSeries.binomialSeries_nat** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：binomialSeries_nat [Ring A] [Algebra R A] (d : Nat) : binomialSeries A (d 
: R) = (1 + X) ^ d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_pow`：coe_pow (n : Nat) : ((φ ^ n : R[X]) : PowerSeries R)
 = (φ : PowerSeries R) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coe_add`：coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coe_one`：coe_one : ((1 : R[X]) : PowerSeries R) = 1
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `Polynomial.coeff_one_add_X_pow`：coeff_one_add_X_pow (R : Type*) [Semirin
g R] (n k : Nat) : ((1 + X) ^ n).coeff k = (n.choose k : R)
· 使用定理 `Ring.choose_natCast`：choose_natCast [NatPowAssoc R] (n k : Nat) : choose
 (n : R) k = Nat.choose n k
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma binomialSeries_nat [Ring A] [Algebra R A] (d : ℕ) :
    binomialSeries A (d : R) = (1 + X) ^ d := by
  ext n
  have hright : (1 + X) ^ d = (((1 : Polynomial A) + (Polynomial.X)) ^ d).toPowerSeries := by
    simp
  rw [hright, Polynomial.coeff_coe, binomialSeries_coeff, Polynomial.coeff_one_add_X_pow]
  simp [Ring.choose_natCast, Nat.cast_smul_eq_nsmul]

@[simp]
/-
**PowerSeries.binomialSeries_zero** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：binomialSeries_zero [Ring A] [Algebra R A] : binomialSeries A (0 : R) = (1
 : A⟦X⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `PowerSeries.binomialSeries_nat`：binomialSeries_nat [Ring A] [Algebra R A
] (d : Nat) : binomialSeries A (d : R) = (1 + X) ^ d
-/
lemma binomialSeries_zero [Ring A] [Algebra R A] :
    binomialSeries A (0 : R) = (1 : A⟦X⟧) := by
  simpa using binomialSeries_nat 0
/-
**PowerSeries.rescale_neg_one_invOneSubPow** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：rescale_neg_one_invOneSubPow [CommRing A] (d : Nat) : rescale (-1 : A) (in
vOneSubPow A d) = binomialSeries A (-d : Int)
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用引理 `PowerSeries.binomialSeries_coeff`：binomialSeries_coeff [Semiring A] [SMu
l R A] (r : R) (n : Nat) : coeff n (binomialSeries A r) = Ring.choose r n • 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_negOnePow_natCast`：cast_negOnePow_natCast (R : Type*) [Ring R] 
(n : Nat) : negOnePow n = (-1 : R) ^ n
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Ring.choose_zero_ite`：choose_zero_ite (R) [NonAssocRing R] [Pow R Nat] [
NatPowAssoc R] [BinomialRing R] (k : Nat) : choose (0 : R) k = if k = 0 then 1 e
lse 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 37 条，此处仅展示前 30 条）
-/
lemma rescale_neg_one_invOneSubPow [CommRing A] (d : ℕ) :
    rescale (-1 : A) (invOneSubPow A d) = binomialSeries A (-d : ℤ) := by
  ext n
  rw [coeff_rescale, binomialSeries_coeff, ← Int.cast_negOnePow_natCast, ← zsmul_eq_mul]
  cases d with
  | zero =>
    by_cases hn : n = 0 <;> simp [invOneSubPow, Ring.choose_zero_ite, hn]
  | succ d =>
    simp only [invOneSubPow, coeff_mk, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
      zsmul_eq_mul, mul_one]
    rw [show (-1 : ℤ) + -d = -(d + 1) by abel, Ring.choose_neg, Nat.choose_symm_add, Units.smul_def,
      show (d : ℤ) + 1 + n - 1 = d + n by lia, ← Nat.cast_add, Ring.choose_natCast]
    norm_cast

end PowerSeries

