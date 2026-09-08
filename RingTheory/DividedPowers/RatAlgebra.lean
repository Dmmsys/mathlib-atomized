/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.RingTheory.DividedPowers.Basic

/-! # Examples of divided power structures

In this file we show that, for certain choices of a commutative (semi)ring `A` and an ideal `I` of
`A`, the family of maps `ℕ → A → A` given by `fun n x ↦ x^n/n!` is a divided power structure on `I`.

## Main Definitions

* `DividedPowers.OfInvertibleFactorial.dpow` : the family of functions `ℕ → A → A` given by
  `x^n/n!`.
* `DividedPowers.OfInvertibleFactorial.dividedPowers` : the divided power structure on `I` given by
  `fun x n ↦ x^n/n!`, assuming that there exists a natural number `n` such that `f (n-1)!` is
  invertible in `A` and `I^n = 0`.
* `DividedPowers.OfSquareZero.dividedPowers` : given an ideal `I` such that `I^2 =0`, this is
  the divided power structure on `I` given by `fun x n ↦ x^n/n!`.
* `DividedPowers.CharP.dividedPowers` : if `A` is a commutative ring of prime characteristic `p`
  and `I` is an ideal such that `I^p = 0`, , this is the divided power structure on `I` given by
  `fun x n ↦ x^n/n!`.
* `DividedPowers.RatAlgebra.dividedPowers` : if `I` is any ideal in a `ℚ`-algebra, this is the
  divided power structure on `I` given by `fun x n ↦ x^n/n!`.

## Main Results

* `DividedPowers.RatAlgebra.dividedPowers_unique`: there are no other divided power structures on an
  ideal of a `ℚ`-algebra.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

-/

@[expose] public section

open Nat Ring

namespace DividedPowers

namespace OfInvertibleFactorial

variable {A : Type*} [CommSemiring A] (I : Ideal A) [DecidablePred (fun x ↦ x ∈ I)]

/-- The family of functions `ℕ → A → A` given by `x^n/n!`. -/
/-
**DividedPowers.OfInvertibleFactorial.dpow** 是 Mathlib 中的一个定义，位于命名空间 `DividedPow
ers.OfInvertibleFactorial`。
形式化陈述：dpow : Nat -> A -> A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of functions `ℕ → A → A` given by `x^n/n!`.
-/
noncomputable def dpow : ℕ → A → A := fun m x => if x ∈ I then inverse (m ! : A) * x ^ m else 0

variable {I}
/-
**DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `
DividedPowers.OfInvertibleFactorial`。
形式化陈述：dpow_eq_of_mem {m : Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m !
 : A) * x ^ m
参数：hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dpow_eq_of_mem {m : ℕ} {x : A} (hx : x ∈ I) : dpow I m x = inverse (m ! : A) * x ^ m := by
  simp [dpow, hx]
/-
**DividedPowers.OfInvertibleFactorial.dpow_eq_of_not_mem** 是 Mathlib 中的一个定理，位于命名
空间 `DividedPowers.OfInvertibleFactorial`。
形式化陈述：dpow_eq_of_not_mem {m : Nat} {x : A} (hx : x ∉ I) : dpow I m x = 0
参数：hx : x ∉ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dpow_eq_of_not_mem {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by simp [dpow, hx]
/-
**DividedPowers.OfInvertibleFactorial.dpow_null** 是 Mathlib 中的一个定理，位于命名空间 `Divid
edPowers.OfInvertibleFactorial`。
形式化陈述：dpow_null {m : Nat} {x : A} (hx : x ∉ I) : dpow I m x = 0
参数：hx : x ∉ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dpow_null {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by simp [dpow, hx]
/-
**DividedPowers.OfInvertibleFactorial.dpow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Divid
edPowers.OfInvertibleFactorial`。
形式化陈述：dpow_zero {x : A} (hx : x in I) : dpow I 0 x = 1
参数：hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ring.inverse_one`：inverse_one : (1 : M₀)⁻¹ʳ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dpow_zero {x : A} (hx : x ∈ I) : dpow I 0 x = 1 := by simp [dpow, hx]
/-
**DividedPowers.OfInvertibleFactorial.dpow_one** 是 Mathlib 中的一个定理，位于命名空间 `Divide
dPowers.OfInvertibleFactorial`。
形式化陈述：dpow_one {x : A} (hx : x in I) : dpow I 1 x = x
参数：hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ring.inverse_one`：inverse_one : (1 : M₀)⁻¹ʳ = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dpow_one {x : A} (hx : x ∈ I) : dpow I 1 x = x := by simp [dpow_eq_of_mem hx]
/-
**DividedPowers.OfInvertibleFactorial.dpow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Divide
dPowers.OfInvertibleFactorial`。
形式化陈述：dpow_mem {m : Nat} (hm : m != 0) {x : A} (hx : x in I) : dpow I m x in I
参数：hm : m != 0；hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.pow_mem_of_mem`：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n
) : a ^ n in I
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem dpow_mem {m : ℕ} (hm : m ≠ 0) {x : A} (hx : x ∈ I) : dpow I m x ∈ I := by
  rw [dpow_eq_of_mem hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))
/-
**DividedPowers.OfInvertibleFactorial.dpow_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `
DividedPowers.OfInvertibleFactorial`。
形式化陈述：dpow_add_of_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m : Nat} (hmn :
 m < n) {x y : A} (hx : x in I) (hy : y in I) : dpow I m (x + y) = (Finset.antid
iagonal m).sum (fun k => dpow I k.1 x * dpow I k.2 y)
参数：hn_fac : IsUnit ((n - 1)! : A)；hmn : m < n；hx : x in I；hy : y in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ring.inverse_mul_eq_iff_eq_mul`：inverse_mul_eq_iff_eq_mul (x y z : M₀) (
h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z
· 使用定理 `IsUnit.natCast_factorial_of_lt`：natCast_factorial_of_lt {n : Nat} (hn_fa
c : IsUnit ((n - 1)! : A)) {m : Nat} (hmn : m < n) : IsUnit (m ! : A)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Commute.add_pow'`：add_pow' (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑
 m in antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.smul_congr`：∀ {R : Type u_2} {α : Type u_3} [
inst : CommSemiring α] [inst_1 : SMul R α] {r : R} {a b t c : α},   a = b → (∀ (
x : α), r • x = t * x) → t …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 45 条，此处仅展示前 30 条）
-/
theorem dpow_add_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} (hmn : m < n)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum (fun k ↦ dpow I k.1 x * dpow I k.2 y) := by
  rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn),
    Finset.mul_sum, Commute.add_pow' (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hx, if_pos hy]
  ring_nf
  simp only [mul_assoc]; congr; rw [← mul_assoc]
  exact castChoose_eq (hn_fac.natCast_factorial_of_lt hmn) hk
/-
**DividedPowers.OfInvertibleFactorial.dpow_add** 是 Mathlib 中的一个定理，位于命名空间 `Divide
dPowers.OfInvertibleFactorial`。
形式化陈述：dpow_add {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m :
 Nat} {x : A} (hx : x in I) {y : A} (hy : y in I) : dpow I m (x + y) = (Finset.a
ntidiagonal m).sum fun k => dpow I k.1 x * dpow I k.2 y
参数：hn_fac : IsUnit ((n - 1)! : A)；hnI : I ^ n = 0；hx : x in I；hy : y in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_add_of_lt`：dpow_add_of_lt {n : 
Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m : Nat} (hmn : m < n) {x y : A} (hx : x 
in I) (hy : y in I) : dpow I m (x + y) =…
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
-/
theorem dpow_add {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m : ℕ} {x : A}
    (hx : x ∈ I) {y : A} (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum fun k ↦ dpow I k.1 x * dpow I k.2 y := by
  by_cases! hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · have h_sub : I ^ m ≤ I ^ n := Ideal.pow_le_pow_right hmn
    rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 := by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
      exact Set.mem_of_subset_of_mem h_sub (Ideal.pow_mem_pow (Ideal.add_mem I hx hy) m)
    rw [hxy, mul_zero, eq_comm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_pos hx, if_pos hy, mul_assoc, mul_comm (x ^ k.1), mul_assoc, ← mul_assoc]
    apply mul_eq_zero_of_right
    rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
    apply Set.mem_of_subset_of_mem h_sub
    rw [← Finset.mem_antidiagonal.mp hk, add_comm, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hy _) (Ideal.pow_mem_pow hx _)
/-
**DividedPowers.OfInvertibleFactorial.dpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Divide
dPowers.OfInvertibleFactorial`。
形式化陈述：dpow_mul {m : Nat} {a x : A} (hx : x in I) : dpow I m (a * x) = a ^ m * dp
ow I m x
参数：hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dpow_mul {m : ℕ} {a x : A} (hx : x ∈ I) : dpow I m (a * x) = a ^ m * dpow I m x := by
  rw [dpow_eq_of_mem (Ideal.mul_mem_left I _ hx), dpow_eq_of_mem hx,
    mul_pow, ← mul_assoc, mul_comm _ (a ^ m), mul_assoc]
/-
**DividedPowers.OfInvertibleFactorial.dpow_mul_of_add_lt** 是 Mathlib 中的一个定理，位于命名
空间 `DividedPowers.OfInvertibleFactorial`。
形式化陈述：dpow_mul_of_add_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat} 
(hkm : m + k < n) {x : A} (hx : x in I) : dpow I m x * dpow I k x = ↑((m + k).ch
oose m) * dpow I (m + k) x
参数：hn_fac : IsUnit ((n - 1)! : A)；hkm : m + k < n；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Ring.eq_mul_inverse_iff_mul_eq`：eq_mul_inverse_iff_mul_eq (x y z : M₀) (
h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y
· 使用定理 `IsUnit.natCast_factorial_of_lt`：natCast_factorial_of_lt {n : Nat} (hn_fa
c : IsUnit ((n - 1)! : A)) {m : Nat} (hmn : m < n) : IsUnit (m ! : A)
· 使用定理 `Ring.inverse_mul_eq_iff_eq_mul`：inverse_mul_eq_iff_eq_mul (x y z : M₀) (
h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.add_choose_mul_factorial_mul_factorial`：add_choose_mul_factorial_mul
_factorial (i j : Nat) : (i + j).choose j * i ! * j ! = (i + j)!
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
-/
theorem dpow_mul_of_add_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m k : ℕ}
    (hkm : m + k < n) {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hx, dpow_eq_of_mem hx, dpow_eq_of_mem hx,
    mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m),
    ← pow_add, ← mul_assoc, ← mul_assoc]
  apply congr_arg₂ _ _ rfl
  rw [eq_mul_inverse_iff_mul_eq _ _ _ (hn_fac.natCast_factorial_of_lt hkm),
      mul_assoc,
      inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hm),
      inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hk)]
  norm_cast; apply congr_arg
  rw [← Nat.add_choose_mul_factorial_mul_factorial, mul_comm, mul_comm _ (m !), Nat.choose_symm_add]
/-
**DividedPowers.OfInvertibleFactorial.mul_dpow** 是 Mathlib 中的一个定理，位于命名空间 `Divide
dPowers.OfInvertibleFactorial`。
形式化陈述：mul_dpow {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n 
= 0) {m k : Nat} {x : A} (hx : x in I) : dpow I m x * dpow I k x = ↑((m + k).cho
ose m) * dpow I (m + k) x
参数：hn_fac : IsUnit ((n - 1).factorial : A)；hnI : I ^ n = 0；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mul_of_add_lt`：dpow_mul_of_add_
lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat} (hkm : m + k < n) {x :
 A} (hx : x in I) : dpow I m x * dpow I k x …
· 使用定理 `Ideal.pow_eq_zero_of_mem`：pow_eq_zero_of_mem {I : Ideal R} {n m : Nat} (
hnI : I ^ n = 0) (hmn : n <= m) {x : R} (hx : x in I) : x ^ m = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_dpow {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  by_cases! hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.pow_eq_zero_of_mem hnI hkm hx
    rw [dpow_eq_of_mem hx, dpow_eq_of_mem hx, dpow_eq_of_mem hx,
      mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m), ← pow_add, hxmk,
      mul_zero, mul_zero, mul_zero, mul_zero]
/-
**DividedPowers.OfInvertibleFactorial.dpow_comp_of_mul_lt** 是 Mathlib 中的一个定理，位于命
名空间 `DividedPowers.OfInvertibleFactorial`。
形式化陈述：dpow_comp_of_mul_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat}
 (hk : k != 0) (hkm : m * k < n) {x : A} (hx : x in I) : dpow I m (dpow I k x) =
 ↑(uniformBell m k) * dpow I (m * k) x
参数：hn_fac : IsUnit ((n - 1)! : A)；hk : k != 0；hkm : m * k < n；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mem`：dpow_mem {m : Nat} (hm : m
 != 0) {x : A} (hx : x in I) : dpow I m x in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.uniformBell_zero_left`：uniformBell_zero_left (n : Nat) : uniformBell
 0 n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Ring.eq_mul_inverse_iff_mul_eq`：eq_mul_inverse_iff_mul_eq (x y z : M₀) (
h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y
· 使用定理 `IsUnit.natCast_factorial_of_lt`：natCast_factorial_of_lt {n : Nat} (hn_fa
c : IsUnit ((n - 1)! : A)) {m : Nat} (hmn : m < n) : IsUnit (m ! : A)
· 使用定理 `Ring.inverse_mul_eq_iff_eq_mul`：inverse_mul_eq_iff_eq_mul (x y z : M₀) (
h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z
· 使用引理 `Ring.inverse_pow_mul_eq_iff_eq_mul`：inverse_pow_mul_eq_iff_eq_mul {a : M
₀} (b c : M₀) (ha : IsUnit a) {k : Nat} : a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c
· 使用定理 `Nat.uniformBell_mul_eq`：uniformBell_mul_eq (m : Nat) {n : Nat} (hn : n !
= 0) : uniformBell m n * n ! ^ m * m ! = (m * n)!
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
（共 53 条，此处仅展示前 30 条）
-/
theorem dpow_comp_of_mul_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m k : ℕ} (hk : k ≠ 0)
    (hkm : m * k < n) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m := m * k) hx, dpow_eq_of_mem (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero_left, cast_one, one_mul]
  · have hkn : k < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)) hkm
    rw [dpow_eq_of_mem hx, mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [eq_mul_inverse_iff_mul_eq _ _ _ (hn_fac.natCast_factorial_of_lt hkm),
      mul_assoc, inverse_mul_eq_iff_eq_mul _ _ _ (hn_fac.natCast_factorial_of_lt hmn),
      inverse_pow_mul_eq_iff_eq_mul _ _ (hn_fac.natCast_factorial_of_lt hkn),
      ← uniformBell_mul_eq _ hk]
    push_cast
    ring_nf
/-
**DividedPowers.OfInvertibleFactorial.dpow_comp** 是 Mathlib 中的一个定理，位于命名空间 `Divid
edPowers.OfInvertibleFactorial`。
形式化陈述：dpow_comp {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n
 = 0) {m k : Nat} (hk : k != 0) {x : A} (hx : x in I) : dpow I m (dpow I k x) = 
↑(uniformBell m k) * dpow I (m * k) x
参数：hn_fac : IsUnit ((n - 1).factorial : A)；hnI : I ^ n = 0；hk : k != 0；hx : x in
 I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_comp_of_mul_lt`：dpow_comp_of_mu
l_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m k : Nat} (hk : k != 0) (hkm :
 m * k < n) {x : A} (hx : x in I) : dpow I m …
· 使用定理 `Ideal.pow_eq_zero_of_mem`：pow_eq_zero_of_mem {I : Ideal R} {n m : Nat} (
hnI : I ^ n = 0) (hmn : n <= m) {x : R} (hx : x in I) : x ^ m = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mem`：dpow_mem {m : Nat} (hm : m
 != 0) {x : A} (hx : x in I) : dpow I m x in I
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem dpow_comp {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  by_cases! hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.pow_eq_zero_of_mem hnI hmk hx
    rw [dpow_eq_of_mem (dpow_mem hk hx), dpow_eq_of_mem hx, dpow_eq_of_mem hx,
      mul_pow, ← pow_mul, ← mul_assoc, mul_comm k, hxmk, mul_zero, mul_zero, mul_zero]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `(n-1)!` is invertible in `A` and `I^n = 0`, then `I` admits a divided power structure.
  Proposition 1.2.7 of [B74], part (ii). -/
/-
**DividedPowers.OfInvertibleFactorial.dividedPowers** 是 Mathlib 中的一个定义，位于命名空间 `D
ividedPowers.OfInvertibleFactorial`。
形式化陈述：dividedPowers {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I
 ^ n = 0) : DividedPowers I where dpow
参数：hn_fac : IsUnit ((n - 1).factorial : A)；hnI : I ^ n = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_null`：dpow_null {m : Nat} {x : 
A} (hx : x ∉ I) : dpow I m x = 0
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_zero`：dpow_zero {x : A} (hx : x
 in I) : dpow I 0 x = 1
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_one`：dpow_one {x : A} (hx : x i
n I) : dpow I 1 x = x
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mem`：dpow_mem {m : Nat} (hm : m
 != 0) {x : A} (hx : x in I) : dpow I m x in I
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_add`：dpow_add {n : Nat} (hn_fac
 : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m : Nat} {x : A} (hx : x in I) {y :
 A} (hy : y in I) : dpow I m (x + …
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mul`：dpow_mul {m : Nat} {a x : 
A} (hx : x in I) : dpow I m (a * x) = a ^ m * dpow I m x
· 使用定理 `DividedPowers.OfInvertibleFactorial.mul_dpow`：mul_dpow {n : Nat} (hn_fac
 : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) {m k : Nat} {x : A} (hx : x
 in I) : dpow I m x * dpow I k x =…
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_comp`：dpow_comp {n : Nat} (hn_f
ac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) {m k : Nat} (hk : k != 0)
 {x : A} (hx : x in I) : dpow I m (…

--- 原说明 ---
If `(n-1)!` is invertible in `A` and `I^n = 0`, then `I` admits a divided power 
structure.
  Proposition 1.2.7 of [B74], part (ii).
-/
noncomputable def dividedPowers {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A))
    (hnI : I ^ n = 0) : DividedPowers I where
  dpow            := dpow I
  dpow_null hx    := dpow_null hx
  dpow_zero hx    := dpow_zero hx
  dpow_one hx     := dpow_one hx
  dpow_mem hn hx  := dpow_mem hn hx
  dpow_add hx hy  := dpow_add hn_fac hnI hx hy
  dpow_mul        := dpow_mul
  mul_dpow hx     := mul_dpow hn_fac hnI hx
  dpow_comp hk hx := dpow_comp hn_fac hnI hk hx
/-
**DividedPowers.OfInvertibleFactorial.dpow_apply** 是 Mathlib 中的一个引理，位于命名空间 `Divi
dedPowers.OfInvertibleFactorial`。
形式化陈述：dpow_apply {n : Nat} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ 
n = 0) {m : Nat} {x : A} : (dividedPowers hn_fac hnI).dpow m x = if x in I then 
inverse (m.factorial : A) * x ^ m else 0
参数：hn_fac : IsUnit ((n - 1).factorial : A)；hnI : I ^ n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma dpow_apply {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m : ℕ} {x : A} :
  (dividedPowers hn_fac hnI).dpow m x =
    if x ∈ I then inverse (m.factorial : A) * x ^ m else 0 := rfl

end OfInvertibleFactorial

namespace OfSquareZero

variable {A : Type*} [CommSemiring A] {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)]
  (hI2 : I ^ 2 = 0)

/-- If `I^2 = 0`, then `I` admits a divided power structure. -/
/-
**DividedPowers.OfSquareZero.dividedPowers** 是 Mathlib 中的一个定义，位于命名空间 `DividedPow
ers.OfSquareZero`。
形式化陈述：dividedPowers : DividedPowers I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I^2 = 0`, then `I` admits a divided power structure.
-/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (by norm_num) hI2
/-
**DividedPowers.OfSquareZero.dpow_of_two_le** 是 Mathlib 中的一个定理，位于命名空间 `DividedPo
wers.OfSquareZero`。
形式化陈述：dpow_of_two_le {n : Nat} (hn : 2 <= n) (a : A) : (dividedPowers hI2) n a =
 0
参数：hn : 2 <= n；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.pow_eq_zero_of_mem`：pow_eq_zero_of_mem {I : Ideal R} {n m : Nat} (
hnI : I ^ n = 0) (hmn : n <= m) {x : R} (hx : x in I) : x ^ m = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem dpow_of_two_le {n : ℕ} (hn : 2 ≤ n) (a : A) :
    (dividedPowers hI2) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hI2 hn ha, mul_zero]

end OfSquareZero

namespace IsNilpotent

variable {A : Type*} [CommRing A] {p : ℕ} [Fact (Nat.Prime p)] (hp : IsNilpotent (p : A))
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
/-
**DividedPowers.IsNilpotent.dividedPowers** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowe
rs.IsNilpotent`。
形式化陈述：dividedPowers : DividedPowers I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal suc
h that
  `I^p = 0`, then `I` admits a divided power structure.
-/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (n := p)
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hIp
/-
**DividedPowers.IsNilpotent.dpow_of_prime_le** 是 Mathlib 中的一个定理，位于命名空间 `DividedP
owers.IsNilpotent`。
形式化陈述：dpow_of_prime_le {n : Nat} (hn : p <= n) (a : A) : (dividedPowers hp hIp) 
n a = 0
参数：hn : p <= n；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.pow_eq_zero_of_mem`：pow_eq_zero_of_mem {I : Ideal R} {n m : Nat} (
hnI : I ^ n = 0) (hmn : n <= m) {x : R} (hx : x in I) : x ^ m = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers hp hIp) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha, mul_zero]

end IsNilpotent

namespace CharP

variable (A : Type*) [CommRing A] (p : ℕ) [CharP A p] [Fact (Nat.Prime p)]
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
/-
**DividedPowers.CharP.dividedPowers** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers.Cha
rP`。
形式化陈述：dividedPowers : DividedPowers I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal suc
h that
  `I^p = 0`, then `I` admits a divided power structure.
-/
noncomputable def dividedPowers : DividedPowers I :=
  IsNilpotent.dividedPowers ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp
/-
**DividedPowers.CharP.dpow_of_prime_le** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowers.
CharP`。
形式化陈述：dpow_of_prime_le {n : Nat} (hn : p <= n) (a : A) : (dividedPowers A p hIp)
 n a = 0
参数：hn : p <= n；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.pow_eq_zero_of_mem`：pow_eq_zero_of_mem {I : Ideal R} {n m : Nat} (
hnI : I ^ n = 0) (hmn : n <= m) {x : R} (hx : x in I) : x ^ m = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers A p hIp) n a = 0 := by
  simp only [dividedPowers, IsNilpotent.dividedPowers, OfInvertibleFactorial.dpow_apply,
    ite_eq_right_iff]
  intro ha
  rw [Ideal.pow_eq_zero_of_mem hIp hn ha, mul_zero]

end CharP

-- We formalize example 2 from [BO], Section 3.
namespace RatAlgebra

variable {R : Type*} [CommSemiring R] (I : Ideal R) [DecidablePred (fun x ↦ x ∈ I)]

/-- The family `ℕ → R → R` given by `dpow n x = x ^ n / n!`. -/
/-
**DividedPowers.RatAlgebra.dpow** 是 Mathlib 中的一个定义，位于命名空间 `DividedPowers.RatAlge
bra`。
形式化陈述：dpow : Nat -> R -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family `ℕ → R → R` given by `dpow n x = x ^ n / n!`.
-/
noncomputable def dpow : ℕ → R → R := OfInvertibleFactorial.dpow I

variable {I}
/-
**DividedPowers.RatAlgebra.dpow_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `DividedPowe
rs.RatAlgebra`。
形式化陈述：dpow_eq_of_mem (n : Nat) {x : R} (hx : x in I) : dpow I n x = (inverse n.f
actorial : R) * x ^ n
参数：n : Nat；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DividedPowers.RatAlgebra.dpow.eq_1`：∀ {R : Type u_1} [inst : CommSemirin
g R] (I : Ideal R) [inst_1 : DecidablePred fun x => x ∈ I],   DividedPowers.RatA
lgebra.dpow I = DividedP…
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem`：dpow_eq_of_mem {m : 
Nat} {x : A} (hx : x in I) : dpow I m x = inverse (m ! : A) * x ^ m
-/
theorem dpow_eq_of_mem (n : ℕ) {x : R} (hx : x ∈ I) :
    dpow I n x = (inverse n.factorial : R) * x ^ n := by
  rw [dpow, OfInvertibleFactorial.dpow_eq_of_mem hx]

variable [Algebra ℚ R]

variable (I)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `I` is an ideal in a `ℚ`-algebra `A`, then `I` admits a unique divided power structure,
  given by `dpow n x = x ^ n / n!`. -/
/-
**DividedPowers.RatAlgebra.dividedPowers** 是 Mathlib 中的一个定义，位于命名空间 `DividedPower
s.RatAlgebra`。
形式化陈述：dividedPowers : DividedPowers I where dpow
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_null`：dpow_null {m : Nat} {x : 
A} (hx : x ∉ I) : dpow I m x = 0
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_zero`：dpow_zero {x : A} (hx : x
 in I) : dpow I 0 x = 1
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_one`：dpow_one {x : A} (hx : x i
n I) : dpow I 1 x = x
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mem`：dpow_mem {m : Nat} (hm : m
 != 0) {x : A} (hx : x in I) : dpow I m x in I
· 使用定理 `DividedPowers.OfInvertibleFactorial.dpow_mul`：dpow_mul {m : Nat} {a x : 
A} (hx : x in I) : dpow I m (a * x) = a ^ m * dpow I m x

--- 原说明 ---
If `I` is an ideal in a `ℚ`-algebra `A`, then `I` admits a unique divided power 
structure,
  given by `dpow n x = x ^ n / n!`.
-/
noncomputable def dividedPowers : DividedPowers I where
  dpow           := dpow I
  dpow_null hx   := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx   := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx    := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt
    (IsUnit.natCast_factorial_of_algebra ℚ _) (n.lt_succ_self) hx hy
  dpow_mul hx := OfInvertibleFactorial.dpow_mul hx
  mul_dpow {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt
    (IsUnit.natCast_factorial_of_algebra ℚ _) (m + k).lt_succ_self hx
  dpow_comp hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt
    (IsUnit.natCast_factorial_of_algebra ℚ _) hk (lt_add_one _) hx

@[simp]
/-
**DividedPowers.RatAlgebra.dpow_apply** 是 Mathlib 中的一个引理，位于命名空间 `DividedPowers.R
atAlgebra`。
形式化陈述：dpow_apply {n : Nat} {x : R} : (dividedPowers I).dpow n x = if x in I then
 inverse (n.factorial : R) * x ^ n else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dpow_apply {n : ℕ} {x : R} :
    (dividedPowers I).dpow n x = if x ∈ I then inverse (n.factorial : R) * x ^ n else 0 := rfl

omit [DecidablePred fun x ↦ x ∈ I] in
/-- If `I` is an ideal in a `ℚ`-algebra `A`, then the divided power structure on `I` given by
  `dpow n x = x ^ n / n!` is the only possible one. -/
/-
**DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul** 是 Mathlib 中的一个定理，位于命名空间 `Divi
dedPowers.RatAlgebra`。
形式化陈述：dpow_eq_inv_fact_smul (hI : DividedPowers I) {n : Nat} {x : R} (hx : x in 
I) : hI.dpow n x = (inverse (n.factorial : Rat)) • x ^ n
参数：hI : DividedPowers I；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DividedPowers.factorial_mul_dpow_eq_pow`：factorial_mul_dpow_eq_pow {n : 
Nat} (ha : a in I) : (n ! : A) * hI.dpow n a = a ^ n
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Rat.inv_mul_cancel`：∀ (a : ℚ), a ≠ 0 → a⁻¹ * a = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `I` is an ideal in a `ℚ`-algebra `A`, then the divided power structure on `I`
 given by
  `dpow n x = x ^ n / n!` is the only possible one.
-/
theorem dpow_eq_inv_fact_smul (hI : DividedPowers I) {n : ℕ} {x : R} (hx : x ∈ I) :
    hI.dpow n x = (inverse (n.factorial : ℚ)) • x ^ n := by
  rw [inverse_eq_inv', ← factorial_mul_dpow_eq_pow hI hx, ← smul_eq_mul, ← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : ℚ) • (1 : R) := by
    rw [cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [aux, ← mul_smul]
  suffices (n ! : ℚ)⁻¹ * (n !) = 1 by
    rw [this, one_smul]
  apply Rat.inv_mul_cancel
  rw [← cast_zero, ne_eq]
  simp [factorial_ne_zero]

variable {I}

/-- There are no other divided power structures on an ideal of a  `ℚ`-algebra. -/
/-
**DividedPowers.RatAlgebra.dividedPowers_unique** 是 Mathlib 中的一个定理，位于命名空间 `Divid
edPowers.RatAlgebra`。
形式化陈述：dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I
参数：hI : DividedPowers I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DividedPowers.ext`：DividedPowers.ext (hI : DividedPowers I) (hI' : Divid
edPowers I) (h_eq : forall (n : Nat) {x : A} (_ : x in I), hI.dpow n x = hI'.dpo
w n x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DividedPowers.RatAlgebra.dpow_apply`：dpow_apply {n : Nat} {x : R} : (div
idedPowers I).dpow n x = if x in I then inverse (n.factorial : R) * x ^ n else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ring.inverse_mul_eq_iff_eq_mul`：inverse_mul_eq_iff_eq_mul (x y z : M₀) (
h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z
· 使用定理 `IsUnit.natCast_factorial_of_algebra`：natCast_factorial_of_algebra (K : T
ype*) [Semifield K] [CharZero K] [Algebra K A] (n : Nat) : IsUnit (n ! : A)
· 使用定理 `DividedPowers.factorial_mul_dpow_eq_pow`：factorial_mul_dpow_eq_pow {n : 
Nat} (ha : a in I) : (n ! : A) * hI.dpow n a = a ^ n

--- 原说明 ---
There are no other divided power structures on an ideal of a  `ℚ`-algebra.
-/
theorem dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I :=
  hI.ext _ (fun n x hx ↦ by rw [dpow_apply, if_pos hx, eq_comm, inverse_mul_eq_iff_eq_mul _ _ _
      (IsUnit.natCast_factorial_of_algebra ℚ n), factorial_mul_dpow_eq_pow _ hx])

end RatAlgebra

end DividedPowers

