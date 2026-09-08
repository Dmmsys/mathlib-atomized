/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Oliver Nash
-/
module

public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Newton-Raphson method

Given a single-variable polynomial `P` with derivative `P'`, Newton's method concerns iteration of
the rational map: `x ↦ x - P(x) / P'(x)`.

Over a field, it can serve as a root-finding algorithm. It is also useful in proving results such
as Hensel's lemma and the Jordan-Chevalley decomposition.

## Main definitions / results:

* `Polynomial.newtonMap`: the map `x ↦ x - P(x) / P'(x)`, where `P'` is the derivative of the
  polynomial `P`.
* `Polynomial.isFixedPt_newtonMap_of_isUnit_iff`: `x` is a fixed point for Newton iteration iff
  it is a root of `P` (provided `P'(x)` is a unit).
* `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`: if `x` is almost a root of `P` in the
  sense that `P(x)` is nilpotent (and `P'(x)` is a unit) then we may write `x` as a sum
  `x = n + r` where `n` is nilpotent and `r` is a root of `P`. This can be used to prove the
  Jordan-Chevalley decomposition of linear endomorphisms.

-/

@[expose] public section

open Set Function

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {x : S}

/-- Given a single-variable polynomial `P` with derivative `P'`, this is the map:
`x ↦ x - P(x) / P'(x)`. When `P'(x)` is not a unit we use a junk-value pattern and send `x ↦ x`. -/
/-
**Polynomial.newtonMap** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：newtonMap (x : S) : S
参数：x : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a single-variable polynomial `P` with derivative `P'`, this is the map:
`x ↦ x - P(x) / P'(x)`. When `P'(x)` is not a unit we use a junk-value pattern a
nd send `x ↦ x`.
-/
def newtonMap (x : S) : S :=
  x - (Ring.inverse <| aeval x (derivative P)) * aeval x P
/-
**Polynomial.newtonMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：newtonMap_apply : P.newtonMap x = x - (Ring.inverse <| aeval x (derivative
 P)) * (aeval x P)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem newtonMap_apply :
    P.newtonMap x = x - (Ring.inverse <| aeval x (derivative P)) * (aeval x P) :=
  rfl

variable {P}
/-
**Polynomial.newtonMap_apply_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：newtonMap_apply_of_isUnit (h : IsUnit <| aeval x (derivative P)) : P.newto
nMap x = x - h.unit⁻¹ * aeval x P
参数：h : IsUnit <| aeval x (derivative P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem newtonMap_apply_of_isUnit (h : IsUnit <| aeval x (derivative P)) :
    P.newtonMap x = x - h.unit⁻¹ * aeval x P := by
  simp [newtonMap_apply, Ring.inverse, h]
/-
**Polynomial.newtonMap_apply_of_not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：newtonMap_apply_of_not_isUnit (h : ¬ (IsUnit <| aeval x (derivative P))) :
 P.newtonMap x = x
参数：h : ¬ (IsUnit <| aeval x (derivative P))。
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
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem newtonMap_apply_of_not_isUnit (h : ¬ (IsUnit <| aeval x (derivative P))) :
    P.newtonMap x = x := by
  simp [newtonMap_apply, Ring.inverse, h]
/-
**Polynomial.isNilpotent_iterate_newtonMap_sub_of_isNilpotent** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：isNilpotent_iterate_newtonMap_sub_of_isNilpotent (h : IsNilpotent <| aeval
 x P) (n : Nat) : IsNilpotent P.newtonMap^[n] x - x
参数：h : IsNilpotent <| aeval x P；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Polynomial.newtonMap_apply`：newtonMap_apply : P.newtonMap x = x - (Ring.
inverse <| aeval x (derivative P)) * (aeval x P)
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Commute.isNilpotent_add`：isNilpotent_add (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y)
· 使用引理 `Polynomial.isNilpotent_aeval_sub_of_isNilpotent_sub`：isNilpotent_aeval_s
ub_of_isNilpotent_sub (h : IsNilpotent (a - b)) : IsNilpotent (aeval a P - aeval
 b P)
-/
theorem isNilpotent_iterate_newtonMap_sub_of_isNilpotent (h : IsNilpotent <| aeval x P) (n : ℕ) :
    IsNilpotent <| P.newtonMap^[n] x - x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ', comp_apply, newtonMap_apply, sub_right_comm]
    refine (Commute.all _ _).isNilpotent_sub ih <| (Commute.all _ _).isNilpotent_mul_left ?_
    simpa using Commute.isNilpotent_add (Commute.all _ _)
      (isNilpotent_aeval_sub_of_isNilpotent_sub P ih) h
/-
**Polynomial.isFixedPt_newtonMap_of_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：isFixedPt_newtonMap_of_aeval_eq_zero (h : aeval x P = 0) : IsFixedPt P.new
tonMap x
参数：h : aeval x P = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用定理 `Polynomial.newtonMap_apply`：newtonMap_apply : P.newtonMap x = x - (Ring.
inverse <| aeval x (derivative P)) * (aeval x P)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem isFixedPt_newtonMap_of_aeval_eq_zero (h : aeval x P = 0) :
    IsFixedPt P.newtonMap x := by
  rw [IsFixedPt, newtonMap_apply, h, mul_zero, sub_zero]
/-
**Polynomial.isFixedPt_newtonMap_of_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：isFixedPt_newtonMap_of_isUnit_iff (h : IsUnit <| aeval x (derivative P)) :
 IsFixedPt P.newtonMap x ↔ aeval x P = 0
参数：h : IsUnit <| aeval x (derivative P)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用定理 `Polynomial.newtonMap_apply`：newtonMap_apply : P.newtonMap x = x - (Ring.
inverse <| aeval x (derivative P)) * (aeval x P)
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `Ring.inverse_mul_eq_iff_eq_mul`：inverse_mul_eq_iff_eq_mul (x y z : M₀) (
h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isFixedPt_newtonMap_of_isUnit_iff (h : IsUnit <| aeval x (derivative P)) :
    IsFixedPt P.newtonMap x ↔ aeval x P = 0 := by
  rw [IsFixedPt, newtonMap_apply, sub_eq_self, Ring.inverse_mul_eq_iff_eq_mul _ _ _ h, mul_zero]

/-- This is really an auxiliary result, en route to
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`. -/
/-
**Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：aeval_pow_two_pow_dvd_aeval_iterate_newtonMap (h : IsNilpotent (aeval x P)
) (h' : IsUnit (aeval x <| derivative P)) (n : Nat) : (aeval x P) ^ (2 ^ n) ∣ ae
val (P.newtonMap^[n] x) P
参数：h : IsNilpotent (aeval x P)；h' : IsUnit (aeval x <| derivative P)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Polynomial.newtonMap_apply`：newtonMap_apply : P.newtonMap x = x - (Ring.
inverse <| aeval x (derivative P)) * (aeval x P)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub`：isUnit_aeval
_of_isUnit_aeval_of_isNilpotent_sub (hb : IsUnit (aeval b P)) (hab : IsNilpotent
 (a - b)) : IsUnit (aeval a P)
· 使用定理 `Polynomial.isNilpotent_iterate_newtonMap_sub_of_isNilpotent`：isNilpotent
_iterate_newtonMap_sub_of_isNilpotent (h : IsNilpotent <| aeval x P) (n : Nat) :
 IsNilpotent P.newtonMap^[n] x - x
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Ring.mul_inverse_cancel`：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x 
* x⁻¹ʳ = 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
This is really an auxiliary result, en route to
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`.
-/
theorem aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) (n : ℕ) :
    (aeval x P) ^ (2 ^ n) ∣ aeval (P.newtonMap^[n] x) P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ⟨d, hd⟩ := binomExpansion (P.map (algebraMap R S)) (P.newtonMap^[n] x)
      (-Ring.inverse (aeval (P.newtonMap^[n] x) <| derivative P) * aeval (P.newtonMap^[n] x) P)
    rw [eval_map_algebraMap, eval_map_algebraMap] at hd
    rw [iterate_succ', comp_apply, newtonMap_apply, sub_eq_add_neg, neg_mul_eq_neg_mul, hd]
    refine dvd_add ?_ (dvd_mul_of_dvd_right ?_ _)
    · convert! dvd_zero _
      have : IsUnit (aeval (P.newtonMap^[n] x) <| derivative P) :=
        isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' <|
        isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n
      rw [derivative_map, eval_map_algebraMap, ← mul_assoc, mul_neg, Ring.mul_inverse_cancel _ this,
        neg_mul, one_mul, add_neg_cancel]
    · rw [neg_mul, even_two.neg_pow, mul_pow, pow_succ, pow_mul]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ih 2) _

/-- If `x` is almost a root of `P` in the sense that `P(x)` is nilpotent (and `P'(x)` is a
unit) then we may write `x` as a sum `x = n + r` where `n` is nilpotent and `r` is a root of `P`.
Moreover, `n` and `r` are unique.

This can be used to prove the Jordan-Chevalley decomposition of linear endomorphisms. -/
/-
**Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：existsUnique_nilpotent_sub_and_aeval_eq_zero (h : IsNilpotent (aeval x P))
 (h' : IsUnit (aeval x <| derivative P)) : exists! r, IsNilpotent (x - r) ∧ aeva
l r P = 0
参数：h : IsNilpotent (aeval x P)；h' : IsUnit (aeval x <| derivative P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `Polynomial.isNilpotent_iterate_newtonMap_sub_of_isNilpotent`：isNilpotent
_iterate_newtonMap_sub_of_isNilpotent (h : IsNilpotent <| aeval x P) (n : Nat) :
 IsNilpotent P.newtonMap^[n] x - x
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_two_pow_self`：∀ {n : ℕ}, n < 2 ^ n
· 使用定理 `Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`：aeval_pow_two_
pow_dvd_aeval_iterate_newtonMap (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeva
l x <| derivative P)) (n : Nat) : (aeval x P) …
· 使用引理 `Polynomial.isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub`：isUnit_aeval
_of_isUnit_aeval_of_isNilpotent_sub (hb : IsUnit (aeval b P)) (hab : IsNilpotent
 (a - b)) : IsUnit (aeval a P)
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `IsNilpotent.isUnit_add_left_of_commute`：IsNilpotent.isUnit_add_left_of_c
ommute [Ring R] {r u : R} (hnil : IsNilpotent r) (hu : IsUnit u) (h_comm : Commu
te r u) : IsUnit (u + r)
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsUnit.mul_right_eq_zero`：mul_right_eq_zero {a b : M₀} (ha : IsUnit a) :
 a * b = 0 ↔ b = 0
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f

--- 原说明 ---
If `x` is almost a root of `P` in the sense that `P(x)` is nilpotent (and `P'(x)
` is a
unit) then we may write `x` as a sum `x = n + r` where `n` is nilpotent and `r` 
is a root of `P`.
Moreover, `n` and `r` are unique.

This can be used to prove the Jordan-Chevalley decomposition of linear endomorph
isms.
-/
theorem existsUnique_nilpotent_sub_and_aeval_eq_zero
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) :
    ∃! r, IsNilpotent (x - r) ∧ aeval r P = 0 := by
  simp_rw [(neg_sub _ x).symm, isNilpotent_neg_iff]
  refine existsUnique_of_exists_of_unique ?_ fun r₁ r₂ ⟨hr₁, hr₁'⟩ ⟨hr₂, hr₂'⟩ ↦ ?_
  · -- Existence
    obtain ⟨n, hn⟩ := id h
    refine ⟨P.newtonMap^[n] x, isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n, ?_⟩
    rw [← zero_dvd_iff, ← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
    exact aeval_pow_two_pow_dvd_aeval_iterate_newtonMap h h' n
  · -- Uniqueness
    have ⟨u, hu⟩ := binomExpansion (P.map (algebraMap R S)) r₁ (r₂ - r₁)
    suffices IsUnit (aeval r₁ (derivative P) + u * (r₂ - r₁)) by
      rwa [derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap,
        add_sub_cancel, hr₂', hr₁', zero_add, pow_two, ← mul_assoc, ← add_mul, eq_comm,
        this.mul_right_eq_zero, sub_eq_zero, eq_comm] at hu
    have : IsUnit (aeval r₁ (derivative P)) :=
      isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' hr₁
    rw [← sub_sub_sub_cancel_right r₂ r₁ x]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact (Commute.all _ _).isNilpotent_mul_left <| (Commute.all _ _).isNilpotent_sub hr₂ hr₁

end Polynomial

