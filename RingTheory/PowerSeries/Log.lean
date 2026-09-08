/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Logarithmic Power Series

This file defines the logarithmic power series `log A = ∑ (-1)^(n+1)/n · Xⁿ`
over ℚ-algebras and establishes its key properties.

## Main definitions

* `PowerSeries.log`: The power series `log(1+X) = X - X²/2 + X³/3 - ⋯`.

## Main results

* `PowerSeries.coeff_log`: The coefficient of `log A` at `n` is `(-1)^(n+1)/n` for `n ≥ 1`,
  and `0` for `n = 0`.
* `PowerSeries.constantCoeff_log`: The constant term of `log A` is `0`.
* `PowerSeries.map_log`: `log` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.coeff_one_log`: The coefficient of `log A` at `1` is `1`.
* `PowerSeries.order_log`: The order of `log A` is `1`.
* `PowerSeries.deriv_log`: The derivative of `log(1+X)` is the geometric series
  `∑ (-1)^n · Xⁿ = 1/(1+X)`.
-/

@[expose] public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Power series for `log(1 + X) = X - X²/2 + X³/3 - ⋯`. -/
/-
**PowerSeries.log** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：log : PowerSeries A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Power series for `log(1 + X) = X - X²/2 + X³/3 - ⋯`.
-/
def log : PowerSeries A :=
  mk fun n ↦ if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n)

variable {A}

@[simp]
/-
**PowerSeries.coeff_log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_log (n : Nat) : coeff n (log A) = if n = 0 then 0 else algebraMap Ra
t A ((-1 : Rat) ^ (n + 1) / n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem coeff_log (n : ℕ) :
    coeff n (log A) = if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / n) :=
  coeff_mk _ _

@[simp]
/-
**PowerSeries.constantCoeff_log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_log : constantCoeff (log A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_log`：coeff_log (n : Nat) : coeff n (log A) = if n = 0 
then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_log : constantCoeff (log A) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]
/-
**PowerSeries.map_log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_log {A' : Type*} [CommRing A'] [Algebra Rat A'] (f : A ->+* A') : map 
f (log A) = log A'
参数：f : A ->+* A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_log`：coeff_log (n : Nat) : coeff n (log A) = if n = 0 
then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `RingHom.map_rat_algebraMap`：map_rat_algebraMap [Semiring R] [Semiring S]
 [Algebra Rat R] [Algebra Rat S] (f : R ->+* S) (r : Rat) : f (algebraMap Rat R 
r) = algebraMap …
-/
theorem map_log {A' : Type*} [CommRing A'] [Algebra ℚ A'] (f : A →+* A') :
    map f (log A) = log A' := by
  ext n; simp only [coeff_map, coeff_log]; split_ifs <;> simp [RingHom.map_rat_algebraMap]
/-
**PowerSeries.coeff_one_log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_one_log : coeff 1 (log A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_log`：coeff_log (n : Nat) : coeff n (log A) = if n = 0 
then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_one_log : coeff 1 (log A) = 1 := by simp
/-
**PowerSeries.order_log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_log [Nontrivial A] : (log A).order = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_eq_nat`：order_eq_nat {φ : R⟦X⟧} {n : Nat} : order φ = 
n ↔ coeff n φ != 0 ∧ forall i, i < n -> coeff i φ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_log`：coeff_log (n : Nat) : coeff n (log A) = if n = 0 
then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem order_log [Nontrivial A] : (log A).order = 1 :=
  order_eq_nat.mpr ⟨by simp, fun i hi ↦ by simp [Nat.lt_one_iff.mp hi]⟩

/-- The derivative of `log(1+X)` is the geometric series `1 - X + X² - X³ + ⋯ = 1/(1+X)`. -/
/-
**PowerSeries.deriv_log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：deriv_log : d⁄dX A (log A) = mk fun n => algebraMap Rat A ((-1 : Rat) ^ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_derivative`：coeff_derivative (f : R⟦X⟧) (n : Nat) : co
eff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)
· 使用定理 `PowerSeries.coeff_log`：coeff_log (n : Nat) : coeff n (log A) = if n = 0 
then 0 else algebraMap Rat A ((-1 : Rat) ^ (n + 1) / n)
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n

--- 原说明 ---
The derivative of `log(1+X)` is the geometric series `1 - X + X² - X³ + ⋯ = 1/(1
+X)`.
-/
theorem deriv_log : d⁄dX A (log A) = mk fun n ↦ algebraMap ℚ A ((-1 : ℚ) ^ n) := by
  ext n
  have : (n + 1) = algebraMap ℚ A (n + 1) := by simp
  rw [coeff_derivative, coeff_log, coeff_mk]
  grind

/-! ## Substitution -/

/-
**PowerSeries.HasSubst.log** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : Algebra ℚ A], PowerSeries.H
asSubst (PowerSeries.log A)
参数：PowerSeries.log A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用定理 `PowerSeries.constantCoeff_log`：constantCoeff_log : constantCoeff (log A)
 = 0

--- 原说明 ---
## Substitution
-/
theorem HasSubst.log : HasSubst (log A) :=
  HasSubst.of_constantCoeff_zero' constantCoeff_log
/-
**PowerSeries.HasSubst.exp_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSub
st`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [inst_1 : Algebra ℚ A], PowerSeries.H
asSubst (PowerSeries.exp A - 1)
参数：PowerSeries.exp A - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `PowerSeries.constantCoeff_exp`：constantCoeff_exp : constantCoeff (exp A)
 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasSubst.exp_sub_one : HasSubst (exp A - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [constantCoeff_exp])

/-- `logOf f` is `log(1+X)` substituted at `f - 1`, i.e., `(f-1) - (f-1)²/2 + (f-1)³/3 - ⋯`. -/
/-
**PowerSeries.logOf** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：logOf (f : A⟦X⟧) : A⟦X⟧
参数：f : A⟦X⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`logOf f` is `log(1+X)` substituted at `f - 1`, i.e., `(f-1) - (f-1)²/2 + (f-1)³
/3 - ⋯`.
-/
noncomputable def logOf (f : A⟦X⟧) : A⟦X⟧ :=
  (log A).subst (f - 1)
/-
**PowerSeries.logOf_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：logOf_eq (f : A⟦X⟧) : logOf f = (log A).subst (f - 1)
参数：f : A⟦X⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem logOf_eq (f : A⟦X⟧) : logOf f = (log A).subst (f - 1) := rfl
/-
**PowerSeries.constantCoeff_logOf** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) : constantCoeff 
(logOf f) = 0
参数：hf : constantCoeff f = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.logOf_eq`：logOf_eq (f : A⟦X⟧) : logOf f = (log A).subst (f -
 1)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.constantCoeff_eq`：constantCoeff_eq (f : R⟦X⟧) : constantCoef
f f = MvPowerSeries.constantCoeff f
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `PowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (ha
 : a.constantCoeff = 0) (f : PowerSeries R) (hf : f.constantCoeff = 0) : MvPower
Series.constantCoeff (subst a…
· 使用定理 `PowerSeries.constantCoeff_log`：constantCoeff_log : constantCoeff (log A)
 = 0
-/
theorem constantCoeff_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff (logOf f) = 0 := by
  rw [logOf_eq]
  have h : MvPowerSeries.constantCoeff (f - 1 : A⟦X⟧) = 0 := by
    rw [map_sub, map_one, ← constantCoeff_eq, hf, sub_self]
  exact constantCoeff_subst_eq_zero h _ constantCoeff_log

variable (A) in
@[simp]
/-
**PowerSeries.logOf_one_add_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：logOf_one_add_X : logOf (1 + X : A⟦X⟧) = log A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.logOf_eq`：logOf_eq (f : A⟦X⟧) : logOf f = (log A).subst (f -
 1)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `PowerSeries.X_subst`：X_subst (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f
-/
theorem logOf_one_add_X : logOf (1 + X : A⟦X⟧) = log A := by
  rw [logOf_eq, add_sub_cancel_left, X_subst]

end PowerSeries

end

