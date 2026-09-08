/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Wenrong Zou
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings and
is patterned after `Mathlib/Algebra/MvPolynomial/Equiv.lean`.

* `MvPowerSeries.isEmptyEquiv` : The isomorphism between multivariable power series
  in no variables and the ground ring.

* `MvPowerSeries.optionEquivLeft` : The isomorphism between multivariable power series
  in `Option σ` and power series with coefficients in `MvPowerSeries σ R`.

* `MvPowerSeries.finSuccEquiv` : The isomorphism between multivariable power series
  in `Fin (n + 1)` and power series over multivariable power series in `Fin n`.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials
  with respect to the ideal spanned by all variables when the index is finite.

-/

@[expose] public section

noncomputable section

open Finsupp Finset Function

namespace MvPowerSeries

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

section isEmptyEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in no variables and the ground ring. -/
@[simps!]
/-
**MvPowerSeries.isEmptyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：isEmptyEquiv [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between multivariable power series in no variables and the groun
d ring.
-/
def isEmptyEquiv [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R where
  __ := constantCoeff
  invFun := C
  left_inv _ := by ext x; simp [Subsingleton.eq_zero x]
  commutes' _ := rfl

end isEmptyEquiv

section optionEquivLeft

variable (R σ) in
/-- Implementation detail for `optionEquivLeft`. Use `MvPowerSeries.optionEquivLeft` instead. -/
/-
**MvPowerSeries.optionFunLeft** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail for `optionEquivLeft`. Use `MvPowerSeries.optionEquivLeft`
 instead.
-/
private def optionFunLeft (p : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  .mk fun n ↦ fun x ↦ p.coeff (x.optionElim n)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.coeff_coeff_optionFunLeft** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeri
es`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coeff_coeff_optionFunLeft (p : MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ) :
    coeff x (PowerSeries.coeff n (optionFunLeft σ R p)) = coeff (x.optionElim n) p := by
  rw [optionFunLeft, PowerSeries.coeff_mk]
  exact LinearMap.proj_apply ..
/-
**MvPowerSeries.optionFunLeft_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem optionFunLeft_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionFunLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) := by
  classical
  ext n y
  rw [PowerSeries.coeff_monomial, coeff_coeff_optionFunLeft, coeff_monomial]
  split_ifs with h1 h2 h3
  · simp [← h1]
  · absurd h2
    rw [← optionElim_apply_none n, h1]
  · replace h1 : ¬ y = x.some := fun h ↦ by
      absurd h1; ext u
      cases u <;> simp_all
    rw [coeff_monomial, if_neg h1]
  · rw [coeff_zero]
/-
**MvPowerSeries.optionFunLeft_mul** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma optionFunLeft_mul (p q : MvPowerSeries (Option σ) R) :
    optionFunLeft σ R (p * q) = optionFunLeft σ R p * optionFunLeft σ R q := by
  classical
  ext k x
  simp only [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, map_sum, sum_sigma']
  refine sum_bij (fun y _ ↦ ⟨(y.1 none, y.2 none), (y.1.some, y.2.some)⟩) ?_ ?_ ?_ ?_
  · intros; simp_all [Finsupp.ext_iff]
  · intros; ext t <;> cases t
    all_goals simp_all [Finsupp.ext_iff]
  · rintro ⟨⟨m, n⟩, ⟨u, v⟩⟩ h
    suffices ∃ a b, (a none = m ∧ b none = n) ∧ a.some = u ∧ a + b = optionElim k x ∧
      b.some = v by simpa
    use u.optionElim m, v.optionElim n
    suffices optionElim m u + optionElim n v = optionElim k x by simp_all
    ext t; cases t <;> simp_all [Finsupp.ext_iff]
  · intros; simp_all [Finsupp.ext_iff]

variable (R σ) in
/-- An inverse function of `optionFunLeft`. -/
/-
**MvPowerSeries.optionInvFunLeft** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inverse function of `optionFunLeft`.
-/
private def optionInvFunLeft (p : PowerSeries (MvPowerSeries σ R)) :
    MvPowerSeries (Option σ) R := fun x ↦ (p.coeff (x none)).coeff x.some
/-
**MvPowerSeries.coeff_optionInvFunLeft** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coeff_optionInvFunLeft (p : PowerSeries (MvPowerSeries σ R)) (x : Option σ →₀ ℕ) :
    coeff x (optionInvFunLeft σ R p) = (p.coeff (x none)).coeff x.some := rfl

variable (R σ) in
/-- The algebra isomorphism between multivariable power series in `Option σ` and
  power series with coefficients in `MvPowerSeries σ R`. -/
@[no_expose]
/-
**MvPowerSeries.optionEquivLeft** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：optionEquivLeft : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSer
ies σ R) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Equiv.0.MvPowerSeries.optionFu
nLeft_mul`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (p q : MvPowe
rSeries (Option σ) R),   MvPowerSeries.optionFunLeft✝ σ R (p * q) = MvP…

--- 原说明 ---
The algebra isomorphism between multivariable power series in `Option σ` and
  power series with coefficients in `MvPowerSeries σ R`.
-/
def optionEquivLeft : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSeries σ R) where
  toFun := optionFunLeft σ R
  invFun := optionInvFunLeft σ R
  left_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  right_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  map_mul' := optionFunLeft_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunLeft]
  commutes' := by
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.C] using
      optionFunLeft_monomial (0 : Option σ →₀ ℕ)
/-
**MvPowerSeries.coeff_coeff_optionEquivLeft** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：coeff_coeff_optionEquivLeft (p : MvPowerSeries (Option σ) R) (n : Nat) (x 
: σ ->₀ Nat) : coeff x (PowerSeries.coeff n (optionEquivLeft σ R p)) = coeff (x.
optionElim n) p
参数：p : MvPowerSeries (Option σ) R；n : Nat；x : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Equiv.0.MvPowerSeries.coeff_co
eff_optionFunLeft`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (p : 
MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ),   (MvPowerSeries.coeff x) ((P…
-/
lemma coeff_coeff_optionEquivLeft (p : MvPowerSeries (Option σ) R) (n : ℕ) (x : σ →₀ ℕ) :
    coeff x (PowerSeries.coeff n (optionEquivLeft σ R p)) = coeff (x.optionElim n) p :=
  coeff_coeff_optionFunLeft ..
/-
**MvPowerSeries.optionEquivLeft_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：optionEquivLeft_monomial (x : Option σ ->₀ Nat) (r : R) : optionEquivLeft 
σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r)
参数：x : Option σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Equiv.0.MvPowerSeries.optionFu
nLeft_monomial`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (x : Opt
ion σ →₀ ℕ) (r : R),   MvPowerSeries.optionFunLeft✝ σ R ((MvPowerSeries.mono…
-/
theorem optionEquivLeft_monomial (x : Option σ →₀ ℕ) (r : R) :
    optionEquivLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) :=
  optionFunLeft_monomial ..

@[simp]
/-
**MvPowerSeries.optionEquivLeft_X_some** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`
。
形式化陈述：optionEquivLeft_X_some (i : σ) : optionEquivLeft σ R (X (Option.some i)) =
 (PowerSeries.C (X i))
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.some_single_some`：some_single_some (a : α) (m : M) : (single (Op
tion.some a) m : Option α ->₀ M).some = single a m
· 使用引理 `PowerSeries.monomial_eq_C_mul_X_pow`：monomial_eq_C_mul_X_pow (r : R) (n 
: Nat) : monomial n r = C r * X ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPowerSeries.optionEquivLeft_monomial`：optionEquivLeft_monomial (x : Op
tion σ ->₀ Nat) (r : R) : optionEquivLeft σ R (monomial x r) = PowerSeries.monom
ial (x none) (monomial x.som…
-/
lemma optionEquivLeft_X_some (i : σ) :
    optionEquivLeft σ R (X (Option.some i)) = (PowerSeries.C (X i)) := by
  have : (optionElim 0 (single i 1)) = single (Option.some i) 1 := by
    classical
    ext a; cases a <;> simp [single_apply]
  simpa [← X_def, PowerSeries.monomial_eq_C_mul_X_pow, this] using
    optionEquivLeft_monomial (single (Option.some i) 1 : Option σ →₀ ℕ) (1 : R)

@[simp]
/-
**MvPowerSeries.optionEquivLeft_X_none** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`
。
形式化陈述：optionEquivLeft_X_none : optionEquivLeft σ R (X none) = PowerSeries.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.some_single_none`：some_single_none (m : M) : (single none m : Op
tion α ->₀ M).some = 0
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
· 使用引理 `PowerSeries.monomial_eq_C_mul_X_pow`：monomial_eq_C_mul_X_pow (r : R) (n 
: Nat) : monomial n r = C r * X ^ n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MvPowerSeries.optionEquivLeft_monomial`：optionEquivLeft_monomial (x : Op
tion σ ->₀ Nat) (r : R) : optionEquivLeft σ R (monomial x r) = PowerSeries.monom
ial (x none) (monomial x.som…
-/
lemma optionEquivLeft_X_none : optionEquivLeft σ R (X none) = PowerSeries.X := by
  simpa [PowerSeries.monomial_eq_C_mul_X_pow, ← X_def] using
    optionEquivLeft_monomial (single none 1 : Option σ →₀ ℕ) (1 : R)

@[simp]
/-
**MvPowerSeries.optionEquivLeft_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：optionEquivLeft_C (r : R) : (optionEquivLeft σ R) (C r) = PowerSeries.C (C
 r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.some_zero`：some_zero : (0 : Option α ->₀ M).some = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.monomial_zero_eq_C`：monomial_zero_eq_C : ⇑(monomial (R
· 使用定理 `MvPowerSeries.optionEquivLeft_monomial`：optionEquivLeft_monomial (x : Op
tion σ ->₀ Nat) (r : R) : optionEquivLeft σ R (monomial x r) = PowerSeries.monom
ial (x none) (monomial x.som…
-/
lemma optionEquivLeft_C (r : R) : (optionEquivLeft σ R) (C r) = PowerSeries.C (C r) := by
  simpa using optionEquivLeft_monomial (0 : Option σ →₀ ℕ) (r : R)

end optionEquivLeft

section finSuccEquiv

variable {n : ℕ}

/-
**MvPowerSeries.embDomain_finSuccEquiv_cons** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSe
ries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma embDomain_finSuccEquiv_cons {M : Type*} [AddCommMonoid M] {n : ℕ} (i : M)
    (x : Fin n →₀ M) : embDomain (finSuccEquiv n).toEmbedding (cons i x) = optionElim i x := by
  ext a; cases a <;> simp [embDomain_eq_mapDomain]

variable (n R) in
/-- The algebra isomorphism between multivariable power series in `Fin (n + 1)` and
power series over multivariable power series in `Fin n`. -/
/-
**MvPowerSeries.finSuccEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：finSuccEquiv : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSer
ies (Fin n) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism between multivariable power series in `Fin (n + 1)` and
power series over multivariable power series in `Fin n`.
-/
def finSuccEquiv : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft (Fin n) R)
/-
**MvPowerSeries.coeff_coeff_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：coeff_coeff_finSuccEquiv (p : MvPowerSeries (Fin (n + 1)) R) {k : Nat} {x 
: Fin n ->₀ Nat} : coeff x (PowerSeries.coeff k (finSuccEquiv R n p)) = coeff (x
.cons k) p
参数：p : MvPowerSeries (Fin (n + 1)) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.TendstoCofinite.equiv`：equiv (e : α ≃ β) : TendstoCofinite e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.coeff_coeff_optionEquivLeft`：coeff_coeff_optionEquivLeft (
p : MvPowerSeries (Option σ) R) (n : Nat) (x : σ ->₀ Nat) : coeff x (PowerSeries
.coeff n (optionEquivLeft σ R p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_embDomain_rename`：coeff_embDomain_rename (e : σ ↪ τ)
 (p : MvPowerSeries σ R) (x : σ ->₀ Nat) : coeff (embDomain e x) (rename e p) = 
p.coeff x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPowerSeries.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Ty
pe u_4) [inst : CommSemiring R] (e : σ ≃ τ) (a : MvPowerSeries σ R),   (MvPowerS
eries.renameEquiv R e…
-/
theorem coeff_coeff_finSuccEquiv (p : MvPowerSeries (Fin (n + 1)) R) {k : ℕ} {x : Fin n →₀ ℕ} :
    coeff x (PowerSeries.coeff k (finSuccEquiv R n p)) = coeff (x.cons k) p := by
  suffices coeff x (PowerSeries.coeff k (optionEquivLeft (Fin n) R
    (rename (_root_.finSuccEquiv n) p))) = coeff (Finsupp.cons k x) p by simpa [finSuccEquiv]
  simp_rw [← Equiv.coe_toEmbedding, coeff_coeff_optionEquivLeft, ← embDomain_finSuccEquiv_cons,
    coeff_embDomain_rename]

@[simp]
/-
**MvPowerSeries.finSuccEquiv_X_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = .X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_coeff_finSuccEquiv`：coeff_coeff_finSuccEquiv (p : Mv
PowerSeries (Fin (n + 1)) R) {k : Nat} {x : Fin n ->₀ Nat} : coeff x (PowerSerie
s.coeff k (finSuccEquiv R n …
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPowerSeries.coeff_one`：coeff_one [DecidableEq σ] : coeff n (1 : MvPowe
rSeries σ R) = if n = 0 then 1 else 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `MvPowerSeries.coeff_zero`：coeff_zero (n : σ ->₀ Nat) : coeff n (0 : MvPo
werSeries σ R) = 0
-/
theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = .X := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_X, coeff_X, cons_eq_single_zero_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_one, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]
/-
**MvPowerSeries.finSuccEquiv_X_succ** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：finSuccEquiv_X_succ (j : Fin n) : finSuccEquiv R n (X j.succ) = .C (X j)
参数：j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_coeff_finSuccEquiv`：coeff_coeff_finSuccEquiv (p : Mv
PowerSeries (Fin (n + 1)) R) {k : Nat} {x : Fin n ->₀ Nat} : coeff x (PowerSerie
s.coeff k (finSuccEquiv R n …
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MvPowerSeries.coeff_index_single_self_X`：coeff_index_single_self_X (s : 
σ) : coeff (single s 1) (X s : MvPowerSeries σ R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `MvPowerSeries.coeff_zero`：coeff_zero (n : σ ->₀ Nat) : coeff n (0 : MvPo
werSeries σ R) = 0
-/
theorem finSuccEquiv_X_succ (j : Fin n) : finSuccEquiv R n (X j.succ) = .C (X j) := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_X, cons_eq_single_succ_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_X, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]
/-
**MvPowerSeries.finSuccEquiv_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：finSuccEquiv_C (r : R) : (finSuccEquiv R n) (C r) = PowerSeries.C (C r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_coeff_finSuccEquiv`：coeff_coeff_finSuccEquiv (p : Mv
PowerSeries (Fin (n + 1)) R) {k : Nat} {x : Fin n ->₀ Nat} : coeff x (PowerSerie
s.coeff k (finSuccEquiv R n …
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `MvPowerSeries.coeff_C`：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
 coeff n (C a) = if n = 0 then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `Finsupp.cons_injective2`：cons_injective2 : Function.Injective2 (cons (n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `MvPowerSeries.coeff_zero`：coeff_zero (n : σ ->₀ Nat) : coeff n (0 : MvPo
werSeries σ R) = 0
-/
theorem finSuccEquiv_C (r : R) : (finSuccEquiv R n) (C r) = PowerSeries.C (C r) := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_C, ← cons_zero_zero,
    cons_injective2.eq_iff]
  split_ifs with h1 h2 h3
  · simp [h1.right]
  · tauto
  · rw [coeff_C, if_neg (by tauto)]
  · rw [coeff_zero]
/-
**MvPowerSeries.finSuccEquiv_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：finSuccEquiv_comp_C : (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
 (PowerSeries.C.comp MvPowerSeries.C) = MvPowerSeries.C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.finSuccEquiv_C`：finSuccEquiv_C (r : R) : (finSuccEquiv R n
) (C r) = PowerSeries.C (C r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv_comp_C : (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
    (PowerSeries.C.comp MvPowerSeries.C) = MvPowerSeries.C := by
  ext1; simp [AlgEquiv.symm_apply_eq]

variable (S : Type*) [CommRing S] [IsNoetherianRing S]
/-
**MvPowerSeries.isNoetherianRing_fin** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isNoetherianRing_fin (n : ℕ) : IsNoetherianRing (MvPowerSeries (Fin n) S) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv S (isEmptyEquiv (Fin 0) S).toRingEquiv.symm
  | succ n _ =>
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) S))
      (finSuccEquiv S n).toRingEquiv.symm
/-
**MvPowerSeries.isNoetherianRing** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
形式化陈述：isNoetherianRing [Finite σ] : IsNoetherianRing (MvPowerSeries σ S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Equiv.0.MvPowerSeries.isNoethe
rianRing_fin`：∀ (S : Type u_3) [inst : CommRing S] [IsNoetherianRing S] (n : ℕ),
 IsNoetherianRing (MvPowerSeries (Fin n) S)
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
-/
instance isNoetherianRing [Finite σ] : IsNoetherianRing (MvPowerSeries σ S) := by
  cases nonempty_fintype σ
  have := isNoetherianRing_fin S (Fintype.card σ)
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin (Fintype.card σ)) S)
    (renameEquiv S (Fintype.equivFin σ)).toRingEquiv.symm

end finSuccEquiv

end CommSemiring

section toAdicCompletion

open Finsupp

variable {σ R : Type*} {n : ℕ} [CommRing R] [Finite σ]

/-
**MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars** 是 Mathlib 中的一个引理
，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_sub_truncTotal_mem_pow_idealOfVars {l m n : Nat} (h : l <= m) (
h' : l <= n) (p : MvPowerSeries σ R) : p.truncTotal m - p.truncTotal n in MvPoly
nomial.idealOfVars σ R ^ l
参数：h : l <= m；h' : l <= n；p : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.mem_pow_idealOfVars_iff'`：mem_pow_idealOfVars_iff' (n : Nat
) (p : MvPolynomial σ R) : p in idealOfVars σ R ^ n ↔ forall x, degree x < n -> 
p.coeff x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
-/
lemma truncTotal_sub_truncTotal_mem_pow_idealOfVars {l m n : ℕ} (h : l ≤ m) (h' : l ≤ n)
    (p : MvPowerSeries σ R) : p.truncTotal m - p.truncTotal n ∈
      MvPolynomial.idealOfVars σ R ^ l := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ (by lia),
    coeff_truncTotal _ (by lia)]
/-
**MvPowerSeries.truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars** 是 Mathli
b 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (p q : MvPowerSeries
 σ R) : (p * q).truncTotal n - p.truncTotal n * q.truncTotal n in MvPolynomial.i
dealOfVars σ R ^ n
参数：p q : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.mem_pow_idealOfVars_iff'`：mem_pow_idealOfVars_iff' (n : Nat
) (p : MvPolynomial σ R) : p in idealOfVars σ R ^ n ↔ forall x, degree x < n -> 
p.coeff x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用引理 `MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul`：coeff_truncT
otal_mul_truncTotal_eq_coeff_mul (hx : degree x < n) : MvPolynomial.coeff x (p.t
runcTotal n * q.truncTotal n) = (coeff x) (p * q…
-/
lemma truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (p q : MvPowerSeries σ R) :
    (p * q).truncTotal n - p.truncTotal n * q.truncTotal n ∈
      MvPolynomial.idealOfVars σ R ^ n := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx,
    coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

/-- The canonical map induced by `truncTotal` from multivariate power series to
the quotient ring of multivariate polynomials by the `n`-th power of
the ideal spanned by all variables. -/
@[simps]
/-
**MvPowerSeries.truncTotalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：truncTotalAlgHom (σ R : Type*) [Finite σ] [CommRing R] (n : Nat) : MvPower
Series σ R ->ₐ[MvPolynomial σ R] MvPolynomial σ R ⧸ (MvPolynomial.idealOfVars σ 
R) ^ n where toFun p
参数：σ R : Type*；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map induced by `truncTotal` from multivariate power series to
the quotient ring of multivariate polynomials by the `n`-th power of
the ideal spanned by all variables.
-/
def truncTotalAlgHom (σ R : Type*) [Finite σ] [CommRing R] (n : ℕ) :
    MvPowerSeries σ R →ₐ[MvPolynomial σ R]
      MvPolynomial σ R ⧸ (MvPolynomial.idealOfVars σ R) ^ n where
  toFun p := truncTotal n p
  map_one' := by
    by_cases! h : n = 0
    · have := Ideal.Quotient.subsingleton_iff.mpr
        (show MvPolynomial.idealOfVars σ R ^ n = ⊤ by simp [h])
      exact Subsingleton.allEq ..
    rw [truncTotal_one h, map_one]
  map_mul' p q := by
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars p q
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by simp
  commutes' p := by
    change (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) (truncTotal n p) =
      (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) p
    rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
    intro x h
    rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ h, MvPolynomial.coeff_coe]

/-- The canonical map from multivariate power series to the adic completion of
multivariate polynomials with respect to the ideal spanned by all variables
when the index is finite. -/
/-
**MvPowerSeries.toAdicCompletion** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：toAdicCompletion (σ R : Type*) [Finite σ] [CommRing R] : MvPowerSeries σ R
 ->ₐ[MvPolynomial σ R] AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomi
al σ R)
参数：σ R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from multivariate power series to the adic completion of
multivariate polynomials with respect to the ideal spanned by all variables
when the index is finite.
-/
def toAdicCompletion (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R →ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) :=
  AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars σ R) (truncTotalAlgHom σ R)
    (fun h ↦ AlgHom.ext fun _ ↦ by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
        truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _)
/-
**MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal** 是 Mathlib 中的一个引理，位于命名空
间 `MvPowerSeries`。
形式化陈述：toAdicCompletion_apply_eq_mk_truncTotal {n : Nat} {p : MvPowerSeries σ R} 
: (toAdicCompletion σ R p).val n = truncTotal n p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAdicCompletion_apply_eq_mk_truncTotal {n : ℕ} {p : MvPowerSeries σ R} :
    (toAdicCompletion σ R p).val n = truncTotal n p := by rfl
/-
**MvPowerSeries.coeff_toAdicCompletion_val_apply_out** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：coeff_toAdicCompletion_val_apply_out {x : σ ->₀ Nat} {p : MvPowerSeries σ 
R} {n : Nat} (hx : degree x < n) : (Quotient.out (((toAdicCompletion σ R) p).val
 n)).coeff x = (coeff x) p
参数：hx : degree x < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.mem_pow_idealOfVars_iff'`：mem_pow_idealOfVars_iff' (n : Nat
) (p : MvPolynomial σ R) : p in idealOfVars σ R ^ n ↔ forall x, degree x < n -> 
p.coeff x = 0
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal`：toAdicCompletion_
apply_eq_mk_truncTotal {n : Nat} {p : MvPowerSeries σ R} : (toAdicCompletion σ R
 p).val n = truncTotal n p
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Ideal.Quotient.mk_out`：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotien
t.out x) = x
-/
theorem coeff_toAdicCompletion_val_apply_out {x : σ →₀ ℕ} {p : MvPowerSeries σ R} {n : ℕ}
    (hx : degree x < n) : (Quotient.out (((toAdicCompletion σ R) p).val n)).coeff x =
      (coeff x) p := by
  rw [← coeff_truncTotal _ hx, ← sub_eq_zero, ← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
  · rw [toAdicCompletion_apply_eq_mk_truncTotal, smul_eq_mul]
    nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ n), ← Ideal.Quotient.eq,
      Ideal.Quotient.mk_out]
  exact hx

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.toAdicCompletion_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：toAdicCompletion_coe (p : MvPolynomial σ R) : toAdicCompletion σ R p = .of
 (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) p
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_pow_idealOfVars_iff'`：mem_pow_idealOfVars_iff' (n : Nat
) (p : MvPolynomial σ R) : p in idealOfVars σ R ^ n ↔ forall x, degree x < n -> 
p.coeff x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.truncTotalAlgHom_apply`：∀ (σ : Type u_3) (R : Type u_4) [i
nst : Finite σ] [inst_1 : CommRing R] (n : ℕ) (p : MvPowerSeries σ R),   (MvPowe
rSeries.truncTotalAlgHom σ…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
-/
theorem toAdicCompletion_coe (p : MvPolynomial σ R) :
    toAdicCompletion σ R p = .of (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) p := by
  symm; ext n
  suffices p - (truncTotal n) p ∈ MvPolynomial.idealOfVars σ R ^ n by
    simpa [toAdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr fun x hx ↦ by simp [coeff_truncTotal _ hx]

/-- An inverse function of `toAdicCompletion`. -/
/-
**MvPowerSeries.toAdicCompletionInv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：toAdicCompletionInv (σ R : Type*) [CommRing R] (f : AdicCompletion (MvPoly
nomial.idealOfVars σ R) (MvPolynomial σ R)) : MvPowerSeries σ R
参数：σ R : Type*；f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ
 R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inverse function of `toAdicCompletion`.
-/
def toAdicCompletionInv (σ R : Type*) [CommRing R]
    (f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      MvPowerSeries σ R := fun x ↦ (f.val (degree x + 1)).out.coeff x

omit [Finite σ] in
/-
**MvPowerSeries.coeff_toAdicCompletionInv** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：coeff_toAdicCompletionInv {x : σ ->₀ Nat} {f : AdicCompletion (MvPolynomia
l.idealOfVars σ R) (MvPolynomial σ R)} : coeff x (toAdicCompletionInv σ R f) = (
f.val (degree x + 1)).out.coeff x
参数：MvPolynomial.idealOfVars σ R；MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_toAdicCompletionInv {x : σ →₀ ℕ}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      coeff x (toAdicCompletionInv σ R f) = (f.val (degree x + 1)).out.coeff x := by rfl
/-
**MvPowerSeries.mk_truncTotal_toAdicCompletionInv** 是 Mathlib 中的一个定理，位于命名空间 `MvP
owerSeries`。
形式化陈述：mk_truncTotal_toAdicCompletionInv {n : Nat} {f : AdicCompletion (MvPolynom
ial.idealOfVars σ R) (MvPolynomial σ R)} : Ideal.Quotient.mk (MvPolynomial.ideal
OfVars σ R ^ n • ⊤) ((truncTotal n) (toAdicCompletionInv σ R f)) = f.val n
参数：MvPolynomial.idealOfVars σ R；MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.mk_out`：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotien
t.out x) = x
· 使用定理 `Ideal.Quotient.mk_eq_mk_iff_sub_mem`：mk_eq_mk_iff_sub_mem (x y : R) : mk
 I x = mk I y ↔ x - y in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPowerSeries.coeff_truncTotal`：coeff_truncTotal (h : degree x < n) : (t
runcTotal n p).coeff x = p.coeff x
· 使用引理 `MvPowerSeries.coeff_toAdicCompletionInv`：coeff_toAdicCompletionInv {x : 
σ ->₀ Nat} {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)
} : coeff x (toAdicCompletion…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.mem_pow_idealOfVars_iff'`：mem_pow_idealOfVars_iff' (n : Nat
) (p : MvPolynomial σ R) : p in idealOfVars σ R ^ n ↔ forall x, degree x < n -> 
p.coeff x = 0
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `AdicCompletion.transitionMap_ideal_mk`：transitionMap_ideal_mk {m n : Nat
} (hmn : m <= n) (x : R) : transitionMap I R hmn (Ideal.Quotient.mk (I ^ n • ⊤ :
 Ideal R) x) = Ideal.Quotie…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 31 条，此处仅展示前 30 条）
-/
theorem mk_truncTotal_toAdicCompletionInv {n : ℕ}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n • ⊤)
    ((truncTotal n) (toAdicCompletionInv σ R f)) = f.val n := by
  rw [← Ideal.Quotient.mk_out (f.val n), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, MvPolynomial.mem_pow_idealOfVars_iff',
    MvPolynomial.coeff_sub]
  intro x h
  rw [coeff_truncTotal _ h, coeff_toAdicCompletionInv, ← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (degree x + 1) _).mp
  · nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ (degree x + 1)),
      ← smul_eq_mul, ← Ideal.Quotient.eq]
    simp only [Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.mk_out]
    rw [← AdicCompletion.transitionMap_ideal_mk _ (Nat.lt_iff_add_one_le.mp h), eq_comm]
    convert! f.prop h; simp
  simp

/-- The isomorphism from multivariate power series to the adic completion of
multivariate polynomials with respect to the ideal spanned by all variables
when the index is finite. -/
/-
**MvPowerSeries.toAdicCompletionAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSerie
s`。
形式化陈述：toAdicCompletionAlgEquiv (σ R : Type*) [Finite σ] [CommRing R] : MvPowerSe
ries σ R ≃ₐ[MvPolynomial σ R] AdicCompletion (MvPolynomial.idealOfVars σ R) (MvP
olynomial σ R) where __
参数：σ R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from multivariate power series to the adic completion of
multivariate polynomials with respect to the ideal spanned by all variables
when the index is finite.
-/
def toAdicCompletionAlgEquiv (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R ≃ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) where
  __ := toAdicCompletion σ R
  invFun := toAdicCompletionInv σ R
  left_inv _ := by
    ext; simp [coeff_toAdicCompletionInv, coeff_toAdicCompletion_val_apply_out]
  right_inv _ := by ext; simpa using! mk_truncTotal_toAdicCompletionInv

@[simp]
/-
**MvPowerSeries.toAdicCompletionAlgEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPowe
rSeries`。
形式化陈述：toAdicCompletionAlgEquiv_apply (p : MvPowerSeries σ R) : toAdicCompletionA
lgEquiv σ R p = toAdicCompletion σ R p
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAdicCompletionAlgEquiv_apply (p : MvPowerSeries σ R) :
    toAdicCompletionAlgEquiv σ R p = toAdicCompletion σ R p := by rfl

@[simp]
/-
**MvPowerSeries.toAdicCompletionAlgEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `M
vPowerSeries`。
形式化陈述：toAdicCompletionAlgEquiv_symm_apply (x : AdicCompletion (MvPolynomial.idea
lOfVars σ R) (MvPolynomial σ R)) : (toAdicCompletionAlgEquiv σ R).symm x = toAdi
cCompletionInv σ R x
参数：x : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAdicCompletionAlgEquiv_symm_apply
    (x : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      (toAdicCompletionAlgEquiv σ R).symm x = toAdicCompletionInv σ R x := by
  rfl

end toAdicCompletion

end MvPowerSeries

section toMvPowerSeries

variable {R σ τ : Type*} [CommSemiring R] {f : PowerSeries R} (i : σ) (r : R)

open PowerSeries Filter
namespace PowerSeries

/-- Given a power series `p : R⟦X⟧` and an index `i`, we may view it as a
multivariate power series `toMvPowerSeries i p : MvPowerSeries σ R`. -/
noncomputable
/-
**PowerSeries.toMvPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries : PowerSeries R ->ₐ[R] MvPowerSeries σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toMvPowerSeries : PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  MvPowerSeries.rename (fun _ ↦ i)
/-
**PowerSeries.toMvPowerSeries_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries_apply : f.toMvPowerSeries i = f.rename (fun _ => i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMvPowerSeries_apply : f.toMvPowerSeries i = f.rename (fun _ ↦ i) := rfl

@[simp]
/-
**PowerSeries.toMvPowerSeries_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.tendstoCofinite_of_finite`：tendstoCofinite_of_finite [Finite α] :
 TendstoCofinite f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.toMvPowerSeries_apply`：toMvPowerSeries_apply : f.toMvPowerSe
ries i = f.rename (fun _ => i)
· 使用引理 `PowerSeries.C_apply`：C_apply {r : R} : C r = MvPowerSeries.C r
· 使用定理 `MvPowerSeries.rename_C`：rename_C (r : R) : rename f (C r : MvPowerSeries
 σ R) = C r
-/
theorem toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r := by
  rw [toMvPowerSeries_apply, C_apply, MvPowerSeries.rename_C]

@[simp]
/-
**PowerSeries.toMvPowerSeries_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.tendstoCofinite_of_finite`：tendstoCofinite_of_finite [Finite α] :
 TendstoCofinite f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.toMvPowerSeries_apply`：toMvPowerSeries_apply : f.toMvPowerSe
ries i = f.rename (fun _ => i)
· 使用引理 `PowerSeries.X_apply`：X_apply : X (R
· 使用定理 `MvPowerSeries.rename_X`：rename_X (i : σ) : rename f (X i : MvPowerSeries
 σ R) = X (f i)
-/
theorem toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R := R) := by
  rw [toMvPowerSeries_apply, X_apply, MvPowerSeries.rename_X]
/-
**PowerSeries.toMvPowerSeries_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries_injective (i : σ) : Function.Injective (toMvPowerSeries (R
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.rename_injective`：rename_injective (e : σ ↪ τ) : Function.
Injective (rename (R
-/
theorem toMvPowerSeries_injective (i : σ) : Function.Injective (toMvPowerSeries (R := R) i) :=
  MvPowerSeries.rename_injective (Embedding.punit i)
/-
**PowerSeries.toMvPowerSeries_inj** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries_inj (i : σ) {p q : R⟦X⟧} : p.toMvPowerSeries i = q.toMvPow
erSeries i ↔ p = q
参数：i : σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PowerSeries.toMvPowerSeries_injective`：toMvPowerSeries_injective (i : σ)
 : Function.Injective (toMvPowerSeries (R
-/
theorem toMvPowerSeries_inj (i : σ) {p q : R⟦X⟧} :
    p.toMvPowerSeries i = q.toMvPowerSeries i ↔ p = q :=
  (toMvPowerSeries_injective i).eq_iff

section CommRing

variable {R : Type*} [CommRing R] {f : R⟦X⟧} {i : σ}

/-
**PowerSeries.toMvPowerSeries_eq_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (MvPowerSeries.X 
i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.tendstoCofinite_of_finite`：tendstoCofinite_of_finite [Finite α] :
 TendstoCofinite f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.toMvPowerSeries_apply`：toMvPowerSeries_apply : f.toMvPowerSe
ries i = f.rename (fun _ => i)
· 使用定理 `MvPowerSeries.rename_eq_subst`：rename_eq_subst : rename f p = p.subst (X
 ∘ f)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
-/
theorem toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, comp_def, subst]
/-
**PowerSeries.subst_toMvPowerSeries** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_toMvPowerSeries {a : σ -> MvPowerSeries τ R} (ha : MvPowerSeries.Has
Subst a) : (f.toMvPowerSeries i).subst a = f.subst (a i)
参数：ha : MvPowerSeries.HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.toMvPowerSeries_eq_subst`：toMvPowerSeries_eq_subst : f.toMvP
owerSeries i = f.subst (MvPowerSeries.X i)
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `PowerSeries.HasSubst.X`：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing
 S] (t : τ), PowerSeries.HasSubst (MvPowerSeries.X t)
· 使用定理 `MvPowerSeries.subst_X`：subst_X (ha : HasSubst a) (s : σ) : subst (R
-/
theorem subst_toMvPowerSeries {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  rw [toMvPowerSeries_eq_subst, subst, MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha, MvPowerSeries.subst_X ha, subst]
/-
**PowerSeries.toMvPowerSeries_coeff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeri
es`。
形式化陈述：toMvPowerSeries_coeff_eq_zero {d : σ ->₀ Nat} (hd : d i = 0) (hf : f.const
antCoeff = 0) : (f.toMvPowerSeries i).coeff d = 0
参数：hd : d i = 0；hf : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.tendstoCofinite_of_finite`：tendstoCofinite_of_finite [Finite α] :
 TendstoCofinite f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.toMvPowerSeries_apply`：toMvPowerSeries_apply : f.toMvPowerSe
ries i = f.rename (fun _ => i)
· 使用定理 `MvPowerSeries.rename_eq_subst`：rename_eq_subst : rename f p = p.subst (X
 ∘ f)
· 使用引理 `PowerSeries.subst_X_comp_const`：subst_X_comp_const {f : R⟦X⟧} {i : τ} : 
.subst (.X (R
· 使用定理 `PowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : PowerSeries 
R) (e : τ ->₀ Nat) : MvPowerSeries.coeff e (subst a f) = finsum (fun (d : Nat) =
> coeff d f •…
· 使用定理 `PowerSeries.HasSubst.X`：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing
 S] (t : τ), PowerSeries.HasSubst (MvPowerSeries.X t)
· 使用定理 `finsum_eq_zero_of_forall_eq_zero`：∀ {α : Type u_1} {M : Type u_5} [inst 
: AddCommMonoid M] {f : α → M}, (∀ (x : α), f x = 0) → ∑ᶠ (i : α), f i = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.X_pow_eq`：X_pow_eq (s : σ) (n : Nat) : (X s : MvPowerSerie
s σ R) ^ n = monomial (single s n) 1
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toMvPowerSeries_coeff_eq_zero {d : σ →₀ ℕ} (hd : d i = 0) (hf : f.constantCoeff = 0) :
    (f.toMvPowerSeries i).coeff d = 0 := by classical
  rw [toMvPowerSeries_apply, MvPowerSeries.rename_eq_subst, subst_X_comp_const,
    coeff_subst (HasSubst.X _), finsum_eq_zero_of_forall_eq_zero]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_eq_right_iff]
  intro _ a
  subst a
  simp_all
/-
**PowerSeries._root_.MvPowerSeries.HasSubst.toMvPowerSeries** 是 Mathlib 中的一个定理，位
于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MvPowerSeries.HasSubst.toMvPowerSeries (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) where
  const_coeff := by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype d.support) fun s => by
    contrapose
    simpa using fun hd ↦ toMvPowerSeries_coeff_eq_zero hd hf

end CommRing

end PowerSeries

variable (f : σ → τ) [TendstoCofinite f] (a : σ) (p : R⟦X⟧)

@[simp]
/-
**MvPowerSeries.rename_comp_toMvPowerSeries** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPowerSeries.rename_comp_toMvPowerSeries : (rename (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Filter.tendstoCofinite_of_finite`：tendstoCofinite_of_finite [Finite α] :
 TendstoCofinite f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Filter.TendstoCofinite.comp`：comp [TendstoCofinite g] [TendstoCofinite f
] : TendstoCofinite (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.rename_rename`：rename_rename [TendstoCofinite g] (p : MvPo
werSeries σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MvPowerSeries.rename_comp_toMvPowerSeries :
    (rename (R := R) f).comp (PowerSeries.toMvPowerSeries a) =
      PowerSeries.toMvPowerSeries (f a) := by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]
/-
**MvPowerSeries.rename_toMvPowerSeries** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MvPowerSeries.rename_toMvPowerSeries : (p.toMvPowerSeries a).rename f = p.
toMvPowerSeries (f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `MvPowerSeries.rename_comp_toMvPowerSeries`：MvPowerSeries.rename_comp_toM
vPowerSeries : (rename (R
-/
lemma MvPowerSeries.rename_toMvPowerSeries :
    (p.toMvPowerSeries a).rename f = p.toMvPowerSeries (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

end toMvPowerSeries

