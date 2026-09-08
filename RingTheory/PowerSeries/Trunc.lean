/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic

/-!

# Formal power series in one variable - Truncation

`PowerSeries.trunc n φ` truncates a (univariate) formal power series
to the polynomial that has the same coefficients as `φ`, for all `m < n`,
and `0` otherwise.

-/

@[expose] public section

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section Trunc
variable [Semiring R]
open Finset Nat

set_option backward.privateInPublic true in
/-
**PowerSeries.truncAux** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def truncAux (n : ℕ) (φ : R⟦X⟧) : R[X] :=
  ∑ m ∈ Ico 0 n, Polynomial.monomial m (coeff m φ)
/-
**PowerSeries.coeff_truncAux** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coeff_truncAux (m) (n) (φ : R⟦X⟧) :
    (truncAux n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [truncAux, Polynomial.coeff_monomial]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The `n`th truncation of a formal power series to a polynomial. -/
/-
**PowerSeries.trunc** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：trunc (n : Nat) : R⟦X⟧ ->ₗ[R] R[X] where toFun
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th truncation of a formal power series to a polynomial.
-/
def trunc (n : ℕ) : R⟦X⟧ →ₗ[R] R[X] where
  toFun := truncAux n
  map_add' φ ψ := Polynomial.ext fun m => by
    simp only [coeff_truncAux, Polynomial.coeff_add]
    split_ifs with H
    · rfl
    · rw [zero_add]
  map_smul' t φ := by ext; simp [truncAux, Polynomial.coeff_monomial]
/-
**PowerSeries.trunc_apply** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_apply (n : Nat) (φ : R⟦X⟧) : trunc n φ = ∑ m in Ico 0 n, Polynomial.
monomial m (coeff m φ)
参数：n : Nat；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trunc_apply (n : ℕ) (φ : R⟦X⟧) :
    trunc n φ = ∑ m ∈ Ico 0 n, Polynomial.monomial m (coeff m φ) := rfl
/-
**PowerSeries.coeff_trunc** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).coeff m = if m < n then coeff
 m φ else 0
参数：m；n；φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.PowerSeries.Trunc.0.PowerSeries.coeff_truncA
ux`：∀ {R : Type u_1} [inst : Semiring R] (m n : ℕ) (φ : PowerSeries R),   (Power
Series.truncAux✝ n φ).coeff m = if m < n then (PowerSeries.coeff…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_trunc (m) (n) (φ : R⟦X⟧) :
    (trunc n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [trunc, coeff_truncAux]

@[simp]
/-
**PowerSeries.trunc_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_one (n) : trunc (n + 1) (1 : R⟦X⟧) = 1
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
-/
theorem trunc_one (n) : trunc (n + 1) (1 : R⟦X⟧) = 1 :=
  Polynomial.ext fun m => by
    grind [PowerSeries.coeff_trunc, PowerSeries.coeff_one, Polynomial.coeff_one]

@[simp]
/-
**PowerSeries.trunc_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_C (n) (a : R) : trunc (n + 1) (C a) = Polynomial.C a
参数：n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem trunc_C (n) (a : R) : trunc (n + 1) (C a) = Polynomial.C a :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, coeff_C, Polynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all
/-
**PowerSeries.trunc_succ** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_succ (f : R⟦X⟧) (n : Nat) : trunc n.succ f = trunc n f + Polynomial.
monomial n (coeff n f)
参数：f : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.trunc_apply`：trunc_apply (n : Nat) (φ : R⟦X⟧) : trunc n φ = 
∑ m in Ico 0 n, Polynomial.monomial m (coeff m φ)
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
-/
theorem trunc_succ (f : R⟦X⟧) (n : ℕ) :
    trunc n.succ f = trunc n f + Polynomial.monomial n (coeff n f) := by
  rw [trunc_apply, Ico_zero_eq_range, sum_range_succ, trunc_apply, Ico_zero_eq_range]
/-
**PowerSeries.natDegree_trunc_lt** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：natDegree_trunc_lt (f : R⟦X⟧) (n) : (trunc (n + 1) f).natDegree < n + 1
参数：f : R⟦X⟧；n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem natDegree_trunc_lt (f : R⟦X⟧) (n) : (trunc (n + 1) f).natDegree < n + 1 := by
  simp +contextual [natDegree_le_iff_coeff_eq_zero, coeff_trunc]
/-
**PowerSeries.trunc_zero'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : PowerSeries R}, (PowerSeries.tru
nc 0) f = 0
参数：PowerSeries.trunc 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma trunc_zero' {f : R⟦X⟧} : trunc 0 f = 0 := rfl
/-
**PowerSeries.degree_trunc_lt** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：degree_trunc_lt (f : R⟦X⟧) (n) : (trunc n f).degree < n
参数：f : R⟦X⟧；n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem degree_trunc_lt (f : R⟦X⟧) (n) : (trunc n f).degree < n := by
  simp +contextual [degree_lt_iff_coeff_zero, coeff_trunc]
/-
**PowerSeries.eval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_trunc_eq_sum_range {S : Type*} [Semiring S] (s : S) (G : R →+* S) (n) (f : R⟦X⟧) :
    (trunc n f).eval₂ G s = ∑ i ∈ range n, G (coeff i f) * s ^ i := by
  cases n with
  | zero =>
    rw [trunc_zero', range_zero, sum_empty, eval₂_zero]
  | succ n =>
    have := natDegree_trunc_lt f n
    rw [eval₂_eq_sum_range' (hn := this)]
    apply sum_congr rfl
    intro _ h
    rw [mem_range] at h
    congr
    rw [coeff_trunc, if_pos h]
/-
**PowerSeries.trunc_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), (PowerSeries.trunc (n + 2)) 
PowerSeries.X = Polynomial.X
参数：n : ℕ；PowerSeries.trunc (n + 2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_X_of_ne_one`：coeff_X_of_ne_one {n : Nat} (hn : n != 1) 
: coeff (X : R[X]) n = 0
· 使用定理 `Nat.one_lt_succ_succ`：∀ (n : ℕ), 1 < n.succ.succ
-/
@[simp] theorem trunc_X (n) : trunc (n + 2) X = (Polynomial.X : R[X]) := by
  ext d
  rw [coeff_trunc, coeff_X]
  split_ifs with h₁ h₂
  · rw [h₂, coeff_X_one]
  · rw [coeff_X_of_ne_one h₂]
  · rw [coeff_X_of_ne_one]
    intro hd
    apply h₁
    rw [hd]
    exact n.one_lt_succ_succ
/-
**PowerSeries.trunc_X_of** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_X_of {n : Nat} (hn : 2 <= n) : trunc n X = (Polynomial.X : R[X])
参数：hn : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `PowerSeries.trunc_X`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), (Powe
rSeries.trunc (n + 2)) PowerSeries.X = Polynomial.X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma trunc_X_of {n : ℕ} (hn : 2 ≤ n) : trunc n X = (Polynomial.X : R[X]) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact trunc_X n

@[simp]
/-
**PowerSeries.trunc_one_left** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_one_left (p : R⟦X⟧) : trunc (R
参数：p : R⟦X⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trunc_one_left (p : R⟦X⟧) : trunc (R := R) 1 p = .C (coeff 0 p) := by
  ext i; simp +contextual [coeff_trunc, Polynomial.coeff_C]
/-
**PowerSeries.trunc_one_X** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_one_X : trunc (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.trunc_one_left`：trunc_one_left (p : R⟦X⟧) : trunc (R
· 使用定理 `PowerSeries.coeff_zero_X`：coeff_zero_X : coeff 0 (X : R⟦X⟧) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trunc_one_X : trunc (R := R) 1 X = 0 := by simp

@[simp]
/-
**PowerSeries.trunc_C_mul** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_C_mul (n : Nat) (r : R) (f : R⟦X⟧) : trunc n (C r * f) = .C r * trun
c n f
参数：n : Nat；r : R；f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `PowerSeries.coeff_C_mul`：coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (C a * φ) = a * coeff n φ
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trunc_C_mul (n : ℕ) (r : R) (f : R⟦X⟧) : trunc n (C r * f) = .C r * trunc n f := by
  ext i; simp [coeff_trunc]

@[simp]
/-
**PowerSeries.trunc_mul_C** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_mul_C (n : Nat) (f : R⟦X⟧) (r : R) : trunc n (f * C r) = trunc n f *
 .C r
参数：n : Nat；f : R⟦X⟧；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `PowerSeries.coeff_mul_C`：coeff_mul_C (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (φ * C a) = coeff n φ * a
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trunc_mul_C (n : ℕ) (f : R⟦X⟧) (r : R) : trunc n (f * C r) = trunc n f * .C r := by
  ext i; simp [coeff_trunc]

/-- Split off the first `n` coefficients. -/
/-
**PowerSeries.eq_shift_mul_X_pow_add_trunc** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：eq_shift_mul_X_pow_add_trunc (n : Nat) (f : R⟦X⟧) : f = (mk fun i => coeff
 (i + n) f) * X ^ n + (f.trunc n : R⟦X⟧)
参数：n : Nat；f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `PowerSeries.coeff_mul_X_pow'`：coeff_mul_X_pow' (p : R⟦X⟧) (n d : Nat) : 
coeff d (p * X ^ n) = ite (n <= d) (coeff (d - n) p) 0
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `ite_add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : 
Add α] (a b c d : α),   ((if P then a else b) + if P then c else d) = if P then 
a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Split off the first `n` coefficients.
-/
lemma eq_shift_mul_X_pow_add_trunc (n : ℕ) (f : R⟦X⟧) :
    f = (mk fun i ↦ coeff (i + n) f) * X ^ n + (f.trunc n : R⟦X⟧) := by
  ext j
  rw [map_add, Polynomial.coeff_coe, coeff_mul_X_pow', coeff_trunc]
  simp_rw [← not_le, ite_not, ite_add_ite]
  simp +contextual

/-- Split off the first `n` coefficients. -/
/-
**PowerSeries.eq_X_pow_mul_shift_add_trunc** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：eq_X_pow_mul_shift_add_trunc (n : Nat) (f : R⟦X⟧) : f = X ^ n * (mk fun i 
=> coeff (i + n) f) + (f.trunc n : R⟦X⟧)
参数：n : Nat；f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `PowerSeries.commute_X_pow`：commute_X_pow (φ : R⟦X⟧) (n : Nat) : Commute 
φ (X ^ n)
· 使用引理 `PowerSeries.eq_shift_mul_X_pow_add_trunc`：eq_shift_mul_X_pow_add_trunc (
n : Nat) (f : R⟦X⟧) : f = (mk fun i => coeff (i + n) f) * X ^ n + (f.trunc n : R
⟦X⟧)

--- 原说明 ---
Split off the first `n` coefficients.
-/
lemma eq_X_pow_mul_shift_add_trunc (n : ℕ) (f : R⟦X⟧) :
    f = X ^ n * (mk fun i ↦ coeff (i + n) f) + (f.trunc n : R⟦X⟧) := by
  rw [← (commute_X_pow _ n).eq, ← eq_shift_mul_X_pow_add_trunc]
/-
**PowerSeries.monomial_eq_C_mul_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：monomial_eq_C_mul_X_pow (r : R) (n : Nat) : monomial n r = C r * X ^ n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
· 使用定理 `PowerSeries.coeff_C_mul`：coeff_C_mul (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (C a * φ) = a * coeff n φ
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monomial_eq_C_mul_X_pow (r : R) (n : ℕ) : monomial n r = C r * X ^ n := by
  ext; simp [coeff_X_pow, coeff_monomial]

@[simp]
/-
**PowerSeries.trunc_X_pow_self_mul** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_X_pow_self_mul (n : Nat) (p : R⟦X⟧) : (X ^ n * p).trunc n = 0
参数：n : Nat；p : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `PowerSeries.coeff_X_pow_mul'`：coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) : 
coeff d (X ^ n * p) = ite (n <= d) (coeff (d - n) p) 0
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma trunc_X_pow_self_mul (n : ℕ) (p : R⟦X⟧) : (X ^ n * p).trunc n = 0 := by
  ext; simp +contextual [coeff_trunc, coeff_X_pow_mul']

end Trunc

section Trunc
/-
Lemmas in this section involve the coercion `R[X] → R⟦X⟧`, so they may only be stated in the case
`R` is commutative. This is because the coercion is an `R`-algebra map.
-/
variable {R : Type*} [CommSemiring R]

open Nat hiding pow_succ pow_zero
open Finset Finset.Nat

/-
**PowerSeries.trunc_trunc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_trunc_of_le {n m} (f : R⟦X⟧) (hnm : n <= m
参数：f : R⟦X⟧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem trunc_trunc_of_le {n m} (f : R⟦X⟧) (hnm : n ≤ m := by rfl) :
    trunc n ↑(trunc m f) = trunc n f := by
  ext d
  rw [coeff_trunc, coeff_trunc, coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos <| lt_of_lt_of_le h hnm]
  · rfl
/-
**PowerSeries.trunc_trunc** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] {n : ℕ} (f : PowerSeries R),   (P
owerSeries.trunc n) ↑((PowerSeries.trunc n) f) = (PowerSeries.trunc n) f
参数：f : PowerSeries R；PowerSeries.trunc n；(PowerSeries.trunc n) f；PowerSeries.tru
nc n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.trunc_trunc_of_le`：trunc_trunc_of_le {n m} (f : R⟦X⟧) (hnm :
 n <= m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] theorem trunc_trunc {n} (f : R⟦X⟧) : trunc n ↑(trunc n f) = trunc n f :=
  trunc_trunc_of_le f
/-
**PowerSeries.trunc_trunc_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] {n : ℕ} (f g : PowerSeries R),   
(PowerSeries.trunc n) (↑((PowerSeries.trunc n) f) * g) = (PowerSeries.trunc n) (
f * g)
参数：f g : PowerSeries R；PowerSeries.trunc n；↑((PowerSeries.trunc n) f) * g；PowerS
eries.trunc n；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.fst_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] theorem trunc_trunc_mul {n} (f g : R⟦X⟧) :
    trunc n ((trunc n f) * g : R⟦X⟧) = trunc n (f * g) := by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, sum_congr rfl]
    intro _ hab
    have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
    rw [coeff_coe, coeff_trunc, if_pos ha]
  · rfl
/-
**PowerSeries.trunc_mul_trunc** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] {n : ℕ} (f g : PowerSeries R),   
(PowerSeries.trunc n) (f * ↑((PowerSeries.trunc n) g)) = (PowerSeries.trunc n) (
f * g)
参数：f g : PowerSeries R；PowerSeries.trunc n；f * ↑((PowerSeries.trunc n) g)；PowerS
eries.trunc n；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.trunc_trunc_mul`：∀ {R : Type u_2} [inst : CommSemiring R] {n
 : ℕ} (f g : PowerSeries R),   (PowerSeries.trunc n) (↑((PowerSeries.trunc n) f)
 * g) = (PowerSer…
-/
@[simp] theorem trunc_mul_trunc {n} (f g : R⟦X⟧) :
    trunc n (f * (trunc n g) : R⟦X⟧) = trunc n (f * g) := by
  rw [mul_comm, trunc_trunc_mul, mul_comm]
/-
**PowerSeries.trunc_trunc_mul_trunc** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_trunc_mul_trunc {n} (f g : R⟦X⟧) : trunc n (trunc n f * trunc n g : 
R⟦X⟧) = trunc n (f * g)
参数：f g : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.trunc_trunc_mul`：∀ {R : Type u_2} [inst : CommSemiring R] {n
 : ℕ} (f g : PowerSeries R),   (PowerSeries.trunc n) (↑((PowerSeries.trunc n) f)
 * g) = (PowerSer…
· 使用定理 `PowerSeries.trunc_mul_trunc`：∀ {R : Type u_2} [inst : CommSemiring R] {n
 : ℕ} (f g : PowerSeries R),   (PowerSeries.trunc n) (f * ↑((PowerSeries.trunc n
) g)) = (PowerSer…
-/
theorem trunc_trunc_mul_trunc {n} (f g : R⟦X⟧) :
    trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) := by
  rw [trunc_trunc_mul, trunc_mul_trunc]
/-
**PowerSeries.trunc_trunc_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：∀ {R : Type u_2} [inst : CommSemiring R] (f : PowerSeries R) (n a : ℕ),   
(PowerSeries.trunc n) (↑((PowerSeries.trunc n) f) ^ a) = (PowerSeries.trunc n) (
f ^ a)
参数：f : PowerSeries R；n a : ℕ；PowerSeries.trunc n；↑((PowerSeries.trunc n) f) ^ a；
PowerSeries.trunc n；f ^ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `PowerSeries.trunc_trunc_mul`：∀ {R : Type u_2} [inst : CommSemiring R] {n
 : ℕ} (f g : PowerSeries R),   (PowerSeries.trunc n) (↑((PowerSeries.trunc n) f)
 * g) = (PowerSer…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.trunc_trunc_mul_trunc`：trunc_trunc_mul_trunc {n} (f g : R⟦X⟧
) : trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g)
-/
@[simp] theorem trunc_trunc_pow (f : R⟦X⟧) (n a : ℕ) :
    trunc n ((trunc n f : R⟦X⟧) ^ a) = trunc n (f ^ a) := by
  induction a with
  | zero =>
    rw [pow_zero, pow_zero]
  | succ a ih =>
    rw [_root_.pow_succ', _root_.pow_succ', trunc_trunc_mul,
      ← trunc_trunc_mul_trunc, ih, trunc_trunc_mul_trunc]
/-
**PowerSeries.trunc_coe_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_coe_eq_self {n} {f : R[X]} (hn : natDegree f < n) : trunc n (f : R⟦X
⟧) = f
参数：hn : natDegree f < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_inj`：coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem trunc_coe_eq_self {n} {f : R[X]} (hn : natDegree f < n) : trunc n (f : R⟦X⟧) = f := by
  rw [← Polynomial.coe_inj]
  ext m
  rw [coeff_coe, coeff_trunc]
  split
  case isTrue h => rfl
  case isFalse h =>
    rw [not_lt] at h
    rw [coeff_coe]; symm
    exact coeff_eq_zero_of_natDegree_lt <| lt_of_lt_of_le hn h

/-- The function `coeff n : R⟦X⟧ → R` is continuous. I.e. `coeff n f` depends only on a sufficiently
long truncation of the power series `f`. -/
/-
**PowerSeries.coeff_coe_trunc_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_coe_trunc_of_lt {n m} {f : R⟦X⟧} (h : n < m) : coeff n (trunc m f) =
 coeff n f
参数：h : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_coe`：coeff_coe (n) : PowerSeries.coeff n φ = coeff φ n
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
The function `coeff n : R⟦X⟧ → R` is continuous. I.e. `coeff n f` depends only o
n a sufficiently
long truncation of the power series `f`.
-/
theorem coeff_coe_trunc_of_lt {n m} {f : R⟦X⟧} (h : n < m) :
    coeff n (trunc m f) = coeff n f := by
  rwa [coeff_coe, coeff_trunc, if_pos]

/-- The `n`-th coefficient of `f*g` may be calculated
from the truncations of `f` and `g`. -/
/-
**PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：coeff_mul_eq_coeff_trunc_mul_trunc {d n} (f g) (h : d < n) : coeff d (f * 
g) = coeff d ((trunc n f : R⟦X⟧) * (trunc n g : R⟦X⟧))
参数：f g；h : d < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc₂`：coeff_mul_eq_coeff_trun
c_mul_trunc₂ {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b) : coeff n (f * g) = 
coeff n ((trunc a f : R⟦X⟧) * (trunc …

--- 原说明 ---
The `n`-th coefficient of `f*g` may be calculated
from the truncations of `f` and `g`.
-/
theorem coeff_mul_eq_coeff_trunc_mul_trunc₂ {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b) :
    coeff n (f * g) = coeff n ((trunc a f : R⟦X⟧) * (trunc b g : R⟦X⟧)) := by
  symm
  rw [← coeff_coe_trunc_of_lt n.lt_succ_self, ← trunc_trunc_mul_trunc, trunc_trunc_of_le f ha,
    trunc_trunc_of_le g hb, trunc_trunc_mul_trunc, coeff_coe_trunc_of_lt n.lt_succ_self]
/-
**PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：coeff_mul_eq_coeff_trunc_mul_trunc {d n} (f g) (h : d < n) : coeff d (f * 
g) = coeff d ((trunc n f : R⟦X⟧) * (trunc n g : R⟦X⟧))
参数：f g；h : d < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc₂`：coeff_mul_eq_coeff_trun
c_mul_trunc₂ {n a b} (f g : R⟦X⟧) (ha : n < a) (hb : n < b) : coeff n (f * g) = 
coeff n ((trunc a f : R⟦X⟧) * (trunc …
-/
theorem coeff_mul_eq_coeff_trunc_mul_trunc {d n} (f g) (h : d < n) :
    coeff d (f * g) = coeff d ((trunc n f : R⟦X⟧) * (trunc n g : R⟦X⟧)) :=
  coeff_mul_eq_coeff_trunc_mul_trunc₂ f g h h

end Trunc

section Ring

variable [Ring R]

@[simp]
/-
**PowerSeries.trunc_sub** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_sub (n : Nat) (φ ψ : R⟦X⟧) : trunc n (φ - ψ) = trunc n φ - trunc n ψ
参数：n : Nat；φ ψ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trunc_sub (n : ℕ) (φ ψ : R⟦X⟧) : trunc n (φ - ψ) = trunc n φ - trunc n ψ := by
  ext i
  simp

end Ring

section Map
variable {S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

/-
**PowerSeries.trunc_map** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：trunc_map (p : R⟦X⟧) (n : Nat) : (p.map f).trunc n = (p.trunc n).map f
参数：p : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_trunc`：coeff_trunc (m) (n) (φ : R⟦X⟧) : (trunc n φ).co
eff m = if m < n then coeff m φ else 0
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trunc_map (p : R⟦X⟧) (n : ℕ) : (p.map f).trunc n = (p.trunc n).map f := by
  ext m; simp [coeff_trunc, apply_ite f]

end Map

end PowerSeries

end

