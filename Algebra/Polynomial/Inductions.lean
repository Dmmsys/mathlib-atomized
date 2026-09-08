/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Damiano Testa, Jens Wagemaker
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Division
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/

@[expose] public section


noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

/-- `divX p` returns a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
/-
**Polynomial.divX** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：divX (p : R[X]) : R[X]
参数：p : R[X]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α

--- 原说明 ---
`divX p` returns a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possibl
e
-/
def divX (p : R[X]) : R[X] :=
  ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩

@[simp]
/-
**Polynomial.coeff_divX** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_divX : (divX p).coeff n = p.coeff (n + 1) := by
  rw [add_comm]; cases p; rfl
/-
**Polynomial.divX_mul_X_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_mul_X_add (p : R[X]) : divX p * X + C (p.coeff 0) = p
参数：p : R[X]。
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
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem divX_mul_X_add (p : R[X]) : divX p * X + C (p.coeff 0) = p :=
  ext <| by rintro ⟨_ | _⟩ <;> simp [coeff_C, coeff_mul_X]

@[simp]
/-
**Polynomial.X_mul_divX_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_mul_divX_add (p : R[X]) : X * divX p + C (p.coeff 0) = p
参数：p : R[X]。
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
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_X_mul`：coeff_X_mul (p : R[X]) (n : Nat) : coeff (X * p)
 (n + 1) = coeff p n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem X_mul_divX_add (p : R[X]) : X * divX p + C (p.coeff 0) = p :=
  ext <| by rintro ⟨_ | _⟩ <;> simp [coeff_C]

@[simp]
/-
**Polynomial.divX_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_C (a : R) : divX (C a) = 0
参数：a : R。
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
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divX_C (a : R) : divX (C a) = 0 :=
  ext fun n => by simp [coeff_divX]
/-
**Polynomial.divX_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_eq_zero_iff : divX p = 0 ↔ p = C (p.coeff 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.divX_mul_X_add`：divX_mul_X_add (p : R[X]) : divX p * X + C (p
.coeff 0) = p
· 使用定理 `Polynomial.divX_C`：divX_C (a : R) : divX (C a) = 0
-/
theorem divX_eq_zero_iff : divX p = 0 ↔ p = C (p.coeff 0) :=
  ⟨fun h => by simpa [eq_comm, h] using divX_mul_X_add p, fun h => by rw [h, divX_C]⟩
/-
**Polynomial.divX_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_add : divX (p + q) = divX p + divX q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem divX_add : divX (p + q) = divX p + divX q :=
  ext <| by simp

@[simp]
/-
**Polynomial.divX_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_zero : divX (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem divX_zero : divX (0 : R[X]) = 0 := leadingCoeff_eq_zero.mp rfl

@[simp]
/-
**Polynomial.divX_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_one : divX (1 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
-/
theorem divX_one : divX (1 : R[X]) = 0 := by
  ext
  simpa only [coeff_divX, coeff_zero] using! coeff_one

@[simp]
/-
**Polynomial.divX_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_C_mul : divX (C a * p) = C a * divX p
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
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divX_C_mul : divX (C a * p) = C a * divX p := by
  ext
  simp
/-
**Polynomial.divX_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_X_pow : divX (X ^ n : R[X]) = if (n = 0) then 0 else X ^ (n - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.divX_one`：divX_one : divX (1 : R[X]) = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem divX_X_pow : divX (X ^ n : R[X]) = if (n = 0) then 0 else X ^ (n - 1) := by
  cases n
  · simp
  · ext n
    simp [coeff_X_pow]

/-- `divX` as an additive homomorphism. -/
noncomputable
/-
**Polynomial.divX_hom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：divX_hom : R[X] ->+ R[X]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.divX_zero`：divX_zero : divX (0 : R[X]) = 0
· 使用定理 `Polynomial.divX_add`：divX_add : divX (p + q) = divX p + divX q
-/
def divX_hom : R[X] →+ R[X] :=
  { toFun := divX
    map_zero' := divX_zero
    map_add' := fun _ _ => divX_add }
/-
**Polynomial.divX_hom_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, Polynomial.divX_hom
 p = p.divX
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem divX_hom_toFun : divX_hom p = divX p := rfl
/-
**Polynomial.natDegree_divX_eq_natDegree_tsub_one** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：natDegree_divX_eq_natDegree_tsub_one : p.divX.natDegree = p.natDegree - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_natDegree_eq_sub`：map_natDegree_eq_sub {S F : Type*} [Sem
iring S] [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : F} {p : R[X]
} {k : Nat} (φ_k : fo…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.divX_hom_toFun`：∀ {R : Type u} [inst : Semiring R] {p : Polyn
omial R}, Polynomial.divX_hom p = p.divX
· 使用定理 `Polynomial.divX_C_mul`：divX_C_mul : divX (C a * p) = C a * divX p
· 使用定理 `Polynomial.divX_X_pow`：divX_X_pow : divX (X ^ n : R[X]) = if (n = 0) the
n 0 else X ^ (n - 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.natDegree_C_mul_X_pow`：natDegree_C_mul_X_pow (n : Nat) (a : R
) (ha : a != 0) : natDegree (C a * X ^ n) = n
-/
theorem natDegree_divX_eq_natDegree_tsub_one : p.divX.natDegree = p.natDegree - 1 := by
  apply map_natDegree_eq_sub (φ := divX_hom)
  · intro f
    simpa [divX_hom, divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intro n c c0
    rw [← C_mul_X_pow_eq_monomial, divX_hom_toFun, divX_C_mul, divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0
/-
**Polynomial.natDegree_divX_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_divX_le : p.divX.natDegree <= p.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Polynomial.natDegree_divX_eq_natDegree_tsub_one`：natDegree_divX_eq_natDe
gree_tsub_one : p.divX.natDegree = p.natDegree - 1
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
-/
theorem natDegree_divX_le : p.divX.natDegree ≤ p.natDegree :=
  natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)
/-
**Polynomial.divX_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：divX_C_mul_X_pow : divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n 
- 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.divX_C_mul`：divX_C_mul : divX (C a * p) = C a * divX p
· 使用定理 `Polynomial.divX_X_pow`：divX_X_pow : divX (X ^ n : R[X]) = if (n = 0) the
n 0 else X ^ (n - 1)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divX_C_mul_X_pow : divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n - 1) := by
  simp only [divX_C_mul, divX_X_pow, mul_ite, mul_zero]
/-
**Polynomial.degree_divX_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_divX_lt (hp0 : p != 0) : (divX p).degree < p.degree
参数：hp0 : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.divX_C`：divX_C (a : R) : divX (C a) = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Polynomial.zero_le_degree_iff`：zero_le_degree_iff : 0 <= degree p ↔ p !=
 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.divX_eq_zero_iff`：divX_eq_zero_iff : divX p = 0 ↔ p = C (p.co
eff 0)
（共 35 条，此处仅展示前 30 条）
-/
theorem degree_divX_lt (hp0 : p ≠ 0) : (divX p).degree < p.degree := by
  have := Nontrivial.of_polynomial_ne hp0
  calc
    degree (divX p) < (divX p * X + C (p.coeff 0)).degree :=
      if h : degree p ≤ 0 then by
        have h' : C (p.coeff 0) ≠ 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h, divX_C, degree_zero, zero_mul, zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : divX p ≠ 0 := by
          simpa [divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (divX p) * leadingCoeff X ≠ 0 := by simpa
        have : degree (C (p.coeff 0)) < degree (divX p * X) :=
          calc
            degree (C (p.coeff 0)) ≤ 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (X : R[X]) := degree_X.symm
            _ ≤ degree (divX p * X) := by
              rw [← zero_add (degree X), degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_elim]
/-
**Polynomial.recOnHorner** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：recOnHorner {M : R[X] -> Sort*} (p : R[X]) (M0 : M 0) (MC : forall p a, co
eff p 0 = 0 -> a != 0 -> M p -> M (p + C a)) (MX : forall p, p != 0 -> M p -> M 
(p * X)) : M p
参数：p : R[X]；M0 : M 0；MC : forall p a, coeff p 0 = 0 -> a != 0 -> M p -> M (p + C
 a)；MX : forall p, p != 0 -> M p -> M (p * X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An induction principle for polynomials, valued in Sort* instead of Prop.
-/
noncomputable def recOnHorner {M : R[X] → Sort*} (p : R[X]) (M0 : M 0)
    (MC : ∀ p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a))
    (MX : ∀ p, p ≠ 0 → M p → M (p * X)) : M p :=
  letI := Classical.decEq R
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    rw [← divX_mul_X_add p] at *
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0, C_0, add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by p.degree

/-- A property holds for all polynomials of positive `degree` with coefficients in a semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,

with appropriate restrictions on each term.

See `natDegree_ne_zero_induction_on` for a similar statement involving no explicit multiplication.
-/
@[elab_as_elim]
/-
**Polynomial.degree_pos_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_pos_induction_on {P : R[X] -> Prop} (p : R[X]) (h0 : 0 < degree p) 
(hC : forall {a}, a != 0 -> P (C a * X)) (hX : forall {p}, 0 < degree p -> P p -
> P (p * X)) (hadd : forall {p} {a}, 0 < degree p -> P p -> P (p + C a)) : P p
参数：p : R[X]；h0 : 0 < degree p；hC : forall {a}, a != 0 -> P (C a * X)；hX : forall
 {p}, 0 < degree p -> P p -> P (p * X)；hadd : forall {p} {a}, 0 < degree p -> P 
p -> P (p + C a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
A property holds for all polynomials of positive `degree` with coefficients in a
 semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,

with appropriate restrictions on each term.

See `natDegree_ne_zero_induction_on` for a similar statement involving no explic
it multiplication.
-/
theorem degree_pos_induction_on {P : R[X] → Prop} (p : R[X]) (h0 : 0 < degree p)
    (hC : ∀ {a}, a ≠ 0 → P (C a * X)) (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
    (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
  recOnHorner p (fun h => by rw [degree_zero] at h; exact absurd h (by decide))
    (fun p a heq0 _ ih h0 =>
      (have : 0 < degree p :=
        (lt_of_not_ge fun h =>
          not_lt_of_ge (degree_C_le (a := a)) <|
            by rwa [eq_C_of_degree_le_zero h, ← C_add, heq0, zero_add] at h0)
      hadd this (ih this)))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        exact hC fun h : coeff p 0 = 0 => by simp [h] at h0')
    h0

/-- A property holds for all polynomials of non-zero `natDegree` with coefficients in a
semiring `R` if it holds for
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
* `p + q`, with `p, q ∈ R[X]`,
* monomials with nonzero coefficient and non-zero exponent,

with appropriate restrictions on each term.

Note that multiplication is "hidden" in the assumption on monomials, so there is no explicit
multiplication in the statement.
See `degree_pos_induction_on` for a similar statement involving more explicit multiplications.
-/
@[elab_as_elim]
/-
**Polynomial.natDegree_ne_zero_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natDegree_ne_zero_induction_on {M : R[X] -> Prop} {f : R[X]} (f0 : f.natDe
gree != 0) (h_C_add : forall {a p}, M p -> M (C a + p)) (h_add : forall {p q}, M
 p -> M q -> M (p + q)) (h_monomial : forall {n : Nat} {a : R}, a != 0 -> n != 0
 -> M (monomial n a)) : M f
参数：f0 : f.natDegree != 0；h_C_add : forall {a p}, M p -> M (C a + p)；h_add : fora
ll {p q}, M p -> M q -> M (p + q)；h_monomial : forall {n : Nat} {a : R}, a != 0 
-> n != 0 -> M (monomial n a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0

--- 原说明 ---
A property holds for all polynomials of non-zero `natDegree` with coefficients i
n a
semiring `R` if it holds for
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
* `p + q`, with `p, q ∈ R[X]`,
* monomials with nonzero coefficient and non-zero exponent,

with appropriate restrictions on each term.

Note that multiplication is "hidden" in the assumption on monomials, so there is
 no explicit
multiplication in the statement.
See `degree_pos_induction_on` for a similar statement involving more explicit mu
ltiplications.
-/
theorem natDegree_ne_zero_induction_on {M : R[X] → Prop} {f : R[X]} (f0 : f.natDegree ≠ 0)
    (h_C_add : ∀ {a p}, M p → M (C a + p)) (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_monomial : ∀ {n : ℕ} {a : R}, a ≠ 0 → n ≠ 0 → M (monomial n a)) : M f := by
  suffices f.natDegree = 0 ∨ M f from Or.recOn this (fun h => (f0 h).elim) id
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
  · rintro p q (hp | hp) (hq | hq)
    · refine Or.inl ?_
      rw [eq_C_of_natDegree_eq_zero hp, eq_C_of_natDegree_eq_zero hq, ← C_add, natDegree_C]
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hp]
      exact h_C_add hq
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hq, add_comm]
      exact h_C_add hp
    · exact Or.inr (h_add hp hq)
  · intro n a _
    by_cases a0 : a = 0
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
    · refine Or.inr ?_
      rw [C_mul_X_pow_eq_monomial]
      exact h_monomial a0 n.succ_ne_zero

end Semiring

end Polynomial

