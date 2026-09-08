/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!
# The discriminant of a matrix
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The discriminant of a matrix is defined to be the discriminant of its characteristic
polynomial. -/
/-
**Matrix.discr** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：discr (A : Matrix n n R) : R
参数：A : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discriminant of a matrix is defined to be the discriminant of its characteri
stic
polynomial.
-/
noncomputable def discr (A : Matrix n n R) : R := A.charpoly.discr

@[simp]
/-
**Matrix.discr_conj** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：discr_conj (g : GL n R) (m : Matrix n n R) : (g.val * m * g.val⁻¹).discr =
 m.discr
参数：g : GL n R；m : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly_units_conj`：charpoly_units_conj (M : (Matrix n n R)ˣ) (N
 : Matrix n n R) : (M.val * N * M.val⁻¹).charpoly = N.charpoly
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma discr_conj (g : GL n R) (m : Matrix n n R) : (g.val * m * g.val⁻¹).discr = m.discr := by
  simp [discr]

@[simp]
/-
**Matrix.discr_conj'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：discr_conj' (g : GL n R) (m : Matrix n n R) : (g.val⁻¹ * m * g.val).discr 
= m.discr
参数：g : GL n R；m : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly_units_conj'`：charpoly_units_conj' (M : (Matrix n n R)ˣ) 
(N : Matrix n n R) : (M.val⁻¹ * N * M.val).charpoly = N.charpoly
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma discr_conj' (g : GL n R) (m : Matrix n n R) : (g.val⁻¹ * m * g.val).discr = m.discr := by
  simp [discr]
/-
**Matrix.discr_of_card_eq_two** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) : A.disc
r = A.trace ^ 2 - 4 * A.det
参数：A : Matrix n n R；hn : Fintype.card n = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.discr.eq_1`：∀ {R : Type u_1} {n : Type u_2} [inst : CommRing R] [
inst_1 : Fintype n] [inst_2 : DecidableEq n] (A : Matrix n n R),   A.discr = A.c
harpoly…
· 使用引理 `Polynomial.discr_of_degree_eq_two`：discr_of_degree_eq_two {f : R[X]} (hf
 : f.degree = 2) : discr f = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charpoly_degree_eq_dim`：charpoly_degree_eq_dim [Nontrivial R] (M 
: Matrix n n R) : M.charpoly.degree = Fintype.card n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Matrix.charpoly_of_card_eq_two`：charpoly_of_card_eq_two [Nontrivial R] (
hn : Fintype.card n = 2) : M.charpoly = X ^ 2 - C M.trace * X + C M.det
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
（共 31 条，此处仅展示前 30 条）
-/
lemma discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  rw [discr, Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]
/-
**Matrix.discr_fin_two** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.discr = A.trace ^ 2 - 4 *
 A.det
参数：A : Matrix (Fin 2) (Fin 2) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.discr_of_card_eq_two`：discr_of_card_eq_two (A : Matrix n n R) (hn
 : Fintype.card n = 2) : A.discr = A.trace ^ 2 - 4 * A.det
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
lemma discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
  A.discr_of_card_eq_two <| Fintype.card_fin _

end Matrix

