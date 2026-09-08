/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Perm.Sign

import Mathlib.Algebra.Module.End
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Nonsingular inverses over semirings

This file proves `A * B = 1 ↔ B * A = 1` for square matrices over a commutative semiring.

-/

@[expose] public section

open Equiv Equiv.Perm Finset

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

namespace Matrix

/-- The determinant, but only the terms of a given sign.
`A.detp 1` is written `|A|⁺` in the literature and `A.detp (-1)` is written `|A|⁻`. -/
/-
**Matrix.detp** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：detp : R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant, but only the terms of a given sign.
`A.detp 1` is written `|A|⁺` in the literature and `A.detp (-1)` is written `|A|
⁻`.
-/
def detp : R := ∑ σ ∈ ofSign s, ∏ k, A k (σ k)
/-
**Matrix.detp_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n R), Matrix.detp s A.trans
pose = Matrix.detp s A
参数：s : ℤˣ；A : Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma detp_transpose : A.transpose.detp s = A.detp s :=
  sum_equiv (.inv _) (by simp) fun σ _ ↦ prod_equiv σ (by simp) (by simp)
/-
**Matrix.detp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] (s : ℤˣ)   [Nonempty n], Matrix.detp s 0 = 0
参数：s : ℤˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma detp_zero [Nonempty n] : (0 : Matrix n n R).detp s = 0 := by simp [detp]

@[simp]
/-
**Matrix.detp_one_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_one_diagonal (d : n -> R) : detp 1 (diagonal d) = ∏ i, d i
参数：d : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp.eq_1`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [in
st_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n R), M
atrix.…
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
-/
lemma detp_one_diagonal (d : n → R) : detp 1 (diagonal d) = ∏ i, d i := by
  rw [detp, sum_eq_single_of_mem 1]
  · simp
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]
/-
**Matrix.detp_one_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_one_one : detp 1 (1 : Matrix n n R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用引理 `Matrix.detp_one_diagonal`：detp_one_diagonal (d : n -> R) : detp 1 (diago
nal d) = ∏ i, d i
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
lemma detp_one_one : detp 1 (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one, detp_one_diagonal, prod_const_one]

@[simp]
/-
**Matrix.detp_neg_one_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_neg_one_diagonal (d : n -> R) : detp (-1) (diagonal d) = 0
参数：d : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp.eq_1`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [in
st_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n R), M
atrix.…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用引理 `Equiv.Perm.mem_ofSign`：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign 
s ↔ σ.sign = s
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
-/
lemma detp_neg_one_diagonal (d : n → R) : detp (-1) (diagonal d) = 0 := by
  rw [detp, sum_eq_zero]
  intro σ hσ
  have hσ1 : σ ≠ 1 := by
    contrapose hσ
    rw [hσ, mem_ofSign, sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]
/-
**Matrix.detp_neg_one_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用引理 `Matrix.detp_neg_one_diagonal`：detp_neg_one_diagonal (d : n -> R) : detp 
(-1) (diagonal d) = 0
-/
lemma detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0 := by
  rw [← diagonal_one, detp_neg_one_diagonal]
/-
**Matrix.detp_one_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] (A : Matrix n n R)   [IsEmpty n], Matrix.detp 1 A = 
1
参数：A : Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp.eq_1`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [in
st_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n R), M
atrix.…
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Finset.sum_unique_nonempty`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddC
ommMonoid M] [inst_1 : Unique ι] (s : Finset ι) (f : ι → M),   s.Nonempty → ∑ x 
∈ s, f x = f def…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
-/
@[simp] lemma detp_one_of_isEmpty [IsEmpty n] : A.detp 1 = 1 := by
  rw [detp, sum_unique_nonempty _ _ ⟨1, _⟩] <;> simp
/-
**Matrix.detp_neg_one_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] (A : Matrix n n R)   [IsEmpty n], Matrix.detp (-1) A
 = 0
参数：A : Matrix n n R；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp.eq_1`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [in
st_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n R), M
atrix.…
· 使用定理 `Equiv.Perm.ofSign.eq_1`：∀ {α : Type u} [inst : DecidableEq α] [inst_1 : 
Fintype α] (s : ℤˣ), Equiv.Perm.ofSign s = {x | Equiv.Perm.sign x = s}
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
-/
@[simp] lemma detp_neg_one_of_isEmpty [IsEmpty n] : A.detp (-1) = 0 := by
  rw [detp, ofSign, univ_unique]
  convert sum_empty
  simp +decide
/-
**Matrix.detp_submatrix_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {m : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : CommS
emiring R] (s : ℤˣ) (A : Matrix n n R) (f g : m ≃ n),   Matrix.detp s (A.submatr
ix ⇑f ⇑g) = Matrix.detp (s * Equiv.Perm.sign (f.symm.trans g)) A
参数：s : ℤˣ；A : Matrix n n R；f g : m ≃ n；A.submatrix ⇑f ⇑g；s * Equiv.Perm.sign (f.
symm.trans g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_equivCongr`：∀ {α : Type u} [inst : DecidableEq α] {β : T
ype v} [inst_1 : Fintype α] [inst_2 : DecidableEq β] [inst_3 : Fintype β]   (f g
 : α ≃ β) (p : E…
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma detp_submatrix_equiv_equiv (f g : m ≃ n) :
    (A.submatrix f g).detp s = A.detp (s * sign (f.symm.trans g)) :=
  sum_equiv (equivCongr f g) (by simp) fun _ _ ↦ prod_equiv f (by simp) fun _ _ ↦ by simp
/-
**Matrix.detp_submatrix_equiv_self** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_submatrix_equiv_self (e : m ≃ n) : (A.submatrix e e).detp s = A.detp 
s
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.detp_submatrix_equiv_equiv`：∀ {n : Type u_1} {m : Type u_2} {R : 
Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq m]   [in
st_3 : DecidableEq n] […
· 使用定理 `Matrix.detp.congr_simp`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype 
n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : CommSemiring R]
 (s s_1 : ℤˣ…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma detp_submatrix_equiv_self (e : m ≃ n) : (A.submatrix e e).detp s = A.detp s := by
  simp
/-
**Matrix.detp_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_smul (c : R) : (c • A).detp s = c ^ Fintype.card n * A.detp s
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma detp_smul (c : R) : (c • A).detp s = c ^ Fintype.card n * A.detp s := by
  simp [detp, Finset.mul_sum, Finset.prod_mul_distrib]
/-
**Matrix.detp_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_map {S : Type*} [CommSemiring S] (f : R ->+* S) : (A.map f).detp s = 
f (A.detp s)
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma detp_map {S : Type*} [CommSemiring S] (f : R →+* S) :
    (A.map f).detp s = f (A.detp s) := by simp [detp]

/-- A square matrix `A` over a commutative semiring `R` is "determinant balanced"
with respect to `a b : R` if `a|A|⁺ + b|A|⁻ = b|A|⁺ + a|A|⁻`. Over a commutative ring,
this is equivalent to `(a - b)|A| = 0`, see `Matrix.isDetpBalanced_iff_sub_mul_det_eq_zero`. -/
/-
**Matrix.IsDetpBalanced** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsDetpBalanced (a b : R) : Prop
参数：a b : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix `A` over a commutative semiring `R` is "determinant balanced"
with respect to `a b : R` if `a|A|⁺ + b|A|⁻ = b|A|⁺ + a|A|⁻`. Over a commutative
 ring,
this is equivalent to `(a - b)|A| = 0`, see `Matrix.isDetpBalanced_iff_sub_mul_d
et_eq_zero`.
-/
def IsDetpBalanced (a b : R) : Prop :=
  a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1)
/-
**Matrix.IsDetpBalanced.refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetpBalanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] (A : Matrix n n R)   (a : R), A.IsDetpBalanced a a
参数：A : Matrix n n R；a : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsDetpBalanced.refl (a : R) : A.IsDetpBalanced a a := rfl

variable {A} {a b c : R}
/-
**Matrix.IsDetpBalanced.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetpBalanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R}, Matrix.detp 1 A = Ma
trix.detp (-1) A → A.IsDetpBalanced a b
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsDetpBalanced.eq_1`：∀ {n : Type u_1} {R : Type u_3} [inst : Fint
ype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (A : Matrix n n R)   (
a b : R),   A.Is…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma IsDetpBalanced.of_eq (eq : A.detp 1 = A.detp (-1)) : A.IsDetpBalanced a b := by
  rw [IsDetpBalanced, eq, add_comm]
/-
**Matrix.IsDetpBalanced.symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetpBalanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R}, A.IsDetpBalanced a b
 → A.IsDetpBalanced b a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsDetpBalanced.symm : A.IsDetpBalanced a b → A.IsDetpBalanced b a := Eq.symm
/-
**Matrix.IsDetpBalanced_comm** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：IsDetpBalanced_comm : A.IsDetpBalanced a b ↔ A.IsDetpBalanced b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
lemma IsDetpBalanced_comm : A.IsDetpBalanced a b ↔ A.IsDetpBalanced b a := Eq.comm
/-
**Matrix.IsDetpBalanced.trans** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetpBalanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b c : R} [IsCancelAdd R], A.
IsDetpBalanced a b → A.IsDetpBalanced b c → A.IsDetpBalanced a c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsDetpBalanced.eq_1`：∀ {n : Type u_1} {R : Type u_3} [inst : Fint
ype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (A : Matrix n n R)   (
a b : R),   A.Is…
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.SemiringInverse.0.Matrix.IsDetpBal
anced.trans._abel_1_2`：∀ {n : Type u_2} {R : Type u_1} [inst : Fintype n] [inst_
1 : DecidableEq n] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b c : R},  
 b …
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.SemiringInverse.0.Matrix.IsDetpBal
anced.trans._abel_1_3`：∀ {n : Type u_2} {R : Type u_1} [inst : Fintype n] [inst_
1 : DecidableEq n] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b c : R},  
 b …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma IsDetpBalanced.trans [IsCancelAdd R]
    (hab : A.IsDetpBalanced a b) (hbc : A.IsDetpBalanced b c) :
    A.IsDetpBalanced a c := by
  rw [IsDetpBalanced] at *
  apply add_left_cancel (a := b * detp 1 A + b * detp (-1) A)
  convert congr($hab + $hbc) using 1 <;> abel
/-
**Matrix.IsDetpBalanced.mul_add_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetpB
alanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R},   A.IsDetpBalanced a
 b →     ∀ (s t : ℤˣ), a * Matrix.detp s A + b * Matrix.detp t A = b * Matrix.de
tp s A + a * Matrix.detp t A
参数：s t : ℤˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsDetpBalanced.mul_add_mul_eq (h : A.IsDetpBalanced a b) (s t : ℤˣ) :
    a * A.detp s + b * A.detp t = b * A.detp s + a * A.detp t := by
  obtain rfl | rfl := Int.units_eq_one_or s <;> obtain rfl | rfl := Int.units_eq_one_or t
  · rw [add_comm]
  · rw [h]
  · rw [add_comm, ← h, add_comm]
  · rw [add_comm]
/-
**Matrix.isDetpBalanced_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R}, A.transpose.IsDetpBa
lanced a b ↔ A.IsDetpBalanced a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.detp_transpose`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n
] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n 
R), Matrix.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isDetpBalanced_transpose_iff : Aᵀ.IsDetpBalanced a b ↔ A.IsDetpBalanced a b := by
  simp [IsDetpBalanced]

alias ⟨IsDetpBalanced.of_transpose, IsDetpBalanced.transpose⟩ := isDetpBalanced_transpose_iff
/-
**Matrix.IsDetpBalanced.submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetp
Balanced`。
形式化陈述：∀ {n : Type u_1} {m : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : CommS
emiring R] {A : Matrix n n R} {a b : R} (e₁ e₂ : m ≃ n),   A.IsDetpBalanced a b 
→ (A.submatrix ⇑e₁ ⇑e₂).IsDetpBalanced a b
参数：e₁ e₂ : m ≃ n；A.submatrix ⇑e₁ ⇑e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp_submatrix_equiv_equiv`：∀ {n : Type u_1} {m : Type u_2} {R : 
Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq m]   [in
st_3 : DecidableEq n] […
· 使用定理 `Matrix.IsDetpBalanced.mul_add_mul_eq`：∀ {n : Type u_1} {R : Type u_3} [i
nst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] {A : Matrix 
n n R}   {a b : R},   A.Is…
-/
lemma IsDetpBalanced.submatrix_equiv (e₁ e₂ : m ≃ n) (h : A.IsDetpBalanced a b) :
    (A.submatrix e₁ e₂).IsDetpBalanced a b := by
  simp_rw [IsDetpBalanced, detp_submatrix_equiv_equiv]
  apply h.mul_add_mul_eq
/-
**Matrix.isDetpBalanced_submatrix_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {m : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : CommS
emiring R] {A : Matrix n n R} {a b : R} {e₁ e₂ : m ≃ n},   (A.submatrix ⇑e₁ ⇑e₂)
.IsDetpBalanced a b ↔ A.IsDetpBalanced a b
参数：A.submatrix ⇑e₁ ⇑e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.IsDetpBalanced.congr_simp`：∀ {n : Type u_1} {R : Type u_3} [inst 
: Fintype n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : CommS
emiring R] (A A_1 : Ma…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Matrix.IsDetpBalanced.submatrix_equiv`：∀ {n : Type u_1} {m : Type u_2} {
R : Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq m]  
 [inst_3 : DecidableEq n] […
-/
@[simp] lemma isDetpBalanced_submatrix_equiv_iff {e₁ e₂ : m ≃ n} :
    (A.submatrix e₁ e₂).IsDetpBalanced a b ↔ A.IsDetpBalanced a b where
  mp h := by simpa using h.submatrix_equiv e₁.symm e₂.symm
  mpr := (·.submatrix_equiv ..)
/-
**Matrix.IsDetpBalanced.smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDetpBalanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R}, A.IsDetpBalanced a b
 → ∀ (c : R), (c • A).IsDetpBalanced a b
参数：c : R；c • A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.detp_smul`：detp_smul (c : R) : (c • A).detp s = c ^ Fintype.card 
n * A.detp s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.IsDetpBalanced.mul_add_mul_eq`：∀ {n : Type u_1} {R : Type u_3} [i
nst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] {A : Matrix 
n n R}   {a b : R},   A.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsDetpBalanced.smul (h : A.IsDetpBalanced a b) (c : R) :
    (c • A).IsDetpBalanced a b := by
  simp_rw [IsDetpBalanced, detp_smul, ← mul_assoc, mul_comm _ (c ^ _), mul_assoc,
    ← mul_add, h.mul_add_mul_eq]

variable (A) in
/-- A square matrix `A` over a commutative semiring `R` is called nonsingular if it is
only determinant balanced with respect to equal elements.

See also See also `Matrix.Nondegenerate`. -/
/-
**Matrix.Nonsingular** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：Nonsingular : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix `A` over a commutative semiring `R` is called nonsingular if it 
is
only determinant balanced with respect to equal elements.

See also See also `Matrix.Nondegenerate`.
-/
def Nonsingular : Prop := ∀ a b : R, A.IsDetpBalanced a b → a = b
/-
**Matrix.Nonsingular.eq_of_IsDetpBalanced** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nons
ingular`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R}, A.Nonsingular → A.Is
DetpBalanced a b → a = b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nonsingular.eq_of_IsDetpBalanced (hA : A.Nonsingular) (hAd : A.IsDetpBalanced a b) :
    a = b := hA a b hAd
/-
**Matrix.IsDetpBalanced.eq_of_nonsingular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsDe
tpBalanced`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] {A : Matrix n n R}   {a b : R}, A.IsDetpBalanced a b
 → A.Nonsingular → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.eq_of_IsDetpBalanced`：∀ {n : Type u_1} {R : Type u_3}
 [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] {A : Matr
ix n n R}   {a b : R}, A.Nons…
-/
lemma IsDetpBalanced.eq_of_nonsingular (hA : A.IsDetpBalanced a b) (hAn : A.Nonsingular) :
    a = b := hAn.eq_of_IsDetpBalanced hA
/-
**Matrix.nonsingular_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R],   Matrix.Nonsingular 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matrix.detp_one_one`：detp_one_one : detp 1 (1 : Matrix n n R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Matrix.detp_neg_one_one`：detp_neg_one_one : detp (-1) (1 : Matrix n n R)
 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
@[simp] lemma nonsingular_one : (1 : Matrix n n R).Nonsingular :=
  fun a b h ↦ by simpa [IsDetpBalanced] using h

variable (A) in
/-
**Matrix.Nonsingular.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nonsingular`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R] (A : Matrix n n R)   [IsEmpty n], A.Nonsingular
参数：A : Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp_one_of_isEmpty`：∀ {n : Type u_1} {R : Type u_3} [inst : Fint
ype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (A : Matrix n n R)   [
IsEmpty n], Matr…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.detp_neg_one_of_isEmpty`：∀ {n : Type u_1} {R : Type u_3} [inst : 
Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (A : Matrix n n R)
   [IsEmpty n], Matr…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma Nonsingular.of_isEmpty [IsEmpty n] : A.Nonsingular := by
  simp [Nonsingular, IsDetpBalanced]
/-
**Matrix.nonsingular_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R]   {A : Matrix n n R}, A.transpose.Nonsingular ↔ A.No
nsingular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma nonsingular_transpose_iff : Aᵀ.Nonsingular ↔ A.Nonsingular := by simp [Nonsingular]

alias ⟨Nonsingular.of_transpose, Nonsingular.transpose⟩ := nonsingular_transpose_iff
/-
**Matrix.nonsingular_submatrix_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {m : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : CommS
emiring R] {A : Matrix n n R} {e₁ e₂ : m ≃ n},   (A.submatrix ⇑e₁ ⇑e₂).Nonsingul
ar ↔ A.Nonsingular
参数：A.submatrix ⇑e₁ ⇑e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma nonsingular_submatrix_equiv_iff {e₁ e₂ : m ≃ n} :
    (A.submatrix e₁ e₂).Nonsingular ↔ A.Nonsingular := by simp [Nonsingular]

alias ⟨_, Nonsingular.submatrix_equiv⟩ := nonsingular_submatrix_equiv_iff
/-
**Matrix.detp_eq_of_row_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_eq_of_row_eq {p q : n} (hpq : p != q) (hrow : A.row p = A.row q) (s :
 Intˣ
参数：hpq : p != q；hrow : A.row p = A.row q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma detp_eq_of_row_eq {p q : n} (hpq : p ≠ q) (hrow : A.row p = A.row q)
    (s : ℤˣ := 1) (t : ℤˣ := -1) : A.detp s = A.detp t := by
  have : A.detp 1 = A.detp (-1) := sum_equiv (.mulRight <| swap p q) (by simp [hpq])
    fun _ _ ↦ prod_equiv (swap p q) (by simp) (by aesop (add simp row))
  obtain rfl | rfl := Int.units_eq_one_or s <;>
  obtain rfl | rfl := Int.units_eq_one_or t <;>
  first | rfl | rw [this]
/-
**Matrix.detp_eq_of_col_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_eq_of_col_eq {p q : n} (hpq : p != q) (hcol : A.col p = A.col q) (s :
 Intˣ
参数：hpq : p != q；hcol : A.col p = A.col q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp_transpose`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n
] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n 
R), Matrix.…
· 使用引理 `Matrix.detp_eq_of_row_eq`：detp_eq_of_row_eq {p q : n} (hpq : p != q) (hr
ow : A.row p = A.row q) (s : Intˣ
-/
lemma detp_eq_of_col_eq {p q : n} (hpq : p ≠ q) (hcol : A.col p = A.col q)
    (s : ℤˣ := 1) (t : ℤˣ := -1) : A.detp s = A.detp t := by
  simpa using detp_eq_of_row_eq (A := Aᵀ) hpq hcol s t
/-
**Matrix.detp_eq_of_row_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_eq_of_row_eq_zero {p : n} (hrow : A.row p = 0) : A.detp s = 0
参数：hrow : A.row p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma detp_eq_of_row_eq_zero {p : n} (hrow : A.row p = 0) : A.detp s = 0 :=
  sum_eq_zero fun _ _ ↦ prod_eq_zero (mem_univ p) congr($hrow _)
/-
**Matrix.detp_eq_of_col_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_eq_of_col_eq_zero {p : n} (hcol : A.col p = 0) : A.detp s = 0
参数：hcol : A.col p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.detp_transpose`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n
] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n 
R), Matrix.…
· 使用引理 `Matrix.detp_eq_of_row_eq_zero`：detp_eq_of_row_eq_zero {p : n} (hrow : A.
row p = 0) : A.detp s = 0
-/
lemma detp_eq_of_col_eq_zero {p : n} (hcol : A.col p = 0) : A.detp s = 0 := by
  simpa using detp_eq_of_row_eq_zero (A := Aᵀ) s hcol

/-- If `A` is determinant balanced with respect to `a` and `b`, any submatrix of
the same or bigger size (possibly with repeated rows or columns) is also. -/
/-
**Matrix.IsDetpBalanced.submatrix_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.I
sDetpBalanced`。
形式化陈述：∀ {n : Type u_1} {m : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : CommS
emiring R] {A : Matrix n n R} {a b : R},   A.IsDetpBalanced a b → Fintype.card n
 ≤ Fintype.card m → ∀ (f g : m → n), (A.submatrix f g).IsDetpBalanced a b
参数：f g : m → n；A.submatrix f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isDetpBalanced_submatrix_equiv_iff`：∀ {n : Type u_1} {m : Type u_
2} {R : Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq 
m]   [inst_3 : DecidableEq n] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.not_injective_iff`：not_injective_iff : ¬ Injective f ↔ exists a
 b, f a = f b ∧ a != b
· 使用定理 `Matrix.IsDetpBalanced.of_eq`：∀ {n : Type u_1} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] {A : Matrix n n R}   
{a b : R}, Matrix…
· 使用引理 `Matrix.detp_eq_of_col_eq`：detp_eq_of_col_eq {p q : n} (hpq : p != q) (hc
ol : A.col p = A.col q) (s : Intˣ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.detp_eq_of_row_eq`：detp_eq_of_row_eq {p q : n} (hpq : p != q) (hr
ow : A.row p = A.row q) (s : Intˣ

--- 原说明 ---
If `A` is determinant balanced with respect to `a` and `b`, any submatrix of
the same or bigger size (possibly with repeated rows or columns) is also.
-/
lemma IsDetpBalanced.submatrix_of_card_le {a b : R} (h : A.IsDetpBalanced a b)
    (le : Fintype.card n ≤ Fintype.card m) (f g : m → n) :
    (A.submatrix f g).IsDetpBalanced a b := by
  by_cases hf : f.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hf
    exact .of_eq (detp_eq_of_row_eq ne <| by ext; simp [eq])
  by_cases hg : g.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hg
    exact .of_eq (detp_eq_of_col_eq ne <| by ext; simp [eq])
  let f' := Equiv.ofBijective f <| (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf, (Fintype.card_le_of_injective f hf).antisymm le⟩
  let g' := Equiv.ofBijective g <| (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hg, (Fintype.card_le_of_injective g hg).antisymm le⟩
  rwa [show f = f' by rfl, show g = g' by rfl, isDetpBalanced_submatrix_equiv_iff]

variable (A)

/-- The adjugate matrix, but only the terms of a given sign. -/
/-
**Matrix.adjp** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：adjp : Matrix n n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjugate matrix, but only the terms of a given sign.
-/
def adjp : Matrix n n R :=
  of fun i j ↦ ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k)
/-
**Matrix.adjp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：adjp_apply (i j : n) : adjp s A i j = ∑ σ in (ofSign s).filter (· j = i), 
∏ k in {j}ᶜ, A k (σ k)
参数：i j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adjp_apply (i j : n) :
    adjp s A i j = ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k) :=
  rfl
/-
**Matrix.adjp_transpose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：adjp_transpose : A.transpose.adjp s = (A.adjp s).transpose
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma adjp_transpose : A.transpose.adjp s = (A.adjp s).transpose :=
  ext fun _ _ ↦ sum_equiv (.inv _) (by aesop) fun σ hσ ↦ prod_equiv σ (by aesop) (by simp)
/-
**Matrix.adjp_none_right** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma adjp_none_right (A : Matrix (Option n) (Option n) R) (i : Option n) :
    A.adjp s i none = (A.submatrix some <| swap none i ∘ some).detp (sign (swap none i) * s) := by
  rw [adjp, of_apply, detp]
  convert sum_image (g := fun σ ↦ decomposeOption.symm (i, σ))
    ((Equiv.injective _).comp (Prod.mk_right_injective i)).injOn
  · ext σ; simp only [mem_filter, mem_ofSign, mem_image]
    exact ⟨fun _ ↦ ⟨σ.removeNone, by rw [← optionCongr_sign]; aesop⟩, by aesop⟩
  convert (prod_image (Option.some_injective n).injOn).symm
  · rfl
  · apply SetLike.coe_injective; simp [← Set.compl_range_some]
/-
**Matrix.adjp_none_none** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：adjp_none_none (A : Matrix (Option n) (Option n) R) : A.adjp s none none =
 (A.submatrix some some).detp s
参数：A : Matrix (Option n) (Option n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.SemiringInverse.0.Matrix.adjp_none
_right`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq
 n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix (Option n) (Opt…
· 使用定理 `Matrix.detp.congr_simp`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype 
n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : CommSemiring R]
 (s s_1 : ℤˣ…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjp_none_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s none none = (A.submatrix some some).detp s := by
  simp [adjp_none_right]
/-
**Matrix.adjp_some_none** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：adjp_some_none (A : Matrix (Option n) (Option n) R) : A.adjp s (some i) no
ne = (A.submatrix some (Function.update some i none)).detp (-s)
参数：A : Matrix (Option n) (Option n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.SemiringInverse.0.Matrix.adjp_none
_right`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq
 n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix (Option n) (Opt…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
lemma adjp_some_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s (some i) none = (A.submatrix some (Function.update some i none)).detp (-s) := by
  rw [adjp_none_right]; congr
  · simp
  · ext1; aesop
/-
**Matrix.adjp_none_some** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：adjp_none_some (A : Matrix (Option n) (Option n) R) : A.adjp s none (some 
i) = (A.submatrix (Function.update some i none) some).detp (-s)
参数：A : Matrix (Option n) (Option n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.detp_transpose`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n
] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n 
R), Matrix.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.detp.congr_simp`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype 
n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : CommSemiring R]
 (s s_1 : ℤˣ…
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用引理 `Matrix.adjp_some_none`：adjp_some_none (A : Matrix (Option n) (Option n) 
R) : A.adjp s (some i) none = (A.submatrix some (Function.update some i none)).d
etp (-s)
· 使用引理 `Matrix.adjp_transpose`：adjp_transpose : A.transpose.adjp s = (A.adjp s).
transpose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjp_none_some (A : Matrix (Option n) (Option n) R) :
    A.adjp s none (some i) = (A.submatrix (Function.update some i none) some).detp (-s) := by
  rw [← detp_transpose]; simp [← A.transpose.adjp_some_none, adjp_transpose]
/-
**Matrix.detp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：detp_mul : detp 1 (A * B) + (detp 1 A * detp (-1) B + detp (-1) A * detp 1
 B) = detp (-1) (A * B) + (detp 1 A * detp 1 B + detp (-1) A * detp (-1) B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mulRightEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsRig
htCancelMul G] (g h : G), (mulRightEmbedding g) h = h * g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Equiv.Perm.mem_ofSign`：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign 
s ↔ σ.sign = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Equiv.coe_fn_injective`：coe_fn_injective : @Function.Injective (α ≃ β) (
α -> β) (fun e => e)
· 使用引理 `Equiv.Perm.ofSign_disjoint`：ofSign_disjoint : _root_.Disjoint (ofSign 1 
: Finset (Perm α)) (ofSign (-1))
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.prod_univ_sum`：prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : fo
rall i, Finset (κ i)) (f : forall i, κ i -> R) : ∏ i, ∑ j in t i, f i j = ∑ x in
 piFinset …
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Finset.sum_compl_add_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
（共 50 条，此处仅展示前 30 条）
-/
theorem detp_mul :
    detp 1 (A * B) + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) =
      detp (-1) (A * B) + (detp 1 A * detp 1 B + detp (-1) A * detp (-1) B) := by
  have hf {s t} {σ : Perm n} (hσ : σ ∈ ofSign s) :
      ofSign (t * s) = (ofSign t).map (mulRightEmbedding σ) := by
    ext τ
    simp_rw [mem_map, mulRightEmbedding_apply, ← eq_mul_inv_iff_mul_eq, exists_eq_right,
      mem_ofSign, map_mul, map_inv, mul_inv_eq_iff_eq_mul, mem_ofSign.mp hσ]
  have h {s t} : detp s A * detp t B =
      ∑ σ ∈ ofSign s, ∑ τ ∈ ofSign (t * s), ∏ k, A k (σ k) * B (σ k) (τ k) := by
    simp_rw [detp, sum_mul_sum, prod_mul_distrib]
    refine sum_congr rfl fun σ hσ ↦ ?_
    simp_rw [hf hσ, sum_map, mulRightEmbedding_apply, Perm.mul_apply]
    exact sum_congr rfl fun τ hτ ↦ (congr_arg (_ * ·) (Equiv.prod_comp σ _).symm)
  let ι : Perm n ↪ (n → n) := ⟨_, coe_fn_injective⟩
  have hι {σ x} : ι σ x = σ x := rfl
  let bij : Finset (n → n) := (disjUnion (ofSign 1) (ofSign (-1)) ofSign_disjoint).map ι
  replace h (s) : detp s (A * B) =
      ∑ σ ∈ bijᶜ, ∑ τ ∈ ofSign s, ∏ i : n, A i (σ i) * B (σ i) (τ i) +
        (detp 1 A * detp s B + detp (-1) A * detp (-s) B) := by
    simp_rw [h, neg_mul_neg, mul_one, detp, mul_apply, prod_univ_sum, Fintype.piFinset_univ]
    rw [sum_comm, ← sum_compl_add_sum bij, sum_map, sum_disjUnion]
    simp_rw [hι]
  rw [h, h, neg_neg, add_assoc]
  conv_rhs => rw [add_assoc]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ ↦ ?_) (add_comm _ _)
  replace hσ : ¬ Function.Injective σ := by
    contrapose hσ
    rw [notMem_compl, mem_map, ofSign_disjUnion]
    exact ⟨Equiv.ofBijective σ hσ.bijective_of_finite, mem_univ _, rfl⟩
  obtain ⟨i, j, hσ, hij⟩ := Function.not_injective_iff.mp hσ
  replace hσ k : σ (swap i j k) = σ k := by
    rw [swap_apply_def]
    split_ifs with h h <;> simp only [hσ, h]
  rw [← mul_neg_one, hf (mem_ofSign.mpr (sign_swap hij)), sum_map]
  simp_rw [prod_mul_distrib, mulRightEmbedding_apply, Perm.mul_apply]
  refine sum_congr rfl fun τ hτ ↦ congr_arg (_ * ·) ?_
  rw [← Equiv.prod_comp (swap i j)]
  simp only [hσ]
/-
**Matrix.mul_adjp_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_adjp_apply_eq : (A * adjp s A) i i = detp s A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_fiberwise_eq_sum_filter`：∀ {ι : Type u_1} {κ : Type u_2} {M :
 Type u_4} [inst : AddCommMonoid M] [inst_1 : DecidableEq κ] (s : Finset ι)   (t
 : Finset κ) (g : ι → κ)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Finset.prod_mul_prod_compl`：prod_mul_prod_compl [Fintype ι] [DecidableEq
 ι] (s : Finset ι) (f : ι -> M) : (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem mul_adjp_apply_eq : (A * adjp s A) i i = detp s A := by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) univ (· i) fun σ ↦ ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_true] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun σ hσ ↦ ?_
  rw [← prod_mul_prod_compl ({i} : Finset n), prod_singleton, (mem_filter.mp hσ).2]
/-
**Matrix.mul_adjp_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_adjp_apply_ne (h : i != j) : (A * adjp 1 A) i j = (A * adjp (-1) A) i 
j
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.mul_adjp_apply_eq`：mul_adjp_apply_eq : (A * adjp s A) i i = detp 
s A
· 使用引理 `Matrix.detp_eq_of_row_eq`：detp_eq_of_row_eq {p q : n} (hpq : p != q) (hr
ow : A.row p = A.row q) (s : Intˣ
-/
theorem mul_adjp_apply_ne (h : i ≠ j) : (A * adjp 1 A) i j = (A * adjp (-1) A) i j := by
  let A' : Matrix n n R := A.updateRow j (A i)
  have h' s : (A * adjp s A) i j = (A' * adjp s A') j j := sum_congr rfl fun _ _ ↦
    congr_arg₂ (· * ·) (by simp [A']) <| sum_congr rfl fun σ hσ ↦ prod_congr rfl fun _ _ ↦ by aesop
  simp_rw [h', mul_adjp_apply_eq]
  apply detp_eq_of_row_eq h
  simp [A', Matrix.row_apply', h]
/-
**Matrix.adjp_mul_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjp_mul_apply_eq : (adjp s A * A) i i = detp s A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.detp_transpose`：∀ {n : Type u_1} {R : Type u_3} [inst : Fintype n
] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] (s : ℤˣ)   (A : Matrix n n 
R), Matrix.…
· 使用定理 `Matrix.mul_adjp_apply_eq`：mul_adjp_apply_eq : (A * adjp s A) i i = detp 
s A
· 使用引理 `Matrix.adjp_transpose`：adjp_transpose : A.transpose.adjp s = (A.adjp s).
transpose
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
-/
theorem adjp_mul_apply_eq : (adjp s A * A) i i = detp s A := by
  rw [← detp_transpose, ← mul_adjp_apply_eq _ _ i, adjp_transpose, ← transpose_mul, transpose_apply]
/-
**Matrix.adjp_mul_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjp_mul_apply_ne (h : i != j) : (adjp 1 A * A) i j = (adjp (-1) A * A) i 
j
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_adjp_apply_ne`：mul_adjp_apply_ne (h : i != j) : (A * adjp 1 A
) i j = (A * adjp (-1) A) i j
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjp_mul_apply_ne (h : i ≠ j) : (adjp 1 A * A) i j = (adjp (-1) A * A) i j := by
  simp_rw [← transpose_apply (_ * _) j i, transpose_mul,
    ← adjp_transpose, mul_adjp_apply_ne _ _ _ h.symm]
/-
**Matrix.mul_adjp_add_detp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_adjp_add_detp : A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + det
p 1 A • 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_adjp_apply_eq`：mul_adjp_apply_eq : (A * adjp s A) i i = detp 
s A
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.mul_adjp_apply_ne`：mul_adjp_apply_ne (h : i != j) : (A * adjp 1 A
) i j = (A * adjp (-1) A) i j
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_adjp_add_detp : A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

/-- Laplace expansion of `detp` along the `none` row of an `Option`-indexed matrix. -/
/-
**Matrix.detp_option_expand_row_none** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：detp_option_expand_row_none (A : Matrix (Option n) (Option n) R) : A.detp 
s = A none none * (A.submatrix some some).detp s + ∑ k : n, A none (some k) * (A
.submatrix some (Function.update some k none)).detp (-s)
参数：A : Matrix (Option n) (Option n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_adjp_apply_eq`：mul_adjp_apply_eq : (A * adjp s A) i i = detp 
s A
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
· 使用引理 `Matrix.adjp_none_none`：adjp_none_none (A : Matrix (Option n) (Option n) 
R) : A.adjp s none none = (A.submatrix some some).detp s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Matrix.adjp_some_none`：adjp_some_none (A : Matrix (Option n) (Option n) 
R) : A.adjp s (some i) none = (A.submatrix some (Function.update some i none)).d
etp (-s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Laplace expansion of `detp` along the `none` row of an `Option`-indexed matrix.
-/
lemma detp_option_expand_row_none (A : Matrix (Option n) (Option n) R) :
    A.detp s = A none none * (A.submatrix some some).detp s +
      ∑ k : n, A none (some k) * (A.submatrix some (Function.update some k none)).detp (-s) := by
  simp_rw [← A.mul_adjp_apply_eq s none, mul_apply,
    Fintype.sum_option, adjp_none_none, adjp_some_none]

variable {A B}
/-
**Matrix.isAddUnit_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isAddUnit_mul {d : n -> R} (hAB : A * B = diagonal d) (i j k : n) (hij : i
 != j) : IsAddUnit (A i k * B k j)
参数：hAB : A * B = diagonal d；i j k : n；hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAddUnit.sum_univ_iff`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype 
ι] [inst_1 : AddCommMonoid M] {f : ι → M},   IsAddUnit (∑ a, f a) ↔ ∀ (a : ι), I
sAddUnit (f …
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `isAddUnit_zero`：∀ {M : Type u_1} [inst : AddMonoid M], IsAddUnit 0
-/
theorem isAddUnit_mul {d : n → R} (hAB : A * B = diagonal d) (i j k : n) (hij : i ≠ j) :
    IsAddUnit (A i k * B k j) := by
  revert k
  rw [← IsAddUnit.sum_univ_iff, ← mul_apply, hAB, diagonal_apply_ne _ hij]
  exact isAddUnit_zero
/-
**Matrix.isAddUnit_detp_mul_detp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isAddUnit_detp_mul_detp {d : n -> R} (hAB : A * B = diagonal d) : IsAddUni
t (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B)
参数：hAB : A * B = diagonal d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用引理 `Equiv.Perm.mem_ofSign`：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign 
s ↔ σ.sign = s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_inv_iff_mul_eq_one`：eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `IsAddUnit.smul_right`：IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUni
t (r • x)
· 使用定理 `Matrix.isAddUnit_mul`：isAddUnit_mul {d : n -> R} (hAB : A * B = diagonal
 d) (i j k : n) (hij : i != j) : IsAddUnit (A i k * B k j)
· 使用定理 `IsAddUnit.add`：∀ {M : Type u_1} [inst : AddMonoid M] {a b : M}, IsAddUni
t a → IsAddUnit b → IsAddUnit (a + b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem isAddUnit_detp_mul_detp {d : n → R} (hAB : A * B = diagonal d) :
    IsAddUnit (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) := by
  suffices h : ∀ {s t}, s ≠ t → IsAddUnit (detp s A * detp t B) from
    (h (by decide)).add (h (by decide))
  intro s t h
  simp_rw [detp, sum_mul_sum, IsAddUnit.sum_iff]
  intro σ hσ τ hτ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ, ← hτ, ← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq, eq_comm, eq_inv_iff_mul_eq_one, eq_comm] at h
  simp_rw [Equiv.ext_iff, not_forall, Perm.mul_apply, Perm.one_apply] at h
  obtain ⟨k, hk⟩ := h
  rw [mul_comm, ← Equiv.prod_comp σ, mul_comm, ← prod_mul_distrib,
    ← mul_prod_erase univ _ (mem_univ k), ← smul_eq_mul]
  exact (isAddUnit_mul hAB k (τ (σ k)) (σ k) hk).smul_right _
/-
**Matrix.isAddUnit_detp_smul_mul_adjp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isAddUnit_detp_smul_mul_adjp {d : n -> R} (hAB : A * B = diagonal d) : IsA
ddUnit (detp 1 A • (B * adjp (-1) B) + detp (-1) A • (B * adjp 1 B))
参数：hAB : A * B = diagonal d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isAddUnit_iff`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst
 : AddMonoid α] {A : Matrix m n α},   IsAddUnit A ↔ ∀ (i : m) (j : n), IsAddUnit
 (A i j)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用引理 `Equiv.Perm.mem_ofSign`：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign 
s ↔ σ.sign = s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用引理 `Finset.exists_mem_ne`：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in 
s, b != a
· 使用定理 `Equiv.Perm.one_lt_card_support_of_ne_one`：one_lt_card_support_of_ne_one 
{f : Perm α} (h : f != 1) : 1 < #f.support
· 使用定理 `eq_inv_iff_mul_eq_one`：eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Finset.prod_mul_prod_compl`：prod_mul_prod_compl [Fintype ι] [DecidableEq
 ι] (s : Finset ι) (f : ι -> M) : (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `IsAddUnit.smul_right`：IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUni
t (r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
（共 39 条，此处仅展示前 30 条）
-/
theorem isAddUnit_detp_smul_mul_adjp {d : n → R} (hAB : A * B = diagonal d) :
    IsAddUnit (detp 1 A • (B * adjp (-1) B) + detp (-1) A • (B * adjp 1 B)) := by
  suffices h : ∀ {s t}, s ≠ t → IsAddUnit (detp s A • (B * adjp t B)) from
    (h (by decide)).add (h (by decide))
  intro s t h
  rw [isAddUnit_iff]
  intro i j
  simp_rw [smul_apply, smul_eq_mul, mul_apply, detp, adjp_apply, mul_sum, sum_mul,
    IsAddUnit.sum_iff]
  intro k hk σ hσ τ hτ
  rw [mem_filter] at hσ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ.1, ← hτ, ← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq, eq_comm, eq_inv_iff_mul_eq_one] at h
  obtain ⟨l, hl1, hl2⟩ := exists_mem_ne (one_lt_card_support_of_ne_one h) (τ⁻¹ j)
  rw [mem_support, ne_comm] at hl1
  rw [ne_eq, ← mem_singleton, ← mem_compl] at hl2
  rw [← prod_mul_prod_compl {τ⁻¹ j}, mul_mul_mul_comm, mul_comm, ← smul_eq_mul]
  apply IsAddUnit.smul_right
  have h0 : ∀ k, k ∈ ({τ⁻¹ j} : Finset n)ᶜ ↔ τ k ∈ ({j} : Finset n)ᶜ := by
    simp [inv_def, eq_symm_apply]
  rw [← prod_equiv τ h0 fun _ _ ↦ rfl, ← prod_mul_distrib, ← mul_prod_erase _ _ hl2, ← smul_eq_mul]
  exact (isAddUnit_mul hAB l (σ (τ l)) (τ l) hl1).smul_right _
/-
**Matrix.detp_smul_add_adjp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：detp_smul_add_adjp (hAB : A * B = 1) : detp 1 B • A + adjp (-1) B = detp (
-1) B • A + adjp 1 B
参数：hAB : A * B = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_adjp_add_detp`：mul_adjp_add_detp : A * adjp 1 A + detp (-1) A
 • 1 = A * adjp (-1) A + detp 1 A • 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem detp_smul_add_adjp (hAB : A * B = 1) :
    detp 1 B • A + adjp (-1) B = detp (-1) B • A + adjp 1 B := by
  have key := congr(A * $(mul_adjp_add_detp B))
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, Matrix.mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]
/-
**Matrix.detp_smul_adjp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：detp_smul_adjp (hAB : A * B = 1) : A + (detp 1 A • adjp (-1) B + detp (-1)
 A • adjp 1 B) = detp 1 A • adjp 1 B + detp (-1) A • adjp (-1) B
参数：hAB : A * B = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.detp_mul`：detp_mul : detp 1 (A * B) + (detp 1 A * detp (-1) B + d
etp (-1) A * detp 1 B) = detp (-1) (A * B) + (detp 1 A * detp 1 B + detp (-1) A 
* det…
· 使用定理 `Matrix.detp_smul_add_adjp`：detp_smul_add_adjp (hAB : A * B = 1) : detp 1
 B • A + adjp (-1) B = detp (-1) B • A + adjp 1 B
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAddUnit.add_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] {a b c : 
M}, IsAddUnit a → (a + b = a + c ↔ b = c)
· 使用引理 `IsAddUnit.smul_right`：IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUni
t (r • x)
· 使用定理 `Matrix.isAddUnit_detp_mul_detp`：isAddUnit_detp_mul_detp {d : n -> R} (hA
B : A * B = diagonal d) : IsAddUnit (detp 1 A * detp (-1) B + detp (-1) A * detp
 1 B)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Matrix.detp_neg_one_one`：detp_neg_one_one : detp (-1) (1 : Matrix n n R)
 = 0
· 使用引理 `Matrix.detp_one_one`：detp_one_one : detp 1 (1 : Matrix n n R) = 1
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
theorem detp_smul_adjp (hAB : A * B = 1) :
    A + (detp 1 A • adjp (-1) B + detp (-1) A • adjp 1 B) =
      detp 1 A • adjp 1 B + detp (-1) A • adjp (-1) B := by
  have h0 := detp_mul A B
  rw [hAB, detp_one_one, detp_neg_one_one, zero_add] at h0
  have h := detp_smul_add_adjp hAB
  replace h := congr(detp 1 A • $h + detp (-1) A • $h.symm)
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, ((isAddUnit_detp_mul_detp hAB).smul_right _).add_right_inj] at h
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) instIsStablyFiniteRingOfCommSemiring : IsStablyFiniteRing R := by
  refine ⟨fun n ↦ ⟨fun {A B} hAB ↦ ?_⟩⟩
  have h0 := detp_mul A B
  rw [hAB, detp_one_one, detp_neg_one_one, zero_add] at h0
  replace h := congr(B * $(detp_smul_adjp hAB))
  simp only [mul_add, Matrix.mul_smul] at h
  replace h := congr($h + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) • 1)
  simp_rw [add_smul, ← smul_smul] at h
  rwa [add_assoc, add_add_add_comm, ← smul_add, ← smul_add,
    add_add_add_comm, ← smul_add, ← smul_add, smul_add, smul_add,
    mul_adjp_add_detp, smul_add, ← mul_adjp_add_detp, smul_add, ← smul_add, ← smul_add,
    add_add_add_comm, smul_smul, smul_smul, ← add_smul, ← h0,
    add_smul, one_smul, ← add_assoc _ 1, add_comm _ 1, add_assoc,
    smul_add, smul_add, add_add_add_comm, smul_smul, smul_smul, ← add_smul,
    ((isAddUnit_detp_smul_mul_adjp hAB).add
      ((isAddUnit_detp_mul_detp hAB).smul_right _)).add_left_inj] at h

end Matrix

