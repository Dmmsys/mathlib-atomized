/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Slava Naprienko
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `Matrix.charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `Matrix.det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `Matrix.trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th
  coefficient of the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.
- `Matrix.coeff_det_one_add_X_smul_eq_sum_minors` proves that the k-th coefficient of
  `det (1 + X • M)` equals the sum of all k×k principal minors of M.
- `Matrix.charpoly_coeff_eq_sum_minors` expresses the coefficients of the characteristic
  polynomial as signed sums of principal minors.
- `Matrix.charpolyRev` the reverse of the characteristic polynomial.
- `Matrix.reverse_charpoly` characterises the reverse of the characteristic polynomial.

-/

@[expose] public section


noncomputable section

universe u v w z

open Finset Matrix Polynomial
open scoped Ring

variable {R : Type u} [CommRing R]
variable {n G : Type v} [DecidableEq n] [Fintype n]
variable {α β : Type v} [DecidableEq α]
variable {M : Matrix n n R}

namespace Matrix

/-
**Matrix.charmatrix_apply_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_apply_natDegree [Nontrivial R] (i j : n) : (charmatrix M i j).n
atDegree = ite (i = j) 1 0
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charmatrix.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : 
Type u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype 
n] (M M_1 : Matrix…
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.charmatrix_apply_ne`：charmatrix_apply_ne (h : i != j) : charmatri
x M i j = -C (M i j)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem charmatrix_apply_natDegree [Nontrivial R] (i j : n) :
    (charmatrix M i j).natDegree = ite (i = j) 1 0 := by
  by_cases h : i = j <;> simp [h]
/-
**Matrix.charmatrix_apply_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_apply_natDegree_le (i j : n) : (charmatrix M i j).natDegree <= 
ite (i = j) 1 0
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charmatrix.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : 
Type u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype 
n] (M M_1 : Matrix…
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Matrix.charmatrix_apply_ne`：charmatrix_apply_ne (h : i != j) : charmatri
x M i j = -C (M i j)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
-/
theorem charmatrix_apply_natDegree_le (i j : n) :
    (charmatrix M i j).natDegree ≤ ite (i = j) 1 0 := by
  split_ifs with h <;> simp [h, natDegree_X_le]

variable (M)
/-
**Matrix.charpoly_sub_diagonal_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_sub_diagonal_degree_lt : (M.charpoly - ∏ i : n, (X - C (M i i))).
degree < ↑(Fintype.card n - 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Polynomial.C_eq_intCast`：C_eq_intCast (n : Int) : C (n : R) = n
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.natDegree_prod_le`：natDegree_prod_le : (∏ i in s, f i).natDeg
ree <= ∑ i in s, (f i).natDegree
（共 36 条，此处仅展示前 30 条）
-/
theorem charpoly_sub_diagonal_degree_lt :
    (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1) := by
  rw [charpoly, det_apply', ← insert_erase (mem_univ (Equiv.refl n)),
    sum_insert (notMem_erase (Equiv.refl n) univ), add_comm]
  simp only [charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id, Int.cast_one,
    Units.val_one, add_sub_cancel_right, Equiv.coe_refl]
  rw [← mem_degreeLT]
  apply Submodule.sum_mem (degreeLT R (Fintype.card n - 1))
  intro c hc; rw [← C_eq_intCast, C_mul']
  apply Submodule.smul_mem (degreeLT R (Fintype.card n - 1)) ↑↑(Equiv.Perm.sign c)
  rw [mem_degreeLT]
  apply lt_of_le_of_lt degree_le_natDegree _
  rw [Nat.cast_lt]
  apply lt_of_le_of_lt _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  apply le_trans (Polynomial.natDegree_prod_le univ fun i : n => charmatrix M (c i) i) _
  rw [card_eq_sum_ones]; rw [sum_filter]; apply sum_le_sum
  intros
  apply charmatrix_apply_natDegree_le
/-
**Matrix.charpoly_coeff_eq_prod_coeff_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_coeff_eq_prod_coeff_of_le {k : Nat} (h : Fintype.card n - 1 <= k)
 : M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k
参数：h : Fintype.card n - 1 <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Matrix.charpoly_sub_diagonal_degree_lt`：charpoly_sub_diagonal_degree_lt 
: (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1)
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : Fintype.card n - 1 ≤ k) :
    M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k := by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  rw [Nat.cast_le]; apply h

@[simp]
/-
**Matrix.charpoly_degree_eq_dim** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) : M.charpoly.degr
ee = Fintype.card n
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_eq_one_of_card_eq_zero`：det_eq_one_of_card_eq_zero {A : Matri
x n n R} (h : Fintype.card n = 0) : det A = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq_of_pos`：degree_eq_iff_natDegree_eq
_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Polynomial.natDegree_prod'`：natDegree_prod' (h : (∏ i in s, (f i).leadin
gCoeff) != 0) : (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Matrix.charpoly_sub_diagonal_degree_lt`：charpoly_sub_diagonal_degree_lt 
: (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1)
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n, (X - C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degree = ↑(Fintype.card n) := by
    rw [degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h), natDegree_prod']
    · simp_rw [natDegree_X_sub_C]
      rw [← Finset.card_univ, sum_const, smul_eq_mul, mul_one]
    simp_rw [(monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  · exact h1
  rw [h1]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia
/-
**Matrix.charpoly_natDegree_eq_dim** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : Type v} [inst_1 : DecidableEq n] [
inst_2 : Fintype n] [Nontrivial R]   (M : Matrix n n R), M.charpoly.natDegree = 
Fintype.card n
参数：M : Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Matrix.charpoly_degree_eq_dim`：charpoly_degree_eq_dim [Nontrivial R] (M 
: Matrix n n R) : M.charpoly.degree = Fintype.card n
-/
@[simp] theorem charpoly_natDegree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.natDegree = Fintype.card n :=
  natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)
/-
**Matrix.charpoly_monic** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_monic (M : Matrix n n R) : M.charpoly.Monic
参数：M : Matrix n n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用定理 `Matrix.det_eq_one_of_card_eq_zero`：det_eq_one_of_card_eq_zero {A : Matri
x n n R} (h : Fintype.card n = 0) : det A = 1
· 使用定理 `Polynomial.monic_one`：monic_one : Monic (1 : R[X])
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
· 使用定理 `Matrix.charpoly_degree_eq_dim`：charpoly_degree_eq_dim [Nontrivial R] (M 
: Matrix n n R) : M.charpoly.degree = Fintype.card n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Matrix.charpoly_sub_diagonal_degree_lt`：charpoly_sub_diagonal_degree_lt 
: (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1)
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_eq_one_of_card_eq_zero h]
    apply monic_one
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, (X - C (M i i))) M.charpoly] at mon
  rw [Monic] at *
  rwa [leadingCoeff_add_of_degree_lt] at mon
  rw [charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [degree_neg]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

/-- See also `Matrix.coeff_charpolyRev_eq_neg_trace`. -/
/-
**Matrix.trace_eq_neg_charpoly_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) : trace M = -M
.charpoly.coeff (Fintype.card n - 1)
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly_coeff_eq_prod_coeff_of_le`：charpoly_coeff_eq_prod_coeff_
of_le {k : Nat} (h : Fintype.card n - 1 <= k) : M.charpoly.coeff k = (∏ i : n, (
X - C (M i i))).coeff k
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用定理 `Polynomial.prod_X_sub_C_coeff_card_pred`：prod_X_sub_C_coeff_card_pred (s
 : Finset ι) (f : ι -> R) (hs : 0 < #s) : (∏ i in s, (X - C (f i))).coeff (#s - 
1) = -∑ i in s, f i
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Matrix.trace.eq_1`：∀ {n : Type u_3} {R : Type u_6} [inst : Fintype n] [i
nst_1 : AddCommMonoid R] (A : Matrix n n R),   A.trace = ∑ i, A.diag i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `Matrix.coeff_charpolyRev_eq_neg_trace`.
-/
theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl, Fintype.card,
    prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos, neg_neg, trace]
  simp_rw [diag_apply]
/-
**Matrix.trace_eq_neg_charpoly_nextCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_eq_neg_charpoly_nextCoeff (M : Matrix n n R) : M.trace = -M.charpoly
.nextCoeff
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.trace_eq_zero_of_isEmpty`：trace_eq_zero_of_isEmpty [IsEmpty n] (A
 : Matrix n n R) : trace A = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charpoly_isEmpty`：charpoly_isEmpty [IsEmpty n] {A : Matrix n n R}
 : charpoly A = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Matrix.trace_eq_neg_charpoly_coeff`：trace_eq_neg_charpoly_coeff [Nonempt
y n] (M : Matrix n n R) : trace M = -M.charpoly.coeff (Fintype.card n - 1)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
-/
theorem trace_eq_neg_charpoly_nextCoeff (M : Matrix n n R) : M.trace = -M.charpoly.nextCoeff := by
  cases isEmpty_or_nonempty n
  · simp [nextCoeff]
  nontriviality
  simp [trace_eq_neg_charpoly_coeff, nextCoeff]
/-
**Matrix.det_eq_sign_charpoly_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_sign_charpoly_coeff (M : Matrix n n R) : M.det = (-1) ^ Fintype.car
d n * M.charpoly.coeff 0
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用定理 `eval_det`：eval_det {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R
) : Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).…
· 使用定理 `Matrix.matPolyEquiv_charmatrix`：matPolyEquiv_charmatrix : matPolyEquiv (
charmatrix M) = X - C M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) :
    M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, matPolyEquiv_charmatrix, ← det_smul]
  simp
/-
**Matrix.derivative_det_one_add_X_smul_aux** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：derivative_det_one_add_X_smul_aux {n} (M : Matrix (Fin n) (Fin n) R) : (de
rivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M
参数：M : Matrix (Fin n) (Fin n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_zero`：det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A
 = 1
· 使用定理 `Polynomial.derivative_one`：derivative_one : derivative (1 : R[X]) = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用引理 `Matrix.trace_eq_zero_of_isEmpty`：trace_eq_zero_of_isEmpty [IsEmpty n] (A
 : Matrix n n R) : trace A = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_succ_row_zero`：det_succ_row_zero {n : Nat} (A : Matrix (Fin n
.succ) (Fin n.succ) R) : det A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * de
t (A.submatrix…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.X_mul_C`：X_mul_C (r : R) : X * C r = C r * X
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
（共 65 条，此处仅展示前 30 条）
-/
lemma derivative_det_one_add_X_smul_aux {n} (M : Matrix (Fin n) (Fin n) R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero, map_sum, eval_finsetSum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
      derivative_C, zero_mul, derivative_X, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_det_add_X_smul, eval_pow, eval_neg, eval_one]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, derivative_one, eval_zero, one_apply_eq, eval_one,
        mul_one, zero_add, one_mul, Fin.succAbove_zero, submatrix_one _ (Fin.succ_injective _),
        det_one, IH, trace_submatrix_succ]
    · intro i _ hi
      cases n with
      | zero => exact (hi (Subsingleton.elim i 0)).elim
      | succ n =>
        simp only [one_apply_ne' hi, eval_zero, mul_zero, zero_add, zero_mul, add_zero]
        rw [det_eq_zero_of_column_eq_zero 0, eval_zero, mul_zero]
        intro j
        rw [submatrix_apply, Fin.succAbove_of_castSucc_lt, one_apply_ne]
        · exact (bne_iff_ne (a := Fin.succ j) (b := Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H ↦ (H <| Finset.mem_univ _).elim

/-- The derivative of `det (1 + M X)` at `0` is the trace of `M`. -/
/-
**Matrix.derivative_det_one_add_X_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：derivative_det_one_add_X_smul (M : Matrix n n R) : (derivative <| det (1 +
 (X : R[X]) • M.map C)).eval 0 = trace M
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_reindexLinearEquiv_self`：det_reindexLinearEquiv_self [CommRin
g R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (M : Ma
trix m m R) : det (reind…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Matrix.submatrix_one_equiv`：submatrix_one_equiv [Zero α] [One α] [Decida
bleEq m] [DecidableEq l] (e : l ≃ m) : (1 : Matrix m m α).submatrix e e = 1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Polynomial.X_mul_C`：X_mul_C (r : R) : X * C r = C r * X
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Matrix.derivative_det_one_add_X_smul_aux`：derivative_det_one_add_X_smul_
aux {n} (M : Matrix (Fin n) (Fin n) R) : (derivative <| det (1 + (X : R[X]) • M.
map C)).eval 0 = trace M

--- 原说明 ---
The derivative of `det (1 + M X)` at `0` is the trace of `M`.
-/
lemma derivative_det_one_add_X_smul (M : Matrix n n R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert! derivative_det_one_add_X_smul_aux (e M)
  · ext; simp [map_add, e]
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    simp_rw [e, coe_reindexLinearEquiv, reindex_apply, diag_apply, submatrix_apply]
/-
**Matrix.coeff_det_one_add_X_smul_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：coeff_det_one_add_X_smul_one (M : Matrix n n R) : (det (1 + (X : R[X]) • M
.map C)).coeff 1 = trace M
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_derivative`：coeff_derivative (p : R[X]) (n : Nat) : coe
ff (derivative p) n = coeff p (n + 1) * (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_det_one_add_X_smul_one (M : Matrix n n R) :
    (det (1 + (X : R[X]) • M.map C)).coeff 1 = trace M := by
  simp only [← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, Nat.cast_zero, mul_one]
/-
**Matrix.det_one_add_X_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：det_one_add_X_smul (M : Matrix n n R) : det (1 + (X : R[X]) • M.map C) = (
1 : R[X]) + trace M • X + (det (1 + (X : R[X]) • M.map C)).divX.divX * X ^ 2
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_algebraMap`：C_eq_algebraMap (r : R) : C r = algebraMap R
 R[X] r
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `Matrix.coeff_det_one_add_X_smul_one`：coeff_det_one_add_X_smul_one (M : M
atrix n n R) : (det (1 + (X : R[X]) • M.map C)).coeff 1 = trace M
· 使用定理 `Polynomial.coeff_divX`：coeff_divX : (divX p).coeff n = p.coeff (n + 1)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.divX_mul_X_add`：divX_mul_X_add (p : R[X]) : divX p * X + C (p
.coeff 0) = p
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用引理 `eval_det_add_X_smul`：eval_det_add_X_smul {R : Type*} [CommRing R] (A : M
atrix n n R[X]) (M : Matrix n n R) : (det (A + (X : R[X]) • M.map C)).eval 0 = (
det A).ev…
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
-/
lemma det_one_add_X_smul (M : Matrix n n R) :
    det (1 + (X : R[X]) • M.map C) =
      (1 : R[X]) + trace M • X + (det (1 + (X : R[X]) • M.map C)).divX.divX * X ^ 2 := by
  rw [Algebra.smul_def (trace M), ← C_eq_algebraMap, pow_two, ← mul_assoc, add_assoc,
    ← add_mul, ← coeff_det_one_add_X_smul_one, ← coeff_divX, add_comm (C _), divX_mul_X_add,
    add_comm (1 : R[X]), ← C.map_one]
  convert! (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]

/-- The first two terms of the Taylor expansion of `det (1 + r • M)` at `r = 0`. -/
/-
**Matrix.det_one_add_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：det_one_add_smul (r : R) (M : Matrix n n R) : det (1 + r • M) = 1 + trace 
M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2
参数：r : R；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eval_det`：eval_det {R : Type*} [CommRing R] (M : Matrix n n R[X]) (r : R
) : Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).…
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `matPolyEquiv_map_smul`：matPolyEquiv_map_smul (p : R[X]) (M : Matrix n n 
R[X]) : matPolyEquiv (p • M) = p.map (algebraMap _ _) * matPolyEquiv M
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `matPolyEquiv_map_C`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type w
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEqu
iv (M.ma…
· 使用定理 `Polynomial.X_mul_C`：X_mul_C (r : R) : X * C r = C r * X
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Polynomial.eval_mul_X`：eval_mul_X : (p * X).eval x = p.eval x * x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The first two terms of the Taylor expansion of `det (1 + r • M)` at `r = 0`.
-/
lemma det_one_add_smul (r : R) (M : Matrix n n R) :
    det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)
/-
**Matrix.charpoly_of_card_eq_two** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charpoly_of_card_eq_two [Nontrivial R] (hn : Fintype.card n = 2) : M.charp
oly = X ^ 2 - C M.trace * X + C M.det
参数：hn : Fintype.card n = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_eq_sign_charpoly_coeff`：det_eq_sign_charpoly_coeff (M : Matri
x n n R) : M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Matrix.trace_eq_neg_charpoly_coeff`：trace_eq_neg_charpoly_coeff [Nonempt
y n] (M : Matrix n n R) : trace M = -M.charpoly.coeff (Fintype.card n - 1)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
（共 48 条，此处仅展示前 30 条）
-/
lemma charpoly_of_card_eq_two [Nontrivial R] (hn : Fintype.card n = 2) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  have : Nonempty n := by rw [← Fintype.card_pos_iff]; lia
  ext i
  by_cases hi : i ∈ Finset.range 3
  · fin_cases hi
    · simp [det_eq_sign_charpoly_coeff, hn]
    · simp [trace_eq_neg_charpoly_coeff, hn]
    · simpa [leadingCoeff, charpoly_natDegree_eq_dim, hn, coeff_X] using
        M.charpoly_monic.leadingCoeff
  · rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hi
    suffices M.charpoly.coeff i = 0 by
      simpa [show i ≠ 2 by lia, show 1 ≠ i by lia, show i ≠ 0 by lia, coeff_X, coeff_C]
    apply coeff_eq_zero_of_natDegree_lt
    simpa [charpoly_natDegree_eq_dim, hn] using hi
/-
**Matrix.charpoly_fin_two** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) : M.charpol
y = X ^ 2 - C M.trace * X + C M.det
参数：M : Matrix (Fin 2) (Fin 2) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.charpoly_of_card_eq_two`：charpoly_of_card_eq_two [Nontrivial R] (
hn : Fintype.card n = 2) : M.charpoly = X ^ 2 - C M.trace * X + C M.det
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
lemma charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det :=
  M.charpoly_of_card_eq_two <| Fintype.card_fin _

end Matrix

/-
**matPolyEquiv_eq_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : Nat) [CommRing K] (M : Matrix
 n n K) : matPolyEquiv ((expand K k : K[X] ->+* K[X]).mapMatrix (charmatrix (M ^
 k))) = X ^ k - C (M ^ k)
参数：k : Nat；M : Matrix n n K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `matPolyEquiv_coeff_apply`：matPolyEquiv_coeff_apply (m : Matrix n n R[X])
 (k : Nat) (i j : n) : coeff (matPolyEquiv m) k i j = coeff (m i j) k
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Matrix.charmatrix_apply_ne`：charmatrix_apply_ne (h : i != j) : charmatri
x M i j = -C (M i j)
（共 37 条，此处仅展示前 30 条）
-/
theorem matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [CommRing K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  ext m i j
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs with mp m0 <;> simp
  · rw [charmatrix_apply_ne _ _ _ hij, map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;> simp_all

namespace Matrix

/-- Any matrix polynomial `p` is equivalent under evaluation to `p %ₘ M.charpoly`; that is, `p`
is equivalent to a polynomial with degree less than the dimension of the matrix. -/
/-
**Matrix.aeval_eq_aeval_mod_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[X]) : aeval M p = ae
val M (p %ₘ M.charpoly)
参数：M : Matrix n n R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_modByMonic_eq_self_of_root`：aeval_modByMonic_eq_self_of
_root [Algebra R S] {p q : R[X]} {x : S} (hx : aeval x q = 0) : aeval x (p %ₘ q)
 = aeval x p
· 使用定理 `Matrix.aeval_self_charpoly`：aeval_self_charpoly (M : Matrix n n R) : aev
al M M.charpoly = 0

--- 原说明 ---
Any matrix polynomial `p` is equivalent under evaluation to `p %ₘ M.charpoly`; t
hat is, `p`
is equivalent to a polynomial with degree less than the dimension of the matrix.
-/
theorem aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[X]) :
    aeval M p = aeval M (p %ₘ M.charpoly) :=
  (aeval_modByMonic_eq_self_of_root M.aeval_self_charpoly).symm

/-- Any matrix power can be computed as the sum of matrix powers less than `Fintype.card n`.

TODO: add the statement for negative powers phrased with `zpow`. -/
/-
**Matrix.pow_eq_aeval_mod_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : Nat) : M ^ k = aeval M (
X ^ k %ₘ M.charpoly)
参数：M : Matrix n n R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.aeval_eq_aeval_mod_charpoly`：aeval_eq_aeval_mod_charpoly (M : Mat
rix n n R) (p : R[X]) : aeval M p = aeval M (p %ₘ M.charpoly)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x

--- 原说明 ---
Any matrix power can be computed as the sum of matrix powers less than `Fintype.
card n`.

TODO: add the statement for negative powers phrased with `zpow`.
-/
theorem pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : ℕ) :
    M ^ k = aeval M (X ^ k %ₘ M.charpoly) := by rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

section Ideal

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.coeff_charpoly_mem_ideal_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coeff_charpoly_mem_ideal_pow {I : Ideal R} (h : forall i j, M i j in I) (k
 : Nat) : M.charpoly.coeff k in I ^ (Fintype.card n - k)
参数：h : forall i j, M i j in I；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Submodule.smul_mem_iff'`：smul_mem_iff' [Group G] [MulAction G M] [SMul G
 R] [IsScalarTower G R M] (g : G) : g • x in p ↔ x in p
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_prod_mem_ideal_pow_tsub`：∀ {R : Type u} [inst : CommSem
iring R] {ι : Type u_2} (s : Finset ι) (f : ι → Polynomial R) (I : Ideal R) (n :
 ι → ℕ),   (∀ i ∈ s, ∀ (k : ℕ)…
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Matrix.charmatrix_apply`：charmatrix_apply : charmatrix M i j = (Matrix.d
iagonal fun _ : n => X) i j - C (M i j)
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Matrix.smul_one_eq_diagonal`：smul_one_eq_diagonal [DecidableEq m] (a : α
) : a • (1 : Matrix m m α) = diagonal fun _ => a
· 使用定理 `Matrix.smul_apply`：smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i :
 m) (j : n) : (r • A) i j = r • (A i j)
· 使用定理 `Polynomial.coeff_X_mul_zero`：coeff_X_mul_zero (p : R[X]) : coeff (X * p)
 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_self_add`：tsub_self_add (a b : α) : a - (a + b) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
（共 31 条，此处仅展示前 30 条）
-/
theorem coeff_charpoly_mem_ideal_pow {I : Ideal R} (h : ∀ i j, M i j ∈ I) (k : ℕ) :
    M.charpoly.coeff k ∈ I ^ (Fintype.card n - k) := by
  delta charpoly
  rw [Matrix.det_apply, finsetSum_coeff]
  apply sum_mem
  rintro c -
  rw [coeff_smul, Submodule.smul_mem_iff']
  have : ∑ x : n, 1 = Fintype.card n := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
  rw [← this]
  apply coeff_prod_mem_ideal_pow_tsub
  rintro i - (_ | k)
  · rw [tsub_zero, pow_one, charmatrix_apply, coeff_sub, ← smul_one_eq_diagonal, smul_apply,
      smul_eq_mul, coeff_X_mul_zero, coeff_C_zero, zero_sub, neg_mem_iff]
    exact h (c i) i
  · rw [add_comm, tsub_self_add, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

end Ideal

section reverse

open LaurentPolynomial hiding C

/-- The reverse of the characteristic polynomial of a matrix.

It has some advantages over the characteristic polynomial, including the fact that it can be
extended to infinite dimensions (for appropriate operators). In such settings it is known as the
"characteristic power series". -/
/-
**Matrix.charpolyRev** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：charpolyRev (M : Matrix n n R) : R[X]
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse of the characteristic polynomial of a matrix.

It has some advantages over the characteristic polynomial, including the fact th
at it can be
extended to infinite dimensions (for appropriate operators). In such settings it
 is known as the
"characteristic power series".
-/
def charpolyRev (M : Matrix n n R) : R[X] := det (1 - (X : R[X]) • M.map C)
/-
**Matrix.reverse_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：reverse_charpoly (M : Matrix n n R) : M.charpoly.reverse = M.charpolyRev
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.T_add`：T_add (m n : Int) : (T (m + n) : R[T;T⁻¹]) = T 
m * T n
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `LaurentPolynomial.T_zero`：T_zero : (T 0 : R[T;T⁻¹]) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `AlgHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintyp
e n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] [in
st_4…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgHom.mapMatrix_apply`：∀ {m : Type u_2} {R : Type u_7} {α : Type u_11} 
{β : Type u_12} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : CommSemi
ring R] [ins…
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.toLaurent_X`：∀ {R : Type u_1} [inst : Semiring R], Polynomial
.toLaurent Polynomial.X = LaurentPolynomial.T 1
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `Polynomial.toLaurent_comp_C`：∀ {R : Type u_1} [inst : Semiring R], ⇑Poly
nomial.toLaurent ∘ ⇑Polynomial.C = ⇑LaurentPolynomial.C
· 使用定理 `Matrix.smul_eq_diagonal_mul`：smul_eq_diagonal_mul [Fintype m] [Decidable
Eq m] (M : Matrix m n α) (a : α) : a • M = (diagonal fun _ => a) * M
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
（共 63 条，此处仅展示前 30 条）
-/
lemma reverse_charpoly (M : Matrix n n R) :
    M.charpoly.reverse = M.charpolyRev := by
  nontriviality R
  let t : R[T;T⁻¹] := T 1
  let t_inv : R[T;T⁻¹] := T (-1)
  let p : R[T;T⁻¹] := det (scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := det (1 - scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  have hp : toLaurentAlg M.charpoly = p := by
    simp [p, t, charpoly, charmatrix, AlgHom.map_det, map_sub]
  have hq : toLaurentAlg M.charpolyRev = q := by
    simp [q, t, charpolyRev, AlgHom.map_det, map_sub, smul_eq_diagonal_mul]
  suffices t_inv ^ Fintype.card n * p = invert q by
    apply toLaurent_injective
    rwa [toLaurent_reverse, ← coe_toLaurentAlg, hp, hq, ← involutive_invert.injective.eq_iff,
      map_mul, involutive_invert p, charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : ℤ), ← T_pow, map_pow, invert_T, mul_comm]
  rw [← det_smul, smul_sub, scalar_apply, ← diagonal_smul, Pi.smul_def, smul_eq_mul, ht,
    diagonal_one, invert.map_det]
  simp [t_inv, map_sub, map_one, map_mul, t, smul_eq_diagonal_mul]
/-
**Matrix.charpoly_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_inv (A : Matrix n n R) (h : IsUnit A) : A⁻¹.charpoly = (-1) ^ Fin
type.card n * C A.det⁻¹ʳ * A.charpolyRev
参数：A : Matrix n n R；h : IsUnit A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.inv_mul_of_invertible`：inv_mul_of_invertible [Invertible A] : A⁻¹
 * A = 1
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_nonsing_inv`：det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_inv_of_invertible`：mul_inv_of_invertible [Invertible A] : A *
 A⁻¹ = 1
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
（共 33 条，此处仅展示前 30 条）
-/
theorem charpoly_inv (A : Matrix n n R) (h : IsUnit A) :
    A⁻¹.charpoly = (-1) ^ Fintype.card n * C A.det⁻¹ʳ * A.charpolyRev := by
  have : Invertible A := h.invertible
  calc
  _ = (scalar n X - C.mapMatrix A⁻¹).det := rfl
  _ = C (A⁻¹ * A).det * (scalar n X - C.mapMatrix A⁻¹).det := by simp
  _ = C A⁻¹.det * C A.det * (scalar n X - C.mapMatrix A⁻¹).det := by rw [det_mul]; simp
  _ = C A⁻¹.det * (C A.det * (scalar n X - C.mapMatrix A⁻¹).det) := by ac_rfl
  _ = C A⁻¹.det * (C.mapMatrix A * (scalar n X - C.mapMatrix A⁻¹)).det := by simp [RingHom.map_det]
  _ = C A⁻¹.det * (C.mapMatrix A * scalar n X - 1).det := by rw [mul_sub, ← map_mul]; simp
  _ = C A⁻¹.det * ((-1) ^ Fintype.card n * (1 - scalar n X * C.mapMatrix A).det) := by
    rw [← neg_sub, det_neg, det_one_sub_mul_comm]
  _ = _ := by simp [charpolyRev, smul_eq_diagonal_mul]; ac_rfl
/-
**Matrix.eval_charpolyRev** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : Type v} [inst_1 : DecidableEq n] [
inst_2 : Fintype n] {M : Matrix n n R},   Polynomial.eval 0 M.charpolyRev = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpolyRev.eq_1`：∀ {R : Type u} [inst : CommRing R] {n : Type v}
 [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpolyR
ev = (1 - Pol…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_evalRingHom`：coe_evalRingHom (r : R) : (evalRingHom r : R
[X] -> R) = eval r
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Polynomial.X_mul_C`：X_mul_C (r : R) : X * C r = C r * X
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
（共 32 条，此处仅展示前 30 条）
-/
@[simp] lemma eval_charpolyRev :
    eval 0 M.charpolyRev = 1 := by
  rw [charpolyRev, ← coe_evalRingHom, RingHom.map_det, ← det_one (R := R) (n := n)]
  have : (1 - (X : R[X]) • M.map C).map (eval 0) = 1 := by
    ext i j; rcases eq_or_ne i j with hij | hij <;> simp [hij, one_apply]
  congr
/-
**Matrix.coeff_charpolyRev_eq_neg_trace** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : Type v} [inst_1 : DecidableEq n] [
inst_2 : Fintype n] (M : Matrix n n R),   M.charpolyRev.coeff 1 = -M.trace
参数：M : Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.coe_det_isEmpty`：coe_det_isEmpty [IsEmpty n] : (det : Matrix n n 
R -> R) = Function.const _ 1
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.trace_eq_zero_of_isEmpty`：trace_eq_zero_of_isEmpty [IsEmpty n] (A
 : Matrix n n R) : trace A = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.reverse_charpoly`：reverse_charpoly (M : Matrix n n R) : M.charpol
y.reverse = M.charpolyRev
· 使用定理 `Polynomial.coeff_one_reverse`：coeff_one_reverse (f : R[X]) : coeff (reve
rse f) 1 = nextCoeff f
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `Matrix.trace_eq_neg_charpoly_coeff`：trace_eq_neg_charpoly_coeff [Nonempt
y n] (M : Matrix n n R) : trace M = -M.charpoly.coeff (Fintype.card n - 1)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma coeff_charpolyRev_eq_neg_trace (M : Matrix n n R) :
    coeff M.charpolyRev 1 = - trace M := by
  nontriviality R
  cases isEmpty_or_nonempty n
  · simp [charpolyRev, coeff_one]
  · simp [trace_eq_neg_charpoly_coeff M, ← M.reverse_charpoly, nextCoeff]
/-
**Matrix.isUnit_charpolyRev_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isUnit_charpolyRev_of_isNilpotent (hM : IsNilpotent M) : IsUnit M.charpoly
Rev
参数：hM : IsNilpotent M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `one_sub_dvd_one_sub_pow`：one_sub_dvd_one_sub_pow (x : R) (n : Nat) : 1 -
 x ∣ 1 - x ^ n
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma isUnit_charpolyRev_of_isNilpotent (hM : IsNilpotent M) :
    IsUnit M.charpolyRev := by
  obtain ⟨k, hk⟩ := hM
  replace hk : 1 - (X : R[X]) • M.map C ∣ 1 := by
    convert! one_sub_dvd_one_sub_pow ((X : R[X]) • M.map C) k
    rw [← C.mapMatrix_apply, smul_pow, ← map_pow, hk, map_zero, smul_zero, sub_zero]
  apply isUnit_of_dvd_one
  rw [← det_one (R := R[X]) (n := n)]
  exact map_dvd detMonoidHom hk
/-
**Matrix.isNilpotent_trace_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isNilpotent_trace_of_isNilpotent (hM : IsNilpotent M) : IsNilpotent (trace
 M)
参数：hM : IsNilpotent M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.trace_eq_zero_of_isEmpty`：trace_eq_zero_of_isEmpty [IsEmpty n] (A
 : Matrix n n R) : trace A = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`：isUnit_iff_coeff_isUnit_
isNilpotent : IsUnit P ↔ IsUnit (P.coeff 0) ∧ (forall i, i != 0 -> IsNilpotent (
P.coeff i))
· 使用引理 `Matrix.isUnit_charpolyRev_of_isNilpotent`：isUnit_charpolyRev_of_isNilpot
ent (hM : IsNilpotent M) : IsUnit M.charpolyRev
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.coeff_charpolyRev_eq_neg_trace`：∀ {R : Type u} [inst : CommRing R
] {n : Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),
   M.charpolyRev.coeff 1 = …
-/
lemma isNilpotent_trace_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (trace M) := by
  cases isEmpty_or_nonempty n
  · simp
  suffices IsNilpotent (coeff (charpolyRev M) 1) by simpa using this
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
    _ one_ne_zero
/-
**Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `
Matrix`。
形式化陈述：isNilpotent_charpoly_sub_pow_of_isNilpotent (hM : IsNilpotent M) : IsNilpo
tent (M.charpoly - X ^ (Fintype.card n))
参数：hM : IsNilpotent M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.modByMonic_X`：modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0)
· 使用定理 `Matrix.eval_charpolyRev`：∀ {R : Type u} [inst : CommRing R] {n : Type v}
 [inst_1 : DecidableEq n] [inst_2 : Fintype n] {M : Matrix n n R},   Polynomial.
eval 0 M.char…
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
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isUnit_iff'`：isUnit_iff' : IsUnit P ↔ IsUnit (eval 0 P) ∧ IsN
ilpotent (P /ₘ X)
· 使用引理 `Matrix.isUnit_charpolyRev_of_isNilpotent`：isUnit_charpolyRev_of_isNilpot
ent (hM : IsNilpotent M) : IsUnit M.charpolyRev
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.natDegree_sub_le`：natDegree_sub_le (p q : R[X]) : natDegree (
p - q) <= max (natDegree p) (natDegree q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Polynomial.isNilpotent_reflect_iff`：∀ {R : Type u_1} [inst : CommRing R]
 {P : Polynomial R} {N : ℕ},   P.natDegree ≤ N → (IsNilpotent (Polynomial.reflec
t N P) ↔ IsNilpotent P)
· 使用定理 `Polynomial.reflect_sub`：reflect_sub (f g : R[X]) (N : Nat) : reflect N (
f - g) = reflect N f - reflect N g
· 使用定理 `Polynomial.reverse.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyn
omial R), f.reverse = Polynomial.reflect f.natDegree f
· 使用引理 `Matrix.reverse_charpoly`：reverse_charpoly (M : Matrix n n R) : M.charpol
y.reverse = M.charpolyRev
（共 34 条，此处仅展示前 30 条）
-/
lemma isNilpotent_charpoly_sub_pow_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (M.charpoly - X ^ (Fintype.card n)) := by
  nontriviality R
  let p : R[X] := M.charpolyRev
  have hp : p - 1 = X * (p /ₘ X) := by
    conv_lhs => rw [← modByMonic_add_div p X]
    simp [p, modByMonic_X]
  have : IsNilpotent (p /ₘ X) :=
    (Polynomial.isUnit_iff'.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - X ^ (Fintype.card n)).natDegree ≤ M.charpoly.natDegree :=
    le_trans (natDegree_sub_le _ _) (by simp)
  rw [← isNilpotent_reflect_iff aux, reflect_sub, ← reverse, M.reverse_charpoly]
  simpa [p, hp]

/-- The determinant of the matrix obtained by replacing rows outside `s` with identity rows
equals the determinant of the principal submatrix indexed by `s`. -/
/-
**Matrix.det_piecewise_one_eq_submatrix_det** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：det_piecewise_one_eq_submatrix_det (M : Matrix n n R) (s : Finset n) : det
 (Matrix.of <| s.piecewise M.row (1 : Matrix n n R).row) = (M.submatrix (↑) (↑) 
: Matrix s s R).det
参数：M : Matrix n n R；s : Finset n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Matrix.det_fromBlocks_zero₂₁`：det_fromBlocks_zero₂₁ (A : Matrix m m R) (
B : Matrix m n R) (D : Matrix n n R) : (Matrix.fromBlocks A B 0 D).det = A.det *
 D.det
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The determinant of the matrix obtained by replacing rows outside `s` with identi
ty rows
equals the determinant of the principal submatrix indexed by `s`.
-/
lemma det_piecewise_one_eq_submatrix_det
    (M : Matrix n n R) (s : Finset n) :
    det (Matrix.of <| s.piecewise M.row (1 : Matrix n n R).row) =
    (M.submatrix (↑) (↑) : Matrix s s R).det := by
  let e := Equiv.sumCompl (fun x => x ∈ s)
  let +generalize A : Matrix n n R := Matrix.of (s.piecewise M (1 : Matrix n n R))
  rw [← Matrix.det_submatrix_equiv_self e A]
  have h_blocks : A.submatrix e e =
      Matrix.fromBlocks
        (M.submatrix Subtype.val Subtype.val)
        (M.submatrix Subtype.val Subtype.val) 0 1 := by
    ext (i | i) (j | j) <;> dsimp [A, e]
    · simp only [Finset.piecewise, if_pos i.prop]
    · simp only [Finset.piecewise, if_pos i.prop]
    · simp only [Finset.piecewise, if_neg i.prop]
      exact Matrix.one_apply_ne (fun h => i.prop (h ▸ j.prop))
    · simp only [Finset.piecewise, if_neg i.prop, Matrix.one_apply, Subtype.ext_iff]
  rw [h_blocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

set_option backward.isDefEq.respectTransparency.types false in
/-- The k-th coefficient of `det (1 + X • M)` equals the sum of all k×k principal minors of M.
This generalizes `coeff_det_one_add_X_smul_one` (the k = 1 case, which gives the trace)
and `det_eq_sign_charpoly_coeff` (the k = n case, which gives the determinant). -/
/-
**Matrix.coeff_det_one_add_X_smul_eq_sum_minors** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：coeff_det_one_add_X_smul_eq_sum_minors (M : Matrix n n R) (k : Nat) : (det
 (1 + (X : R[X]) • M.map C)).coeff k = ∑ s in Finset.univ.powersetCard k, (M.sub
matrix (Subtype.val : s -> n) (Subtype.val : s -> n)).det
参数：M : Matrix n n R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlternatingMap.map_add_univ`：map_add_univ [DecidableEq ι] [Fintype ι] (m
 m' : ι -> M) : f (m + m') = ∑ s : Finset ι, f (s.piecewise m m')
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MonoidWithZeroHom.map_ite_one_zero`：map_ite_one_zero {F : Type*} [FunLik
e F α β] [MonoidWithZeroHomClass F α β] (f : F) (p : Prop) [Decidable p] : f (it
e p 1 0) = ite p 1 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AlternatingMap.map_smul_univ`：map_smul_univ {R : Type*} [CommSemiring R]
 {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Modul
e R N] [Fintype ι]…
· 使用定理 `Finset.prod_ite_mem`：prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : 
ι -> M) : ∏ i in s, (if i in t then f i else 1) = ∏ i in s inter t, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The k-th coefficient of `det (1 + X • M)` equals the sum of all k×k principal mi
nors of M.
This generalizes `coeff_det_one_add_X_smul_one` (the k = 1 case, which gives the
 trace)
and `det_eq_sign_charpoly_coeff` (the k = n case, which gives the determinant).
-/
theorem coeff_det_one_add_X_smul_eq_sum_minors
    (M : Matrix n n R) (k : ℕ) :
    (det (1 + (X : R[X]) • M.map C)).coeff k =
    ∑ s ∈ Finset.univ.powersetCard k,
      (M.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det := by
  simp only [det]
  let D := (detRowAlternating : (n → R[X]) [⋀^n]→ₗ[R[X]] R[X])
  rw [add_comm]
  change (D (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i)).coeff k = _
  conv_lhs => rw [show (fun i ↦ ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i) =
      (fun i => ((X : R[X]) • M.map C) i) + (fun i => (1 : Matrix n n R[X]) i) from rfl]
  conv_lhs => rw [D.map_add_univ]
  have h_map : ∀ s : Finset n,
        (s.piecewise (fun i ↦ (M.map C) i)
          (fun i ↦ (1 : Matrix n n R[X]) i) : Matrix n n R[X]) =
        Matrix.map (s.piecewise M (1 : Matrix n n R)) C := by
      intro s; ext i j
      simp only [Finset.piecewise, Matrix.map_apply]
      split_ifs with h <;> simp [Matrix.one_apply]
  have h_det : ∀ s : Finset n,
      D (s.piecewise (fun i ↦ (M.map C) i)
        (fun i ↦ (1 : Matrix n n R[X]) i)) =
      C (det (s.piecewise M (1 : Matrix n n R))) := by
    intro s; change det _ = _
    rw [h_map]; exact (RingHom.map_det C _).symm
  calc (∑ s : Finset n, D (Finset.piecewise s (fun i ↦ ((X : R[X]) • M.map C) i)
            (fun i ↦ (1 : Matrix n n R[X]) i))).coeff k
      _ = (∑ s : Finset n, (X : R[X]) ^ s.card •
            D (s.piecewise (fun i ↦ (M.map C) i)
              (fun i ↦ (1 : Matrix n n R[X]) i))).coeff k := by
        congr 2 with s
        have h_smul : s.piecewise (fun i ↦ ((X : R[X]) • M.map C) i)
            (fun i ↦ (1 : Matrix n n R[X]) i) =
            fun i => (if i ∈ s then (X : R[X]) else 1) •
              s.piecewise (fun i ↦ (M.map C) i) (fun i ↦ (1 : Matrix n n R[X]) i) i := by
          funext i j
          simp only [piecewise, Pi.smul_apply, smul_eq_mul, ite_mul, one_mul]
          split_ifs <;> rfl
        rw [h_smul, D.map_smul_univ]
        congr 1
        simp only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      _ = ∑ s : Finset n, ((X : R[X]) ^ s.card •
            D (Finset.piecewise s (fun i ↦ (M.map C) i)
              (fun i ↦ (1 : Matrix n n R[X]) i))).coeff k := by
        simp only [Polynomial.finsetSum_coeff]
      _ = _ := by
        simp_rw [h_det, smul_eq_mul, mul_comm (X ^ _) (C _)]
        simp_rw [C_mul_X_pow_eq_monomial, coeff_monomial]
        rw [← Finset.sum_filter]
        have h_set : Finset.univ.filter (fun s : Finset n => s.card = k) =
            Finset.univ.powersetCard k := by
          ext s; simp [Finset.mem_powersetCard]
        rw [h_set]
        exact Finset.sum_congr rfl fun s _ => det_piecewise_one_eq_submatrix_det M s

/-- The coefficients of the characteristic polynomial are signed sums of principal minors.
Specifically, the (n-k)-th coefficient of the characteristic polynomial of M equals
`(-1)^k` times the sum of all k×k principal minors of M. -/
/-
**Matrix.charpoly_coeff_eq_sum_minors** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_coeff_eq_sum_minors (M : Matrix n n R) (k : Nat) (hk : k <= Finty
pe.card n) : M.charpoly.coeff (Fintype.card n - k) = (-1) ^ k * ∑ s in Finset.un
iv.powersetCard k, (M.submatrix (Subtype.val : s -> n) (Subtype.val : s -> n)).d
et
参数：M : Matrix n n R；k : Nat；hk : k <= Fintype.card n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reverse`：coeff_reverse (f : R[X]) (n : Nat) : f.reverse
.coeff n = f.coeff (revAt f.natDegree n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.reverse_charpoly`：reverse_charpoly (M : Matrix n n R) : M.charpol
y.reverse = M.charpolyRev
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.map_neg`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w
} [inst : Neg α] [inst_1 : Neg β] (f : α → β),   (∀ (a : α), f (-a) = -f a) → ∀ 
(M :…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Matrix.coeff_det_one_add_X_smul_eq_sum_minors`：coeff_det_one_add_X_smul_
eq_sum_minors (M : Matrix n n R) (k : Nat) : (det (1 + (X : R[X]) • M.map C)).co
eff k = ∑ s in Finset.univ.powerset…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n

--- 原说明 ---
The coefficients of the characteristic polynomial are signed sums of principal m
inors.
Specifically, the (n-k)-th coefficient of the characteristic polynomial of M equ
als
`(-1)^k` times the sum of all k×k principal minors of M.
-/
theorem charpoly_coeff_eq_sum_minors
    (M : Matrix n n R) (k : ℕ) (hk : k ≤ Fintype.card n) :
    M.charpoly.coeff (Fintype.card n - k) =
    (-1) ^ k * ∑ s ∈ Finset.univ.powersetCard k,
      (M.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det := by
  nontriviality R
  have hnd := M.charpoly_natDegree_eq_dim
  have hrev : M.charpoly.coeff (Fintype.card n - k) = M.charpoly.reverse.coeff k := by
    simp [Polynomial.coeff_reverse, hnd, hk]
  rw [hrev, M.reverse_charpoly]
  have hcharpolyRev : M.charpolyRev = det (1 + (X : R[X]) • (-M).map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M, smul_neg]
  rw [hcharpolyRev, coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [submatrix_neg, Pi.neg_apply, det_neg, Fintype.card_coe, mul_sum]
  exact Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_powersetCard.mp hs).2]

end reverse

end Matrix

