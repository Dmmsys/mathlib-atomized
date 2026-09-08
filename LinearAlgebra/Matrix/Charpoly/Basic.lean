/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.MatrixPolynomialAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` for corollaries of this theorem.

## Main definitions

* `Matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

@[expose] public section

noncomputable section

universe u v w

namespace Matrix

open Finset Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)


/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
/-
**Matrix.charmatrix** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：charmatrix (M : Matrix n n R) : Matrix n n R[X]
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $
t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
/-
**Matrix.charmatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_apply : charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j
 - C (M i j)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem charmatrix_apply :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl

@[simp]
/-
**Matrix.charmatrix_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

@[simp]
/-
**Matrix.charmatrix_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_apply_ne (h : i != j) : charmatrix M i j = -C (M i j)
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charmatrix_apply_ne (h : i ≠ j) : charmatrix M i j = -C (M i j) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]

@[simp]
/-
**Matrix.charmatrix_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_zero : charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X
])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.map_zero`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type 
w} [inst : Zero α] [inst_1 : Zero β] (f : α → β),   f 0 = 0 → Matrix.map 0 f = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem charmatrix_zero : charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X]) := by
  simp [charmatrix]

@[simp]
/-
**Matrix.charmatrix_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_diagonal (d : n -> R) : charmatrix (diagonal d) = diagonal fun 
i => X - C (d i)
参数：d : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charmatrix.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u
_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charma
trix = (Matr…
· 使用定理 `Matrix.scalar_apply`：scalar_apply (a : α) : scalar n a = diagonal fun _ 
=> a
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
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
· 使用定理 `Matrix.diagonal_sub`：diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n -> α) 
: diagonal d₁ - diagonal d₂ = diagonal fun i => d₁ i - d₂ i
-/
theorem charmatrix_diagonal (d : n → R) :
    charmatrix (diagonal d) = diagonal fun i => X - C (d i) := by
  rw [charmatrix, scalar_apply, RingHom.mapMatrix_apply, diagonal_map (map_zero _), diagonal_sub]

@[simp]
/-
**Matrix.charmatrix_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_one : charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charmatrix_diagonal`：charmatrix_diagonal (d : n -> R) : charmatri
x (diagonal d) = diagonal fun i => X - C (d i)
-/
theorem charmatrix_one : charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1 :=
  charmatrix_diagonal _

@[simp]
/-
**Matrix.charmatrix_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_natCast (k : Nat) : charmatrix (k : Matrix n n R) = diagonal fu
n _ => X - (k : R[X])
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charmatrix_diagonal`：charmatrix_diagonal (d : n -> R) : charmatri
x (diagonal d) = diagonal fun i => X - C (d i)
-/
theorem charmatrix_natCast (k : ℕ) :
    charmatrix (k : Matrix n n R) = diagonal fun _ => X - (k : R[X]) :=
  charmatrix_diagonal _

@[simp]
/-
**Matrix.charmatrix_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_ofNat (k : Nat) [k.AtLeastTwo] : charmatrix (ofNat(k) : Matrix 
n n R) = diagonal fun _ => X - ofNat(k)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charmatrix_natCast`：charmatrix_natCast (k : Nat) : charmatrix (k 
: Matrix n n R) = diagonal fun _ => X - (k : R[X])
-/
theorem charmatrix_ofNat (k : ℕ) [k.AtLeastTwo] :
    charmatrix (ofNat(k) : Matrix n n R) = diagonal fun _ => X - ofNat(k) :=
  charmatrix_natCast _

@[simp]
/-
**Matrix.charmatrix_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_transpose (M : Matrix n n R) : (Mᵀ).charmatrix = M.charmatrixᵀ
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.transpose_sub`：transpose_sub [Sub α] (M : Matrix m n α) (N : Matr
ix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charmatrix_transpose (M : Matrix n n R) : (Mᵀ).charmatrix = M.charmatrixᵀ := by
  simp [charmatrix, transpose_map]
/-
**Matrix.matPolyEquiv_charmatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `matPolyEquiv_coeff_apply`：matPolyEquiv_coeff_apply (m : Matrix n n R[X])
 (k : Nat) (i j : n) : coeff (matPolyEquiv m) k i j = coeff (m i j) k
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `Polynomial.coeff_X`：coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 
0
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
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
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M := by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]
/-
**Matrix.charmatrix_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_reindex (e : n ≃ m) : charmatrix (reindex e e M) = reindex e e 
(charmatrix M)
参数：e : n ≃ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charmatrix.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : 
Type u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype 
n] (M M_1 : Matrix…
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.charmatrix_apply_ne`：charmatrix_apply_ne (h : i != j) : charmatri
x M i j = -C (M i j)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem charmatrix_reindex (e : n ≃ m) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]
/-
**Matrix.charmatrix_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_map (M : Matrix n n R) (f : R ->+* S) : charmatrix (M.map f) = 
(charmatrix M).map (Polynomial.map f)
参数：M : Matrix n n R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `Polynomial.map_neg`：∀ {R : Type u} [inst : Ring R] {p : Polynomial R} {S
 : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (-p) = -Polynom
ial.map …
-/
lemma charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]
/-
**Matrix.charmatrix_fromBlocks** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_fromBlocks : charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) = fromBloc
ks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
lemma charmatrix_fromBlocks :
    charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂) := by
  simp only [charmatrix]
  ext (i | i) (j | j) : 2 <;> simp [diagonal]

-- TODO: importing block triangular here is somewhat expensive, if more lemmas about it are added
-- to this file, it may be worth extracting things out to Charpoly/Block.lean
@[simp]
/-
**Matrix.charmatrix_blockTriangular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_blockTriangular_iff {α : Type*} [Preorder α] {M : Matrix n n R}
 {b : n -> α} : M.charmatrix.BlockTriangular b ↔ M.BlockTriangular b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charmatrix.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u
_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charma
trix = (Matr…
· 使用定理 `Matrix.scalar_apply`：scalar_apply (a : α) : scalar n a = diagonal fun _ 
=> a
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.BlockTriangular.sub_iff_right`：∀ {α : Type u_1} {m : Type u_3} {R
 : Type v} {M N : Matrix m m R} {b : m → α} [inst : LT α] [inst_1 : AddGroup R],
   M.BlockTriangular b → (…
· 使用定理 `Matrix.blockTriangular_diagonal`：blockTriangular_diagonal [DecidableEq m
] (d : m -> R) : BlockTriangular (diagonal d) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma charmatrix_blockTriangular_iff {α : Type*} [Preorder α] {M : Matrix n n R} {b : n → α} :
    M.charmatrix.BlockTriangular b ↔ M.BlockTriangular b := by
  rw [charmatrix, scalar_apply, RingHom.mapMatrix_apply, (blockTriangular_diagonal _).sub_iff_right]
  simp [BlockTriangular]

alias ⟨BlockTriangular.of_charmatrix, BlockTriangular.charmatrix⟩ := charmatrix_blockTriangular_iff

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$. -/
@[wikidata Q849705]
/-
**Matrix.charpoly** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：charpoly (M : Matrix n n R) : R[X]
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
/-
**Matrix.eval_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eval_charpoly (M : Matrix m m R) (t : R) : M.charpoly.eval t = (Matrix.sca
lar _ t - M).det
参数：M : Matrix m m R；t : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_evalRingHom`：coe_evalRingHom (r : R) : (evalRingHom r : R
[X] -> R) = eval r
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.charmatrix.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u
_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charma
trix = (Matr…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Polynomial.eval_neg`：eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval
 x
-/
theorem eval_charpoly (M : Matrix m m R) (t : R) :
    M.charpoly.eval t = (Matrix.scalar _ t - M).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det, Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

@[simp]
/-
**Matrix.charpoly_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_isEmpty [IsEmpty n] {A : Matrix n n R} : charpoly A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.coe_det_isEmpty`：coe_det_isEmpty [IsEmpty n] : (det : Matrix n n 
R -> R) = Function.const _ 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_isEmpty [IsEmpty n] {A : Matrix n n R} : charpoly A = 1 := by
  simp [charpoly]

@[simp]
/-
**Matrix.charpoly_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_zero : charpoly (0 : Matrix n n R) = X ^ Fintype.card n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.charmatrix_zero`：charmatrix_zero : charmatrix (0 : Matrix n n R) 
= Matrix.scalar n (X : R[X])
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_zero : charpoly (0 : Matrix n n R) = X ^ Fintype.card n := by
  simp [charpoly]
/-
**Matrix.charpoly_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_diagonal (d : n -> R) : charpoly (diagonal d) = ∏ i, (X - C (d i)
)
参数：d : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.charmatrix_diagonal`：charmatrix_diagonal (d : n -> R) : charmatri
x (diagonal d) = diagonal fun i => X - C (d i)
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_diagonal (d : n → R) : charpoly (diagonal d) = ∏ i, (X - C (d i)) := by
  simp [charpoly]
/-
**Matrix.charpoly_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_one : charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.charmatrix_one`：charmatrix_one : charmatrix (1 : Matrix n n R) = 
diagonal fun _ => X - 1
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_one : charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n := by
  simp [charpoly]
/-
**Matrix.charpoly_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_natCast (k : Nat) : charpoly (k : Matrix n n R) = (X - (k : R[X])
) ^ Fintype.card n
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.charmatrix_natCast`：charmatrix_natCast (k : Nat) : charmatrix (k 
: Matrix n n R) = diagonal fun _ => X - (k : R[X])
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_natCast (k : ℕ) :
    charpoly (k : Matrix n n R) = (X - (k : R[X])) ^ Fintype.card n := by
  simp [charpoly]
/-
**Matrix.charpoly_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_ofNat (k : Nat) [k.AtLeastTwo] : charpoly (ofNat(k) : Matrix n n 
R) = (X - ofNat(k)) ^ Fintype.card n
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.charpoly_natCast`：charpoly_natCast (k : Nat) : charpoly (k : Matr
ix n n R) = (X - (k : R[X])) ^ Fintype.card n
-/
theorem charpoly_ofNat (k : ℕ) [k.AtLeastTwo] :
    charpoly (ofNat(k) : Matrix n n R) = (X - ofNat(k)) ^ Fintype.card n :=
  charpoly_natCast _

@[simp]
/-
**Matrix.charpoly_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_transpose (M : Matrix n n R) : (Mᵀ).charpoly = M.charpoly
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.charmatrix_transpose`：charmatrix_transpose (M : Matrix n n R) : (
Mᵀ).charmatrix = M.charmatrixᵀ
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_transpose (M : Matrix n n R) : (Mᵀ).charpoly = M.charpoly := by
  simp [charpoly]
/-
**Matrix.charpoly_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_reindex (e : n ≃ m) (M : Matrix n n R) : (reindex e e M).charpoly
 = M.charpoly
参数：e : n ≃ m；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charmatrix_reindex`：charmatrix_reindex (e : n ≃ m) : charmatrix (
reindex e e M) = reindex e e (charmatrix M)
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
-/
theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]
/-
**Matrix.charpoly_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charpoly_map (M : Matrix n n R) (f : R ->+* S) : (M.map f).charpoly = M.ch
arpoly.map f
参数：M : Matrix n n R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用引理 `Matrix.charmatrix_map`：charmatrix_map (M : Matrix n n R) (f : R ->+* S) 
: charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
-/
lemma charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [charpoly, charmatrix_map, ← Polynomial.coe_mapRingHom, charpoly, RingHom.map_det,
    RingHom.mapMatrix_apply]

@[simp]
/-
**Matrix.charpoly_fromBlocks_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]
/-
**Matrix.charpoly_fromBlocks_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]
/-
**Matrix.charmatrix_toSquareBlock** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charmatrix_toSquareBlock {α : Type*} [DecidableEq α] {b : n -> α} {a : α} 
: (M.toSquareBlock b a).charmatrix = M.charmatrix.toSquareBlock b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charmatrix_toSquareBlock {α : Type*} [DecidableEq α] {b : n → α} {a : α} :
    (M.toSquareBlock b a).charmatrix = M.charmatrix.toSquareBlock b a := by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlock_def, diagonal_apply, Subtype.ext_iff]
/-
**Matrix.BlockTriangular.charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangu
lar`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4} [inst_1 : DecidableEq 
n] [inst_2 : Fintype n] (M : Matrix n n R)   {α : Type u_5} {b : n → α} [inst_3 
: LinearOrder α],   M.BlockTriangular b → M.charpoly = ∏ a ∈ Finset.image b Fins
et.univ, (M.toSquareBlock b a).charpoly
参数：M : Matrix n n R；M.toSquareBlock b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.BlockTriangular.det`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M : Matrix m m R} {b : m → α} [inst : CommRing R] [inst_1 : DecidableEq m]   [
inst_2 : Fintype…
· 使用定理 `Matrix.BlockTriangular.charmatrix`：∀ {R : Type u_1} [inst : CommRing R] 
{n : Type u_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] {α : Type u_5}   [i
nst_3 : Preorder α] {M …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `Matrix.charmatrix_toSquareBlock`：charmatrix_toSquareBlock {α : Type*} [D
ecidableEq α] {b : n -> α} {a : α} : (M.toSquareBlock b a).charmatrix = M.charma
trix.toSquareBlock b …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma BlockTriangular.charpoly {α : Type*} {b : n → α} [LinearOrder α] (h : M.BlockTriangular b) :
    M.charpoly = ∏ a ∈ image b univ, (M.toSquareBlock b a).charpoly := by
  simp only [Matrix.charpoly, h.charmatrix.det, charmatrix_toSquareBlock]
/-
**Matrix.charpoly_of_isUpperTriangular** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：charpoly_of_isUpperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.Is
UpperTriangular) : M.charpoly = ∏ i : n, (X - C (M i i))
参数：M : Matrix n n R；h : M.IsUpperTriangular。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `Matrix.BlockTriangular.charmatrix`：∀ {R : Type u_1} [inst : CommRing R] 
{n : Type u_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] {α : Type u_5}   [i
nst_3 : Preorder α] {M …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charpoly_of_isUpperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.IsUpperTriangular) :
    M.charpoly = ∏ i : n, (X - C (M i i)) := by
  simp [charpoly, det_of_isUpperTriangular h.charmatrix]

@[deprecated (since := "2026-07-30")]
alias charpoly_of_upperTriangular := charpoly_of_isUpperTriangular

-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.

See `LinearMap.aeval_self_charpoly` for the equivalent statement about endomorphisms.
-/
/-
**Matrix.aeval_self_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.adjugate_mul`：adjugate_mul (A : Matrix n n α) : adjugate A * A = 
A.det • (1 : Matrix n n α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `matPolyEquiv_smul_one`：matPolyEquiv_smul_one (p : R[X]) : matPolyEquiv (
p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R))
· 使用定理 `Polynomial.eval_mul_X_sub_C`：eval_mul_X_sub_C {p : R[X]} (r : R) : (p * 
(X - C r)).eval r = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Matrix.matPolyEquiv_charmatrix`：matPolyEquiv_charmatrix : matPolyEquiv (
charmatrix M) = X - C M

--- 原说明 ---
The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.

See `LinearMap.aeval_self_charpoly` for the equivalent statement about endomorph
isms.
-/
theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R)`,
  -- we have the same identity in `Polynomial (Matrix n n R)`.
  apply_fun matPolyEquiv at h
  simp only [map_mul, matPolyEquiv_charmatrix] at h
  -- Because the coefficient ring `Matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun fun p => p.eval M at h
  rw [eval_mul_X_sub_C] at h
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [matPolyEquiv_smul_one, eval_map] at h
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h

set_option backward.defeqAttrib.useBackward true in
/--
A version of `Matrix.charpoly_mul_comm` for rectangular matrices.
See also `Matrix.charpoly_mul_comm_of_le` which has just `(A * B).charpoly` as the LHS.
-/
/-
**Matrix.charpoly_mul_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) : X ^ Fintype.car
d n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly
参数：A : Matrix m n R；B : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.mul_neg`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Matrix.smul_eq_mul_diagonal`：smul_eq_mul_diagonal [Fintype n] [Decidable
Eq n] (M : Matrix m n α) (a : α) : a • M = M * diagonal fun _ => a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.neg_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `Matrix.scalar_comm`：scalar_comm (r : α) (hr : forall r', Commute r r') (
M : Matrix m n α) : scalar m r * M = M * scalar n r
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.det_fromBlocks_zero₂₁`：det_fromBlocks_zero₂₁ (A : Matrix m m R) (
B : Matrix m n R) (D : Matrix n n R) : (Matrix.fromBlocks A B 0 D).det = A.det *
 D.det
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `Matrix.charpoly_mul_comm` for rectangular matrices.
See also `Matrix.charpoly_mul_comm_of_le` which has just `(A * B).charpoly` as t
he LHS.
-/
theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly := by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN :
      M * N = fromBlocks (-scalar m X + (A * B).map C) (-(X : R[X]) • A.map C) 0 (-scalar n X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-scalar m X) (-A.map C) 0 ((B * A).map C - scalar n X) := by
    simp [M, N, fromBlocks_multiply, sub_eq_add_neg, -scalar_apply, scalar_comm, Commute.all]
  have hdet_MN : (M * N).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card n * (scalar m X - (A * B).map C).det) := by
    rw [hMN, det_fromBlocks_zero₂₁, neg_add_eq_sub, ← neg_sub, det_neg]
    simp
    ring
  have hdet_NM : (N * M).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card m * (scalar n X - (B * A).map C).det) := by
    rw [hNM, det_fromBlocks_zero₂₁, ← neg_sub, det_neg (_ - _)]
    simp
    ring
  dsimp only [charpoly, charmatrix, RingHom.mapMatrix_apply]
  rw [← (isUnit_neg_one.pow _).isRegular.left.eq_iff, ← hdet_NM, ← hdet_MN, det_mul_comm]
/-
**Matrix.charpoly_mul_comm_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_mul_comm_of_le (A : Matrix m n R) (B : Matrix n m R) (hle : Finty
pe.card n <= Fintype.card m) : (A * B).charpoly = X ^ (Fintype.card m - Fintype.
card n) * (B * A).charpoly
参数：A : Matrix m n R；B : Matrix n m R；hle : Fintype.card n <= Fintype.card m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Polynomial.isRegular_X_pow`：isRegular_X_pow (n : Nat) : IsRegular (X ^ n
 : R[X])
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Matrix.charpoly_mul_comm'`：charpoly_mul_comm' (A : Matrix m n R) (B : Ma
trix n m R) : X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * 
A).charpoly
-/
theorem charpoly_mul_comm_of_le
    (A : Matrix m n R) (B : Matrix n m R) (hle : Fintype.card n ≤ Fintype.card m) :
    (A * B).charpoly = X ^ (Fintype.card m - Fintype.card n) * (B * A).charpoly := by
  rw [← (isRegular_X_pow _).left.eq_iff, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hle, charpoly_mul_comm']

/-- A version of `charpoly_mul_comm'` for square matrices. -/
/-
**Matrix.charpoly_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpo
ly
参数：A B : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Polynomial.isRegular_X_pow`：isRegular_X_pow (n : Nat) : IsRegular (X ^ n
 : R[X])
· 使用定理 `Matrix.charpoly_mul_comm'`：charpoly_mul_comm' (A : Matrix m n R) (B : Ma
trix n m R) : X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * 
A).charpoly

--- 原说明 ---
A version of `charpoly_mul_comm'` for square matrices.
-/
theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly :=
  (isRegular_X_pow _).left.eq_iff.mp <| charpoly_mul_comm' A B
/-
**Matrix.charpoly_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_vecMulVec (u v : n -> R) : (vecMulVec u v).charpoly = X ^ Fintype
.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1)
参数：u v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly_isEmpty`：charpoly_isEmpty [IsEmpty n] {A : Matrix n n R}
 : charpoly A = 1
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.dotProduct_of_isEmpty`：dotProduct_of_isEmpty [Fintype n'] [IsEmpt
y n'] (v w : n' -> α) : v ⬝ᵥ w = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NeZero.one_le`：one_le {n : Nat} [NeZero n] : 1 <= n
· 使用定理 `Fintype.instNeZeroNatCardOfNonempty`：∀ {α : Type u_1} [inst : Fintype α]
 [Nonempty α], NeZero (Fintype.card α)
· 使用定理 `Matrix.vecMulVec_eq`：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (
w : m -> α) (v : n -> α) : vecMulVec w v = replicateCol ι w * replicateRow ι v
· 使用定理 `Matrix.charpoly_mul_comm_of_le`：charpoly_mul_comm_of_le (A : Matrix m n 
R) (B : Matrix n m R) (hle : Fintype.card n <= Fintype.card m) : (A * B).charpol
y = X ^ (Fintype.car…
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用定理 `Matrix.charmatrix.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u
_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charma
trix = (Matr…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Polynomial.X_pow_mul_C`：X_pow_mul_C (r : R) (n : Nat) : X ^ n * C r = C 
r * X ^ n
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
-/
theorem charpoly_vecMulVec (u v : n → R) :
    (vecMulVec u v).charpoly = X ^ Fintype.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1) := by
  cases isEmpty_or_nonempty n
  · simp
  · have h : 1 ≤ Fintype.card n := NeZero.one_le
    rw [vecMulVec_eq (ι := Unit), charpoly_mul_comm_of_le (n := Unit) _ _ h, charpoly, charmatrix]
    simp [-Matrix.map_mul, mul_sub, ← pow_succ, h, dotProduct_comm, smul_eq_C_mul]

@[simp]
/-
**Matrix.charpoly_units_conj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) : (M.val * N 
* M.val⁻¹).charpoly = N.charpoly
参数：M : (Matrix n n R)ˣ；N : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly_mul_comm`：charpoly_mul_comm (A B : Matrix n n R) : (A * 
B).charpoly = (B * A).charpoly
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M.val⁻¹).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

@[simp]
/-
**Matrix.charpoly_units_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) : (M.val⁻¹ *
 N * M.val).charpoly = N.charpoly
参数：M : (Matrix n n R)ˣ；N : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.inv_inv_of_invertible`：inv_inv_of_invertible [Invertible A] : A⁻¹
⁻¹ = A
· 使用定理 `Matrix.charpoly_units_conj`：charpoly_units_conj (M : (Matrix n n R)ˣ) (N
 : Matrix n n R) : (M.val * N * M.val⁻¹).charpoly = N.charpoly
-/
theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val⁻¹ * N * M.val).charpoly = N.charpoly := by
  simpa using charpoly_units_conj M⁻¹ N

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.charpoly_sub_scalar** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：charpoly_sub_scalar (M : Matrix n n R) (μ : R) : (M - scalar n μ).charpoly
 = M.charpoly.comp (X + C μ)
参数：M : Matrix n n R；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.sum_comp`：∀ {R : Type u} {ι : Type y} [inst : Semiring R] (s 
: Finset ι) (p : ι → Polynomial R) (q : Polynomial R),   (∑ i ∈ s, p i).comp q =
 ∑ i ∈ s,…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.smul_comp`：smul_comp [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p q : R[X]) : (s • p).comp q = s • p.comp q
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.prod_comp`：prod_comp {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (q : R[X]) : (∏ j in s, p j).comp q = ∏ j in s, (p j).comp q
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.charmatrix.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : 
Type u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype 
n] (M M_1 : Matrix…
· 使用定理 `Matrix.charmatrix_apply_eq`：charmatrix_apply_eq : charmatrix M i i = (X 
: R[X]) - C (M i i)
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 49 条，此处仅展示前 30 条）
-/
theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - scalar n μ).charpoly = M.charpoly.comp (X + C μ) := by
  simp_rw [charpoly, det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

end Matrix

