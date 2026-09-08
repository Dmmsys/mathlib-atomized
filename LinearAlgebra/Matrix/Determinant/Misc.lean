/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Miscellaneous results about determinant

In this file, we collect various formulas about determinant of matrices.
-/

public section

assert_not_exists TwoSidedIdeal

namespace Matrix

variable {R : Type*} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be a `(n+1) × n` matrix whose row sums to zero. Then all the matrices obtained by
deleting one row have the same determinant up to a sign. -/
/-
**Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det** 是 Mathli
b 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det {n : Nat} (M 
: Matrix (Fin (n + 1)) (Fin n) R) (hv : ∑ j, M j = 0) (j₁ j₂ : Fin (n + 1)) : (M
.submatrix (Fin.succAbove j₁) id).det = Int.negOnePow (j₁ - j₂) • (M.submatrix (
Fin.succAbove j₂) id).det
参数：M : Matrix (Fin (n + 1)) (Fin n) R；hv : ∑ j, M j = 0；j₁ j₂ : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Int.negOnePow_zero`：negOnePow_zero : negOnePow 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Fin.val_succ`：∀ {n : ℕ} (j : Fin n), ↑j.succ = ↑j + 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Int.negOnePow_succ`：negOnePow_succ (n : Int) : (n + 1).negOnePow = -n.ne
gOnePow
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `Matrix.det_updateRow_sum`：det_updateRow_sum (A : Matrix n n R) (j : n) (
c : n -> R) : (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det
· 使用定理 `Fin.val_castSucc`：∀ {n : ℕ} (i : Fin n), ↑i.castSucc = ↑i
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Let `M` be a `(n+1) × n` matrix whose row sums to zero. Then all the matrices ob
tained by
deleting one row have the same determinant up to a sign.
-/
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin n) R) (hv : ∑ j, M j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix (Fin.succAbove j₁) id).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix (Fin.succAbove j₂) id).det := by
  suffices ∀ j, (M.submatrix (Fin.succAbove j) id).det =
      Int.negOnePow j • (M.submatrix (Fin.succAbove 0) id).det by
    rw [this j₁, this j₂, smul_smul, ← Int.negOnePow_add, sub_add_cancel]
  intro j
  induction j using Fin.induction with
  | zero => rw [Fin.val_zero, Nat.cast_zero, Int.negOnePow_zero, one_smul]
  | succ i h_ind =>
      rw [Fin.val_succ, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.neg_smul,
        ← neg_eq_iff_eq_neg, ← neg_one_smul R,
        ← det_updateRow_sum (M.submatrix i.succ.succAbove id) i (fun _ ↦ -1),
        ← Fin.val_castSucc i, ← h_ind]
      congr
      ext a b
      simp_rw [neg_one_smul, updateRow_apply, Finset.sum_neg_distrib, Pi.neg_apply,
        Finset.sum_apply, submatrix_apply, id_eq]
      split_ifs with h
      · replace hv := congr_fun hv b
        rw [Fin.sum_univ_succAbove _ i.succ, Pi.add_apply, Finset.sum_apply] at hv
        rwa [h, Fin.succAbove_castSucc_self, neg_eq_iff_add_eq_zero, add_comm]
      · obtain h | h := ne_iff_lt_or_gt.mp h
        · rw [Fin.succAbove_castSucc_of_lt _ _ h,
            Fin.succAbove_of_succ_le _ _ (Fin.succ_lt_succ_iff.mpr h).le]
        · rw [Fin.succAbove_succ_of_lt _ _ h, Fin.succAbove_castSucc_of_le _ _ h.le]

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be a `(n+1) × n` matrix whose column sums to zero. Then all the matrices obtained by
deleting one column have the same determinant up to a sign. -/
/-
**Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'** 是 Mathl
ib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det' {n : Nat} (M
 : Matrix (Fin n) (Fin (n + 1)) R) (hv : forall i, ∑ j, M i j = 0) (j₁ j₂ : Fin 
(n + 1)) : (M.submatrix id (Fin.succAbove j₁)).det = Int.negOnePow (j₁ - j₂) • (
M.submatrix id (Fin.succAbove j₂)).det
参数：M : Matrix (Fin n) (Fin (n + 1)) R；hv : forall i, ∑ j, M i j = 0；j₁ j₂ : Fin 
(n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det`：sub
matrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det {n : Nat} (M : Matrix 
(Fin (n + 1)) (Fin n) R) (hv : ∑ j, M j = 0) (j₁ j₂ : Fin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M

--- 原说明 ---
Let `M` be a `(n+1) × n` matrix whose column sums to zero. Then all the matrices
 obtained by
deleting one column have the same determinant up to a sign.
-/
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det' {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) R) (hv : ∀ i, ∑ j, M i j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix id (Fin.succAbove j₁)).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix id (Fin.succAbove j₂)).det := by
  rw [← det_transpose, transpose_submatrix,
    submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det M.transpose ?_ j₁ j₂,
    ← det_transpose, transpose_submatrix, transpose_transpose]
  ext
  simp_rw [Finset.sum_apply, transpose_apply, hv, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be a `(n+1) × (n+1)` matrix. Assume that all columns, but the `j₀`-column, sums to zero.
Then its determinant is, up to sign, the sum of the `j₀`-column times the determinant of the
matrix obtained by deleting any row and the `j₀`-column. -/
/-
**Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det** 是 Mathlib 中的一
个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_sum_column_mul_submatrix_succAbove_succAbove_det {n : Nat} (M : Mat
rix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1)) (hv : forall j != j₀, ∑
 i, M i j = 0) : M.det = (-1) ^ (i₀ + j₀ : Nat) * (∑ i, M i j₀) * (M.submatrix (
Fin.succAbove i₀) (Fin.succAbove j₀)).det
参数：M : Matrix (Fin (n + 1)) (Fin (n + 1)) R；i₀ j₀ : Fin (n + 1)；hv : forall j !=
 j₀, ∑ i, M i j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.det_updateRow_sum`：det_updateRow_sum (A : Matrix n n R) (j : n) (
c : n -> R) : (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det
· 使用定理 `Matrix.det_succ_row`：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fi
n n.succ) R) (i : Fin n.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) *
 A i j * …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.submatrix_updateRow_succAbove`：submatrix_updateRow_succAbove (A :
 Matrix (Fin m.succ) n' α) (v : n' -> α) (f : o' -> n') (i : Fin m.succ) : (A.up
dateRow i v).submatrix i.s…
· 使用定理 `Fintype.sum_eq_add_sum_subtype_ne`：∀ {α : Type u_1} {M : Type u_4} [inst
 : Fintype α] [inst_1 : AddCommMonoid M] [inst_2 : DecidableEq α] (f : α → M)   
(a : α), ∑ i, f i = f a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Let `M` be a `(n+1) × (n+1)` matrix. Assume that all columns, but the `j₀`-colum
n, sums to zero.
Then its determinant is, up to sign, the sum of the `j₀`-column times the determ
inant of the
matrix obtained by deleting any row and the `j₀`-column.
-/
theorem det_eq_sum_column_mul_submatrix_succAbove_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : ∀ j ≠ j₀, ∑ i, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : ℕ) *
      (∑ i, M i j₀) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← one_smul R M.det, ← Matrix.det_updateRow_sum _ i₀ (fun _ ↦ 1), Matrix.det_succ_row _ i₀]
  simp only [updateRow_apply, if_true, one_smul, submatrix_updateRow_succAbove, Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
  conv_lhs =>
    enter [2, 2, i]
    rw [hv _ i.prop, mul_zero, zero_mul]
  simp [Finset.sum_const_zero, add_zero]

/-- Let `M` be a `(n+1) × (n+1)` matrix. Assume that all rows, but the `i₀`-row, sums to zero.
Then its determinant is, up to sign, the sum of the `i₀`-row times the determinant of the
matrix obtained by deleting the `i₀`-row and any column. -/
/-
**Matrix.det_eq_sum_row_mul_submatrix_succAbove_succAbove_det** 是 Mathlib 中的一个定理
，位于命名空间 `Matrix`。
形式化陈述：det_eq_sum_row_mul_submatrix_succAbove_succAbove_det {n : Nat} (M : Matrix
 (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1)) (hv : forall i != i₀, ∑ j,
 M i j = 0) : M.det = (-1) ^ (i₀ + j₀ : Nat) * (∑ j, M i₀ j) * (M.submatrix (Fin
.succAbove i₀) (Fin.succAbove j₀)).det
参数：M : Matrix (Fin (n + 1)) (Fin (n + 1)) R；i₀ j₀ : Fin (n + 1)；hv : forall i !=
 i₀, ∑ j, M i j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det`：det_eq_s
um_column_mul_submatrix_succAbove_succAbove_det {n : Nat} (M : Matrix (Fin (n + 
1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1)) (hv : for…
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Let `M` be a `(n+1) × (n+1)` matrix. Assume that all rows, but the `i₀`-row, sum
s to zero.
Then its determinant is, up to sign, the sum of the `i₀`-row times the determina
nt of the
matrix obtained by deleting the `i₀`-row and any column.
-/
theorem det_eq_sum_row_mul_submatrix_succAbove_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : ∀ i ≠ i₀, ∑ j, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : ℕ) *
      (∑ j, M i₀ j) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← det_transpose, det_eq_sum_column_mul_submatrix_succAbove_succAbove_det _ j₀ i₀
    (by simpa using hv), ← det_transpose, transpose_submatrix, transpose_transpose, add_comm]
  simp_rw [transpose_apply]

end Matrix

