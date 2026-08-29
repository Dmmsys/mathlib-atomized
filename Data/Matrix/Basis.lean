/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash, Wen Yang
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Matrices with a single non-zero element.

This file provides `Matrix.single`. The matrix `Matrix.single i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/

@[expose] public section

assert_not_exists Matrix.trace

variable {l m n o : Type*}
variable {R S α β γ : Type*}

namespace Matrix

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]

section Zero
variable [Zero α]

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (i : m) (j : n) (a : α)
  body: of fun i' j' => if i = i' ∧ j = j' then a else 0

中文:
定义 single
  签名: (i : m) (j : n) (a : α)
  定义体: of fun i' j' => if i = i' ∧ j = j' then a else 0
-/
def single (i : m) (j : n) (a : α) : Matrix m n α :=
of fun i' j' => if i = i' ∧ j = j' then a else 0

section
variable (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
/--
theorem `single_apply_same` / 定理 `single_apply_same`

English:
theorem single_apply_same
  statement: single i j c i j = c
  proof: if_pos (And.intro rfl rfl)

@[simp]

中文:
定理 single_apply_same
  结论: single i j c i j = c
  证明: if_pos (And.intro rfl rfl)

@[simp]

Depends on / 依赖: And.intro, if_pos
-/
theorem single_apply_same : single i j c i j = c :=
  if_pos (And.intro rfl rfl)

@[simp]
/--
theorem `single_apply_of_ne` / 定理 `single_apply_of_ne`

English:
theorem single_apply_of_ne
  given: (h : ¬(i = i' ∧ j = j'))
  statement: single i j c i' j' = 0
  proof: by
  simp only [single, and_imp, ite_eq_right_iff, of_apply]
  tauto

中文:
定理 single_apply_of_ne
  条件: (h : ¬(i = i' ∧ j = j'))
  结论: single i j c i' j' = 0
  证明: by
  simp only [single, and_imp, ite_eq_right_iff, of_apply]
  tauto

Depends on / 依赖: and_imp, ite_eq_right_iff, of_apply, single
-/
theorem single_apply_of_ne (h : ¬(i = i' ∧ j = j')) : single i j c i' j' = 0 := by
  simp only [single, and_imp, ite_eq_right_iff, of_apply]
  tauto

/--
theorem `single_apply_of_row_ne` / 定理 `single_apply_of_row_ne`

English:
theorem single_apply_of_row_ne
  given: {i i' : m} (hi : i != i') (j j' : n) (a : α)
  proof: by simp [hi]

中文:
定理 single_apply_of_row_ne
  条件: {i i' : m} (hi : i != i') (j j' : n) (a : α)
  证明: by simp [hi]
-/
theorem single_apply_of_row_ne {i i' : m} (hi : i != i') (j j' : n) (a : α) :
    single i j a i' j' = 0 := by simp [hi]

/--
theorem `single_apply_of_col_ne` / 定理 `single_apply_of_col_ne`

English:
theorem single_apply_of_col_ne
  given: (i i' : m) {j j' : n} (hj : j != j') (a : α)
  proof: by simp [hj]

@[grind =]

中文:
定理 single_apply_of_col_ne
  条件: (i i' : m) {j j' : n} (hj : j != j') (a : α)
  证明: by simp [hj]

@[grind =]
-/
theorem single_apply_of_col_ne (i i' : m) {j j' : n} (hj : j != j') (a : α) :
    single i j a i' j' = 0 := by simp [hj]

@[grind =]
/--
lemma `single_apply` / 引理 `single_apply`

English:
lemma single_apply
  statement: single i j c i' j' = if i = i' ∧ j = j' then c else 0
  proof: rfl

中文:
引理 single_apply
  结论: single i j c i' j' = if i = i' ∧ j = j' then c else 0
  证明: rfl
-/
lemma single_apply : single i j c i' j' = if i = i' ∧ j = j' then c else 0 := rfl

end

/--
theorem `single_eq_of_single_single` / 定理 `single_eq_of_single_single`

English:
theorem single_eq_of_single_single
  given: (i : m) (j : n) (a : α)
  proof: by
  ext a b
  unfold single
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]

@[simp]

中文:
定理 single_eq_of_single_single
  条件: (i : m) (j : n) (a : α)
  证明: by
  ext a b
  unfold single
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]

@[simp]

Depends on / 依赖: single
-/
theorem single_eq_of_single_single (i : m) (j : n) (a : α) :
    single i j a = Matrix.of (Pi.single i (Pi.single j a)) := by
  ext a b
  unfold single
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]

@[simp]
/--
theorem `of_symm_single` / 定理 `of_symm_single`

English:
theorem of_symm_single
  given: (i : m) (j : n) (a : α)
  proof: congr_arg of.symm single_eq_of_single_single i j a

@[simp]

中文:
定理 of_symm_single
  条件: (i : m) (j : n) (a : α)
  证明: congr_arg of.symm single_eq_of_single_single i j a

@[simp]

Depends on / 依赖: congr_arg, of.symm, single_eq_of_single_single
-/
theorem of_symm_single (i : m) (j : n) (a : α) :
    of.symm (single i j a) = Pi.single i (Pi.single j a) :=
congr_arg of.symm single_eq_of_single_single i j a

@[simp]
/--
theorem `smul_single` / 定理 `smul_single`

English:
theorem smul_single
  given: [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α)
  proof: by
  unfold single
  ext
  simp [smul_ite]

@[simp]

中文:
定理 smul_single
  条件: [SMulZero类 R α] (r : R) (i : m) (j : n) (a : α)
  证明: by
  unfold single
  ext
  simp [smul_ite]

@[simp]

Depends on / 依赖: single, smul_ite
-/
theorem smul_single [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α) :
    r • single i j a = single i j (r • a) := by
  unfold single
  ext
  simp [smul_ite]

@[simp]
/--
theorem `single_zero` / 定理 `single_zero`

English:
theorem single_zero
  given: (i : m) (j : n)
  statement: single i j (0 : α) = 0
  proof: by
  unfold single
  ext
  simp

@[simp]

中文:
定理 single_zero
  条件: (i : m) (j : n)
  结论: single i j (0 : α) = 0
  证明: by
  unfold single
  ext
  simp

@[simp]

Depends on / 依赖: single
-/
theorem single_zero (i : m) (j : n) : single i j (0 : α) = 0 := by
  unfold single
  ext
  simp

@[simp]
/--
lemma `transpose_single` / 引理 `transpose_single`

English:
lemma transpose_single
  given: (i : m) (j : n) (a : α)
  proof: by
  aesop (add unsafe unfold single)

@[simp]

中文:
引理 transpose_single
  条件: (i : m) (j : n) (a : α)
  证明: by
  aesop (add unsafe unfold single)

@[simp]

Depends on / 依赖: single, unsafe
-/
lemma transpose_single (i : m) (j : n) (a : α) :
    (single i j a)ᵀ = single j i a := by
  aesop (add unsafe unfold single)

@[simp]
/--
lemma `map_single` / 引理 `map_single`

English:
lemma map_single
  statement: (i : m) (j : n) (a : α) {β : Type*} [Zero β]
  proof: by
  aesop (add unsafe unfold single)

中文:
引理 map_single
  结论: (i : m) (j : n) (a : α) {β : 类型} [零 β]
  证明: by
  aesop (add unsafe unfold single)

Depends on / 依赖: single, unsafe
-/
lemma map_single (i : m) (j : n) (a : α) {β : Type*} [Zero β]
    {F : Type*} [FunLike F α β] [ZeroHomClass F α β] (f : F) :
    (single i j a).map f = single i j (f a) := by
  aesop (add unsafe unfold single)

/--
theorem `single_mem_matrix` / 定理 `single_mem_matrix`

English:
theorem single_mem_matrix
  given: {S : Set α} (hS : 0 in S) {i : m} {j : n} {a : α}
  proof: by
  simp only [Set.mem_matrix, single, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

中文:
定理 single_mem_matrix
  条件: {S : 集合 α} (hS : 0 in S) {i : m} {j : n} {a : α}
  证明: by
  simp only [Set.mem_matrix, single, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

Depends on / 依赖: Set.mem_matrix, conv_lhs, ite_mem, mem_matrix, of_apply, single
-/
theorem single_mem_matrix {S : Set α} (hS : 0 in S) {i : m} {j : n} {a : α} :
    Matrix.single i j a in S.matrix ↔ a in S := by
  simp only [Set.mem_matrix, single, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

/--
theorem `diagonal_single` / 定理 `diagonal_single`

English:
theorem diagonal_single
  given: (i : m) (r : α)
  proof: by
  ext j k
  dsimp [diagonal, single]
  grind

@[simp]

中文:
定理 diagonal_single
  条件: (i : m) (r : α)
  证明: by
  ext j k
  dsimp [diagonal, single]
  grind

@[simp]

Depends on / 依赖: diagonal, single
-/
theorem diagonal_single (i : m) (r : α) :
    diagonal (Pi.single i r) = single i i r := by
  ext j k
  dsimp [diagonal, single]
  grind

@[simp]
/--
theorem `submatrix_single_equiv` / 定理 `submatrix_single_equiv`

English:
theorem submatrix_single_equiv
  proof: by
  ext i' j'
  dsimp
  obtain hi | rfl := ne_or_eq (f.symm i) i'
  · rw [single_apply_of_row_ne hi, single_apply_of_row_ne]
    exact f.symm_apply_eq.not.1 hi
  obtain hj | rfl := ne_or_eq (g.symm j) j'
  · rw [single_apply_of_col_ne _ _ hj, single_apply_of_col_ne]
    exact g.symm_apply_eq.not.1 hj
  simp

中文:
定理 submatrix_single_equiv
  证明: by
  ext i' j'
  dsimp
  obtain hi | rfl := ne_or_eq (f.symm i) i'
  · rw [single_apply_of_row_ne hi, single_apply_of_row_ne]
    exact f.symm_apply_eq.not.1 hi
  obtain hj | rfl := ne_or_eq (g.symm j) j'
  · rw [single_apply_of_col_ne _ _ hj, single_apply_of_col_ne]
    exact g.symm_apply_eq.not.1 hj
  simp

Depends on / 依赖: f.symm, f.symm_apply_eq.not, g.symm, g.symm_apply_eq.not, ne_or_eq, single_apply_of_col_ne, single_apply_of_row_ne, symm_apply_eq
-/
theorem submatrix_single_equiv
    (f : l ≃ n) (g : m ≃ o) (i : n) (j : o) (r : α) :
    (single i j r).submatrix f g = single (f.symm i) (g.symm j) r := by
  ext i' j'
  dsimp
  obtain hi | rfl := ne_or_eq (f.symm i) i'
  · rw [single_apply_of_row_ne hi, single_apply_of_row_ne]
    exact f.symm_apply_eq.not.1 hi
  obtain hj | rfl := ne_or_eq (g.symm j) j'
  · rw [single_apply_of_col_ne _ _ hj, single_apply_of_col_ne]
    exact g.symm_apply_eq.not.1 hj
  simp

end Zero

/--
theorem `single_add` / 定理 `single_add`

English:
theorem single_add
  given: [AddZeroClass α] (i : m) (j : n) (a b : α)
  proof: by
  ext
  simp only [single, of_apply]
  split_ifs with h <;> simp [h]

中文:
定理 single_add
  条件: [加法零类 α] (i : m) (j : n) (a b : α)
  证明: by
  ext
  simp only [single, of_apply]
  split_ifs with h <;> simp [h]

Depends on / 依赖: of_apply, single, split_ifs
-/
theorem single_add [AddZeroClass α] (i : m) (j : n) (a b : α) :
    single i j (a + b) = single i j a + single i j b := by
  ext
  simp only [single, of_apply]
  split_ifs with h <;> simp [h]

/--
lemma `single_neg` / 引理 `single_neg`

English:
lemma single_neg
  given: [NegZeroClass α] (i j : n) (b : α)
  proof: .trans ext fun x y => by simp [single, neg_ite] neg_of _

中文:
引理 single_neg
  条件: [NegZero类 α] (i j : n) (b : α)
  证明: .trans ext fun x y => by simp [single, neg_ite] neg_of _

Depends on / 依赖: neg_ite, neg_of, single
-/
lemma single_neg [NegZeroClass α] (i j : n) (b : α) :
    - single i j b = single i j (-b) :=
.trans ext fun x y => by simp [single, neg_ite] neg_of _

/--
theorem `single_mulVec` / 定理 `single_mulVec`

English:
theorem single_mulVec
  statement: [NonUnitalNonAssocSemiring α] [Fintype m]
  proof: by
  ext i'
  simp only [mulVec, dotProduct, single, of_apply, ite_mul, zero_mul]
  rcases eq_or_ne i i' with rfl | h
  · simp
  simp [h, h.symm]

中文:
定理 single_mulVec
  结论: [非幺非结合半环 α] [有限类型 m]
  证明: by
  ext i'
  simp only [mulVec, dotProduct, single, of_apply, ite_mul, zero_mul]
  rcases eq_or_ne i i' with rfl | h
  · simp
  simp [h, h.symm]

Depends on / 依赖: dotProduct, eq_or_ne, h.symm, ite_mul, mulVec, of_apply, single, zero_mul
-/
theorem single_mulVec [NonUnitalNonAssocSemiring α] [Fintype m]
    (i : n) (j : m) (c : α) (x : m -> α) :
    mulVec (single i j c) x = Function.update (0 : n -> α) i (c * x j) := by
  ext i'
  simp only [mulVec, dotProduct, single, of_apply, ite_mul, zero_mul]
  rcases eq_or_ne i i' with rfl | h
  · simp
  simp [h, h.symm]

/--
lemma `single_mulVec_eq` / 引理 `single_mulVec_eq`

English:
lemma single_mulVec_eq
  given: [Fintype n] [NonAssocSemiring α] (i j : n) (b : α) (w : n -> α)
  proof: by
  ext
  simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply]

中文:
引理 single_mulVec_eq
  条件: [有限类型 n] [非结合半环 α] (i j : n) (b : α) (w : n -> α)
  证明: by
  ext
  simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply]

Depends on / 依赖: Function, Function.update_apply, Matrix, Matrix.single_mulVec, Pi.single_apply, single_apply, single_mulVec, update_apply
-/
lemma single_mulVec_eq [Fintype n] [NonAssocSemiring α] (i j : n) (b : α) (w : n -> α) :
    single i j b *ᵥ w = (b * w j) • Pi.single i (1 : α) := by
  ext
  simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply]

/--
lemma `sum_single_eq_diagonal` / 引理 `sum_single_eq_diagonal`

English:
lemma sum_single_eq_diagonal
  given: [AddCommMonoid α] [Fintype m] (f : m -> α)
  proof: by
  ext j k
  rw [sum_apply]; rw [diagonal_apply]; rw [Finset.sum_eq_single j] <;> simp +contextual [single]

中文:
引理 sum_single_eq_diagonal
  条件: [加法交换幺半群 α] [有限类型 m] (f : m -> α)
  证明: by
  ext j k
  rw [sum_apply]; rw [diagonal_apply]; rw [Finset.sum_eq_single j] <;> simp +contextual [single]

Depends on / 依赖: Finset, Finset.sum_eq_single, contextual, diagonal_apply, single, sum_apply, sum_eq_single
-/
lemma sum_single_eq_diagonal [AddCommMonoid α] [Fintype m] (f : m -> α) :
    ∑ i : m, single i i (f i) = Matrix.diagonal f := by
  ext j k
  rw [sum_apply]; rw [diagonal_apply]; rw [Finset.sum_eq_single j] <;> simp +contextual [single]

/--
lemma `sum_single_one` / 引理 `sum_single_one`

English:
lemma sum_single_one
  given: [AddCommMonoid α] [One α] [Fintype m]
  proof: sum_single_eq_diagonal _

中文:
引理 sum_single_one
  条件: [加法交换幺半群 α] [幺 α] [有限类型 m]
  证明: sum_single_eq_diagonal _

Depends on / 依赖: sum_single_eq_diagonal
-/
lemma sum_single_one [AddCommMonoid α] [One α] [Fintype m] :
    ∑ i : m, single i i (1 : α) = 1 :=
  sum_single_eq_diagonal _

/--
lemma `sum_single_natCast` / 引理 `sum_single_natCast`

English:
lemma sum_single_natCast
  given: [AddCommMonoidWithOne α] [Fintype m] (n : Nat)
  proof: sum_single_eq_diagonal _

中文:
引理 sum_single_natCast
  条件: [加法交换带幺幺半群 α] [有限类型 m] (n : 自然数)
  证明: sum_single_eq_diagonal _

Depends on / 依赖: sum_single_eq_diagonal
-/
lemma sum_single_natCast [AddCommMonoidWithOne α] [Fintype m] (n : Nat) :
    ∑ i : m, single i i (n : α) = n :=
  sum_single_eq_diagonal _

/--
lemma `sum_single_ofNat` / 引理 `sum_single_ofNat`

English:
lemma sum_single_ofNat
  given: [AddCommMonoidWithOne α] [Fintype m] (n : Nat) [n.AtLeastTwo]
  proof: sum_single_eq_diagonal _

中文:
引理 sum_single_of自然数
  条件: [加法交换带幺幺半群 α] [有限类型 m] (n : 自然数) [n.AtLeastTwo]
  证明: sum_single_eq_diagonal _

Depends on / 依赖: sum_single_eq_diagonal
-/
lemma sum_single_ofNat [AddCommMonoidWithOne α] [Fintype m] (n : Nat) [n.AtLeastTwo] :
    ∑ i : m, single i i (ofNat(n) : α) = ofNat(n) :=
  sum_single_eq_diagonal _

/--
lemma `sum_single_intCast` / 引理 `sum_single_intCast`

English:
lemma sum_single_intCast
  given: [AddCommGroupWithOne α] [Fintype m] (z : Int)
  proof: sum_single_eq_diagonal _

中文:
引理 sum_single_intCast
  条件: [加法交换带幺群 α] [有限类型 m] (z : 整数)
  证明: sum_single_eq_diagonal _

Depends on / 依赖: sum_single_eq_diagonal
-/
lemma sum_single_intCast [AddCommGroupWithOne α] [Fintype m] (z : Int) :
    ∑ i : m, single i i (z : α) = z :=
  sum_single_eq_diagonal _

/--
theorem `sum_sum_single` / 定理 `sum_sum_single`

English:
theorem sum_sum_single
  given: [AddCommMonoid α] [Fintype m] [Fintype n] (x : m -> n -> α)
  proof: by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [single, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk_inj]

中文:
定理 sum_sum_single
  条件: [加法交换幺半群 α] [有限类型 m] [有限类型 n] (x : m -> n -> α)
  证明: by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [single, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk_inj]

Depends on / 依赖: Fintype, Fintype.sum_prod_type, Matrix, Matrix.of_apply, Matrix.sum_apply, Prod.mk_inj, mk_inj, of_apply, single, sum_apply, sum_prod_type
-/
theorem sum_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : m -> n -> α) :
    ∑ i : m, ∑ j : n, single i j (x i j) = of x := by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [single, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk_inj]

/--
theorem `matrix_eq_sum_single` / 定理 `matrix_eq_sum_single`

English:
theorem matrix_eq_sum_single
  given: [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix m n α)
  proof: .symm sum_sum_single _

中文:
定理 matrix_eq_sum_single
  条件: [加法交换幺半群 α] [有限类型 m] [有限类型 n] (x : 矩阵 m n α)
  证明: .symm sum_sum_single _

Depends on / 依赖: sum_sum_single
-/
theorem matrix_eq_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, single i j (x i j) :=
.symm sum_sum_single _

/--
theorem `single_eq_single_vecMulVec_single` / 定理 `single_eq_single_vecMulVec_single`

English:
theorem single_eq_single_vecMulVec_single
  given: [MulZeroOneClass α] (i : m) (j : n)
  proof: by
  simp [-mul_ite, single, vecMulVec, ite_and, Pi.single_apply, eq_comm]

中文:
定理 single_eq_single_vecMulVec_single
  条件: [乘零幺类 α] (i : m) (j : n)
  证明: by
  simp [-mul_ite, single, vecMulVec, ite_and, Pi.single_apply, eq_comm]

Depends on / 依赖: Pi.single_apply, eq_comm, ite_and, mul_ite, single, single_apply, vecMulVec
-/
theorem single_eq_single_vecMulVec_single [MulZeroOneClass α] (i : m) (j : n) :
    single i j (1 : α) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  simp [-mul_ite, single, vecMulVec, ite_and, Pi.single_apply, eq_comm]

-- todo: the old proof used fintypes, I don't know `Finsupp` but this feels generalizable
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  proof: by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_single M]; rw [← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis

@[elab_as_elim]

中文:
定理 induction_on'
  证明: by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_single M]; rw [← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis

@[elab_as_elim]
-/
protected theorem induction_on'
    [AddCommMonoid α] [Finite m] [Finite n] {P : Matrix m n α -> Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : forall p q, P p -> P q -> P (p + q))
    (h_std_basis : forall (i : m) (j : n) (x : α), P (single i j x)) : P M := by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_single M]; rw [← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  proof: Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis

中文:
定理 induction_on
  证明: Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis
-/
protected theorem induction_on
    [AddCommMonoid α] [Finite m] [Finite n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α -> Prop} (M : Matrix m n α) (h_add : forall p q, P p -> P q -> P (p + q))
    (h_std_basis : forall i j x, P (single i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis

/-- `Matrix.single` as a bundled additive map. -/
@[simps]
/--
Definition of `singleAddMonoidHom` / `singleAddMonoidHom` 的定义

English:
definition singleAddMonoidHom
  signature: [AddCommMonoid α] (i : m) (j : n)
  body: single i j
  map_zero' := single_zero _ _
  map_add' _ _ := single_add _ _ _ _

中文:
定义 singleAddMonoidHom
  签名: [加法交换幺半群 α] (i : m) (j : n)
  定义体: single i j
  map_zero' := single_zero _ _
  map_add' _ _ := single_add _ _ _ _

Depends on / 依赖: single
-/
def singleAddMonoidHom [AddCommMonoid α] (i : m) (j : n) : α ->+ Matrix m n α where
  toFun := single i j
  map_zero' := single_zero _ _
  map_add' _ _ := single_add _ _ _ _

variable (R)
/-- `Matrix.single` as a bundled linear map. -/
@[simps!]
/--
Definition of `singleLinearMap` / `singleLinearMap` 的定义

English:
definition singleLinearMap
  signature: [Semiring R] [AddCommMonoid α] [Module R α] (i : m) (j : n)
  body: singleAddMonoidHom i j
.symm map_smul' _ _ := smul_single _ _ _ _

中文:
定义 singleLinearMap
  签名: [半环 R] [加法交换幺半群 α] [模 R α] (i : m) (j : n)
  定义体: singleAddMonoidHom i j
.symm map_smul' _ _ := smul_single _ _ _ _

Depends on / 依赖: singleAddMonoidHom
-/
def singleLinearMap [Semiring R] [AddCommMonoid α] [Module R α] (i : m) (j : n) :
    α ->ₗ[R] Matrix m n α where
  __ := singleAddMonoidHom i j
.symm map_smul' _ _ := smul_single _ _ _ _

section ext

/-- Additive maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
/--
theorem `ext_addMonoidHom` / 定理 `ext_addMonoidHom`

English:
theorem ext_addMonoidHom
  proof: by
  cases nonempty_fintype m
  cases nonempty_fintype n
  ext x
  rw [matrix_eq_sum_single x]
  simp_rw [map_sum]
  congr! 2
  exact DFunLike.congr_fun (h _ _) _

中文:
定理 ext_addMonoidHom
  证明: by
  cases nonempty_fintype m
  cases nonempty_fintype n
  ext x
  rw [matrix_eq_sum_single x]
  simp_rw [map_sum]
  congr! 2
  exact DFunLike.congr_fun (h _ _) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_sum, matrix_eq_sum_single, nonempty_fintype, simp_rw
-/
theorem ext_addMonoidHom
    [Finite m] [Finite n] [AddCommMonoid α] [AddCommMonoid β] ⦃f g : Matrix m n α ->+ β⦄
    (h : forall i j, f.comp (singleAddMonoidHom i j) = g.comp (singleAddMonoidHom i j)) :
    f = g := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  ext x
  rw [matrix_eq_sum_single x]
  simp_rw [map_sum]
  congr! 2
  exact DFunLike.congr_fun (h _ _) _

/-- Linear maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
/--
theorem `ext_linearMap` / 定理 `ext_linearMap`

English:
theorem ext_linearMap
  proof: LinearMap.toAddMonoidHom_injective ext_addMonoidHom fun i j =>
congrArg LinearMap.toAddMonoidHom h i j

中文:
定理 ext_linearMap
  证明: LinearMap.toAddMonoidHom_injective ext_addMonoidHom fun i j =>
congrArg LinearMap.toAddMonoidHom h i j

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom, LinearMap.toAddMonoidHom_injective, ext_addMonoidHom, toAddMonoidHom, toAddMonoidHom_injective
-/
theorem ext_linearMap
    [Finite m] [Finite n] [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    ⦃f g : Matrix m n α ->ₗ[R] β⦄
    (h : forall i j, f ∘ₗ singleLinearMap R i j = g ∘ₗ singleLinearMap R i j) :
    f = g :=
LinearMap.toAddMonoidHom_injective ext_addMonoidHom fun i j =>
congrArg LinearMap.toAddMonoidHom h i j

section liftLinear
variable {R} (S)
variable [Fintype m] [Fintype n] [Semiring R] [Semiring S] [AddCommMonoid α] [AddCommMonoid β]
variable [Module R α] [Module R β] [Module S β] [SMulCommClass R S β]

/--
Definition of `liftLinear` / `liftLinear` 的定义

English:
definition liftLinear
  signature: : (m -> n -> α ->ₗ[R] β) ≃ₗ[S] (Matrix m n α ->ₗ[R] β)
  body: LinearEquiv.piCongrRight (fun _ => LinearMap.lsum R _ S) ≪≫ₗ LinearMap.lsum R _ S ≪≫ₗ
    LinearEquiv.congrLeft _ _ (ofLinearEquiv _)

中文:
定义 liftLinear
  签名: : (m -> n -> α ->ₗ[R] β) ≃ₗ[S] (矩阵 m n α ->ₗ[R] β)
  定义体: LinearEquiv.piCongrRight (fun _ => LinearMap.lsum R _ S) ≪≫ₗ LinearMap.lsum R _ S ≪≫ₗ
    LinearEquiv.congrLeft _ _ (ofLinearEquiv _)

Depends on / 依赖: LinearEquiv, LinearEquiv.congrLeft, LinearEquiv.piCongrRight, LinearMap, LinearMap.lsum, congrLeft, ofLinearEquiv, piCongrRight
-/
def liftLinear : (m -> n -> α ->ₗ[R] β) ≃ₗ[S] (Matrix m n α ->ₗ[R] β) :=
  LinearEquiv.piCongrRight (fun _ => LinearMap.lsum R _ S) ≪≫ₗ LinearMap.lsum R _ S ≪≫ₗ
    LinearEquiv.congrLeft _ _ (ofLinearEquiv _)

-- not `simp` to let `liftLinear_single` fire instead
/--
theorem `liftLinear_apply` / 定理 `liftLinear_apply`

English:
theorem liftLinear_apply
  given: (f : m -> n -> α ->ₗ[R] β) (M : Matrix m n α)
  proof: by
  simp [liftLinear, map_sum, LinearEquiv.congrLeft]

中文:
定理 liftLinear_apply
  条件: (f : m -> n -> α ->ₗ[R] β) (M : 矩阵 m n α)
  证明: by
  simp [liftLinear, map_sum, LinearEquiv.congrLeft]

Depends on / 依赖: LinearEquiv, LinearEquiv.congrLeft, congrLeft, liftLinear, map_sum
-/
theorem liftLinear_apply (f : m -> n -> α ->ₗ[R] β) (M : Matrix m n α) :
    liftLinear S f M = ∑ i, ∑ j, f i j (M i j) := by
  simp [liftLinear, map_sum, LinearEquiv.congrLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `liftLinear_single` / 定理 `liftLinear_single`

English:
theorem liftLinear_single
  given: (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n) (a : α)
  proof: by
  dsimp [liftLinear, -LinearMap.lsum_apply, LinearEquiv.congrLeft, LinearEquiv.piCongrRight]
  simp_rw [of_symm_single, LinearMap.lsum_piSingle]

@[simp]

中文:
定理 liftLinear_single
  条件: (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n) (a : α)
  证明: by
  dsimp [liftLinear, -LinearMap.lsum_apply, LinearEquiv.congrLeft, LinearEquiv.piCongrRight]
  simp_rw [of_symm_single, LinearMap.lsum_piSingle]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.congrLeft, LinearEquiv.piCongrRight, LinearMap, LinearMap.lsum_apply, LinearMap.lsum_piSingle, congrLeft, liftLinear, lsum_apply, lsum_piSingle, of_symm_single, piCongrRight, simp_rw
-/
theorem liftLinear_single (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n) (a : α) :
    liftLinear S f (Matrix.single i j a) = f i j a := by
  dsimp [liftLinear, -LinearMap.lsum_apply, LinearEquiv.congrLeft, LinearEquiv.piCongrRight]
  simp_rw [of_symm_single, LinearMap.lsum_piSingle]

@[simp]
/--
theorem `liftLinear_comp_singleLinearMap` / 定理 `liftLinear_comp_singleLinearMap`

English:
theorem liftLinear_comp_singleLinearMap
  given: (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n)
  proof: LinearMap.ext liftLinear_single S f i j

@[simp]

中文:
定理 liftLinear_comp_singleLinearMap
  条件: (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n)
  证明: LinearMap.ext liftLinear_single S f i j

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, liftLinear_single
-/
theorem liftLinear_comp_singleLinearMap (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n) :
    liftLinear S f ∘ₗ Matrix.singleLinearMap _ i j = f i j :=
LinearMap.ext liftLinear_single S f i j

@[simp]
/--
theorem `liftLinear_singleLinearMap` / 定理 `liftLinear_singleLinearMap`

English:
theorem liftLinear_singleLinearMap
  given: [Module S α] [SMulCommClass R S α]
  proof: ext_linearMap _ liftLinear_comp_singleLinearMap _ _

中文:
定理 liftLinear_singleLinearMap
  条件: [模 S α] [标量交换类 R S α]
  证明: ext_linearMap _ liftLinear_comp_singleLinearMap _ _

Depends on / 依赖: Matrix
-/
theorem liftLinear_singleLinearMap [Module S α] [SMulCommClass R S α] :
    liftLinear S (Matrix.singleLinearMap R) = .id (M := Matrix m n α) :=
ext_linearMap _ liftLinear_comp_singleLinearMap _ _

end liftLinear

end ext

section
variable [Zero α] (i j : n) (c : α)

-- This simp lemma should take priority over `diag_apply`
@[simp 1050]
/--
theorem `diag_single_of_ne` / 定理 `diag_single_of_ne`

English:
theorem diag_single_of_ne
  given: (h : i != j)
  statement: diag (single i j c) = 0
  proof: funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₁.trans e₂.symm)

中文:
定理 diag_single_of_ne
  条件: (h : i != j)
  结论: diag (single i j c) = 0
  证明: funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₁.trans e₂.symm)

Depends on / 依赖: if_neg
-/
theorem diag_single_of_ne (h : i != j) : diag (single i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₁.trans e₂.symm)

-- This simp lemma should take priority over `diag_apply`
@[simp 1050]
/--
theorem `diag_single_same` / 定理 `diag_single_same`

English:
theorem diag_single_same
  statement: diag (single i i c) = Pi.single i c
  proof: by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]

中文:
定理 diag_single_same
  结论: diag (single i i c) = 依赖函数类型.single i c
  证明: by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]
-/
theorem diag_single_same : diag (single i i c) = Pi.single i c := by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]

end

section mul
variable [Fintype m] [NonUnitalNonAssocSemiring α] (c : α)

omit [DecidableEq n] in
@[simp]
/--
theorem `single_mul_apply_same` / 定理 `single_mul_apply_same`

English:
theorem single_mul_apply_same
  given: (i : l) (j : m) (b : n) (M : Matrix m n α)
  proof: by simp [mul_apply, single]

omit [DecidableEq l] in
@[simp]

中文:
定理 single_mul_apply_same
  条件: (i : l) (j : m) (b : n) (M : 矩阵 m n α)
  证明: by simp [mul_apply, single]

omit [DecidableEq l] in
@[simp]

Depends on / 依赖: mul_apply, single
-/
theorem single_mul_apply_same (i : l) (j : m) (b : n) (M : Matrix m n α) :
    (single i j c * M) i b = c * M j b := by simp [mul_apply, single]

omit [DecidableEq l] in
@[simp]
/--
theorem `mul_single_apply_same` / 定理 `mul_single_apply_same`

English:
theorem mul_single_apply_same
  given: (i : m) (j : n) (a : l) (M : Matrix l m α)
  proof: by simp [mul_apply, single]

omit [DecidableEq n] in
@[simp]

中文:
定理 mul_single_apply_same
  条件: (i : m) (j : n) (a : l) (M : 矩阵 l m α)
  证明: by simp [mul_apply, single]

omit [DecidableEq n] in
@[simp]

Depends on / 依赖: mul_apply, single
-/
theorem mul_single_apply_same (i : m) (j : n) (a : l) (M : Matrix l m α) :
    (M * single i j c) a j = M a i * c := by simp [mul_apply, single]

omit [DecidableEq n] in
@[simp]
/--
theorem `single_mul_apply_of_ne` / 定理 `single_mul_apply_of_ne`

English:
theorem single_mul_apply_of_ne
  given: (i : l) (j : m) (a : l) (b : n) (h : a != i) (M : Matrix m n α)
  proof: by simp [mul_apply, h.symm]

omit [DecidableEq l] in
@[simp]

中文:
定理 single_mul_apply_of_ne
  条件: (i : l) (j : m) (a : l) (b : n) (h : a != i) (M : 矩阵 m n α)
  证明: by simp [mul_apply, h.symm]

omit [DecidableEq l] in
@[simp]

Depends on / 依赖: h.symm, mul_apply
-/
theorem single_mul_apply_of_ne (i : l) (j : m) (a : l) (b : n) (h : a != i) (M : Matrix m n α) :
    (single i j c * M) a b = 0 := by simp [mul_apply, h.symm]

omit [DecidableEq l] in
@[simp]
/--
theorem `mul_single_apply_of_ne` / 定理 `mul_single_apply_of_ne`

English:
theorem mul_single_apply_of_ne
  given: (i : m) (j : n) (a : l) (b : n) (hbj : b != j) (M : Matrix l m α)
  proof: by simp [mul_apply, hbj.symm]

@[simp]

中文:
定理 mul_single_apply_of_ne
  条件: (i : m) (j : n) (a : l) (b : n) (hbj : b != j) (M : 矩阵 l m α)
  证明: by simp [mul_apply, hbj.symm]

@[simp]

Depends on / 依赖: MySubobject, MySubobject.carrier, carrier, hbj.symm, mul_apply
-/
theorem mul_single_apply_of_ne (i : m) (j : n) (a : l) (b : n) (hbj : b != j) (M : Matrix l m α) :
    (M * single i j c) a b = 0 := by simp [mul_apply, hbj.symm]

@[simp]
/--
theorem `single_mul_single_same` / 定理 `single_mul_single_same`

English:
theorem single_mul_single_same
  given: (i : l) (j : m) (k : n) (d : α)
  proof: by
  ext a b
  simp only [mul_apply, single]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]

@[simp]

中文:
定理 single_mul_single_same
  条件: (i : l) (j : m) (k : n) (d : α)
  证明: by
  ext a b
  simp only [mul_apply, single]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]

@[simp]

Depends on / 依赖: MySubobject, mul_apply, ofSetLike, single
-/
theorem single_mul_single_same (i : l) (j : m) (k : n) (d : α) :
    single i j c * single j k d = single i k (c * d) := by
  ext a b
  simp only [mul_apply, single]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]

@[simp]
/--
theorem `single_mul_mul_single` / 定理 `single_mul_mul_single`

English:
theorem single_mul_mul_single
  statement: [Fintype n]
  proof: by
  ext i'' j''
  simp only [mul_apply, single]
  by_cases h₁ : i = i'' <;> by_cases h₂ : j = j'' <;> simp [h₁, h₂]

@[simp]

中文:
定理 single_mul_mul_single
  结论: [有限类型 n]
  证明: by
  ext i'' j''
  simp only [mul_apply, single]
  by_cases h₁ : i = i'' <;> by_cases h₂ : j = j'' <;> simp [h₁, h₂]

@[simp]

Depends on / 依赖: mul_apply, single
-/
theorem single_mul_mul_single [Fintype n]
    (i : l) (i' : m) (j' : n) (j : o) (a : α) (x : Matrix m n α) (b : α) :
    single i i' a * x * single j' j b = single i j (a * x i' j' * b) := by
  ext i'' j''
  simp only [mul_apply, single]
  by_cases h₁ : i = i'' <;> by_cases h₂ : j = j'' <;> simp [h₁, h₂]

@[simp]
/--
theorem `single_mul_single_of_ne` / 定理 `single_mul_single_of_ne`

English:
theorem single_mul_single_of_ne
  given: (i : l) (j k : m) {l : n} (h : j != k) (d : α)
  proof: by
  ext a b
  simp only [mul_apply, single, of_apply]
  by_cases h₁ : i = a
  · simp [h₁, h, Finset.sum_eq_zero]
  · simp [h₁]

中文:
定理 single_mul_single_of_ne
  条件: (i : l) (j k : m) {l : n} (h : j != k) (d : α)
  证明: by
  ext a b
  simp only [mul_apply, single, of_apply]
  by_cases h₁ : i = a
  · simp [h₁, h, Finset.sum_eq_zero]
  · simp [h₁]

Depends on / 依赖: Finset, Finset.sum_eq_zero, mul_apply, of_apply, single, sum_eq_zero
-/
theorem single_mul_single_of_ne (i : l) (j k : m) {l : n} (h : j != k) (d : α) :
    single i j c * single k l d = 0 := by
  ext a b
  simp only [mul_apply, single, of_apply]
  by_cases h₁ : i = a
  · simp [h₁, h, Finset.sum_eq_zero]
  · simp [h₁]

end mul

section Commute

variable [Fintype n] [Semiring α]

/--
theorem `row_eq_zero_of_commute_single` / 定理 `row_eq_zero_of_commute_single`

English:
theorem row_eq_zero_of_commute_single
  statement: {i j k : n} {M : Matrix n n α}
  proof: by
  have := ext_iff.mpr hM i k
  simp_all

中文:
定理 row_eq_zero_of_commute_single
  结论: {i j k : n} {M : 矩阵 n n α}
  证明: by
  have := ext_iff.mpr hM i k
  simp_all

Depends on / 依赖: Membership, ext_iff, ext_iff.mpr, instMembership
-/
theorem row_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) (hkj : k != j) : M j k = 0 := by
  have := ext_iff.mpr hM i k
  simp_all

/--
theorem `col_eq_zero_of_commute_single` / 定理 `col_eq_zero_of_commute_single`

English:
theorem col_eq_zero_of_commute_single
  statement: {i j k : n} {M : Matrix n n α}
  proof: by
  have := ext_iff.mpr hM k j
  simp_all

中文:
定理 col_eq_zero_of_commute_single
  结论: {i j k : n} {M : 矩阵 n n α}
  证明: by
  have := ext_iff.mpr hM k j
  simp_all

Depends on / 依赖: CoeSort, ext_iff, ext_iff.mpr
-/
theorem col_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) (hki : k != i) : M k i = 0 := by
  have := ext_iff.mpr hM k j
  simp_all

/--
theorem `diag_eq_of_commute_single` / 定理 `diag_eq_of_commute_single`

English:
theorem diag_eq_of_commute_single
  statement: {i j : n} {M : Matrix n n α}
  proof: by
  have := ext_iff.mpr hM i j
  simp_all

中文:
定理 diag_eq_of_commute_single
  结论: {i j : n} {M : 矩阵 n n α}
  证明: by
  have := ext_iff.mpr hM i j
  simp_all

Depends on / 依赖: ext_iff, ext_iff.mpr
-/
theorem diag_eq_of_commute_single {i j : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) : M i i = M j j := by
  have := ext_iff.mpr hM i j
  simp_all

/--
theorem `mem_range_scalar_of_commute_single` / 定理 `mem_range_scalar_of_commute_single`

English:
theorem mem_range_scalar_of_commute_single
  statement: {M : Matrix n n α}
  proof: by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_single (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_single (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_single (hM hij) hkl.symm]

中文:
定理 mem_range_scalar_of_commute_single
  结论: {M : 矩阵 n n α}
  证明: by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_single (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_single (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_single (hM hij) hkl.symm]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Matrix, Matrix.ext, Nonempty, Subsingleton, Subsingleton.elim, col_eq_zero_of_commute_single, diag_eq_of_commute_single, diagonal_apply_eq, diagonal_apply_ne, eq_or_ne, hkl.sym, hkl.symm, isEmpty_or_nonempty, row_eq_zero_of_commute_single, scalar_apply
-/
theorem mem_range_scalar_of_commute_single {M : Matrix n n α}
    (hM : Pairwise fun i j => Commute (single i j 1) M) :
    M in Set.range (Matrix.scalar n) := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_single (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_single (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_single (hM hij) hkl.symm]

/--
theorem `mem_range_scalar_iff_commute_single` / 定理 `mem_range_scalar_iff_commute_single`

English:
theorem mem_range_scalar_iff_commute_single
  given: {M : Matrix n n α}
  proof: by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_single⟩
  rw [scalar_commute_iff]
  simp

中文:
定理 mem_range_scalar_iff_commute_single
  条件: {M : 矩阵 n n α}
  证明: by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_single⟩
  rw [scalar_commute_iff]
  simp

Depends on / 依赖: Commute, Commute.symm, mem_range_scalar_of_commute_single, scalar_commute_iff
-/
theorem mem_range_scalar_iff_commute_single {M : Matrix n n α} :
    M in Set.range (Matrix.scalar n) ↔ forall (i j : n), i != j -> Commute (single i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_single⟩
  rw [scalar_commute_iff]
  simp

/--
theorem `mem_range_scalar_iff_commute_single'` / 定理 `mem_range_scalar_iff_commute_single'`

English:
theorem mem_range_scalar_iff_commute_single'
  given: {M : Matrix n n α}
  proof: by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
fun hM => mem_range_scalar_iff_commute_single.mpr fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp

中文:
定理 mem_range_scalar_iff_commute_single'
  条件: {M : 矩阵 n n α}
  证明: by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
fun hM => mem_range_scalar_iff_commute_single.mpr fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp

Depends on / 依赖: Commute, Commute.symm, coe_set_eq, coe_set_eq.symm, mem_range_scalar_iff_commute_single, mem_range_scalar_iff_commute_single.mpr, scalar_commute_iff
-/
theorem mem_range_scalar_iff_commute_single' {M : Matrix n n α} :
    M in Set.range (Matrix.scalar n) ↔ forall (i j : n), Commute (single i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
fun hM => mem_range_scalar_iff_commute_single.mpr fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp

/--
theorem `center_eq_scalar_image` / 定理 `center_eq_scalar_image`

English:
theorem center_eq_scalar_image
  proof: Set.ext fun x => by
  simp_rw [Set.mem_image, Semigroup.mem_center_iff]
.symm⟩ refine ⟨fun hx => ?_, fun ⟨x, hx, eq⟩ y => eq ▸ scalar_commute x (hx · |>.symm) y
  refine (isEmpty_or_nonempty n).elim (fun _ => ⟨0, by simp [nontriviality]⟩) fun ⟨i⟩ => ?_
  obtain ⟨x, rfl⟩ := mem_range_scalar_iff_commute_single'.mpr fun _ _ => hx _
  exact ⟨x, by simpa using fun r => congr($(hx (single i i r)) i i)⟩

中文:
定理 center_eq_scalar_image
  证明: Set.ext fun x => by
  simp_rw [Set.mem_image, Semigroup.mem_center_iff]
.symm⟩ refine ⟨fun hx => ?_, fun ⟨x, hx, eq⟩ y => eq ▸ scalar_commute x (hx · |>.symm) y
  refine (isEmpty_or_nonempty n).elim (fun _ => ⟨0, by simp [nontriviality]⟩) fun ⟨i⟩ => ?_
  obtain ⟨x, rfl⟩ := mem_range_scalar_iff_commute_single'.mpr fun _ _ => hx _
  exact ⟨x, by simpa using fun r => congr($(hx (single i i r)) i i)⟩

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff, Set.ext, Set.mem_image, isEmpty_or_nonempty, mem_center_iff, mem_image, mem_range_scalar_iff_commute_single, nontriviality, scalar_commute, simp_rw, single
-/
theorem center_eq_scalar_image :
    Set.center (Matrix n n α) = scalar n '' Set.center α := Set.ext fun x => by
  simp_rw [Set.mem_image, Semigroup.mem_center_iff]
.symm⟩ refine ⟨fun hx => ?_, fun ⟨x, hx, eq⟩ y => eq ▸ scalar_commute x (hx · |>.symm) y
  refine (isEmpty_or_nonempty n).elim (fun _ => ⟨0, by simp [nontriviality]⟩) fun ⟨i⟩ => ?_
  obtain ⟨x, rfl⟩ := mem_range_scalar_iff_commute_single'.mpr fun _ _ => hx _
  exact ⟨x, by simpa using fun r => congr($(hx (single i i r)) i i)⟩

/--
theorem `submonoidCenter_eq_scalar_map` / 定理 `submonoidCenter_eq_scalar_map`

English:
theorem submonoidCenter_eq_scalar_map
  proof: SetLike.coe_injective center_eq_scalar_image

中文:
定理 submonoidCenter_eq_scalar_map
  证明: SetLike.coe_injective center_eq_scalar_image

Depends on / 依赖: SetLike, SetLike.coe_injective, center_eq_scalar_image, coe_injective
-/
theorem submonoidCenter_eq_scalar_map :
    Submonoid.center (Matrix n n α) = (Submonoid.center α).map (scalar n) :=
  SetLike.coe_injective center_eq_scalar_image

/--
theorem `subsemigroupCenter_eq_scalar_map` / 定理 `subsemigroupCenter_eq_scalar_map`

English:
theorem subsemigroupCenter_eq_scalar_map
  proof: SetLike.coe_injective center_eq_scalar_image

中文:
定理 subsemigroupCenter_eq_scalar_map
  证明: SetLike.coe_injective center_eq_scalar_image

Depends on / 依赖: SetLike, SetLike.coe_injective, center_eq_scalar_image, coe_injective
-/
theorem subsemigroupCenter_eq_scalar_map :
    Subsemigroup.center (Matrix n n α) = (Subsemigroup.center α).map (scalar n).toMulHom :=
  SetLike.coe_injective center_eq_scalar_image

/--
theorem `subsemiringCenter_eq_scalar_map` / 定理 `subsemiringCenter_eq_scalar_map`

English:
theorem subsemiringCenter_eq_scalar_map
  proof: SetLike.coe_injective center_eq_scalar_image

中文:
定理 subsemiringCenter_eq_scalar_map
  证明: SetLike.coe_injective center_eq_scalar_image

Depends on / 依赖: SetLike, SetLike.coe_injective, center_eq_scalar_image, coe_injective
-/
theorem subsemiringCenter_eq_scalar_map :
    Subsemiring.center (Matrix n n α) = (Subsemiring.center α).map (scalar n) :=
  SetLike.coe_injective center_eq_scalar_image

/--
theorem `subringCenter_eq_scalar_map` / 定理 `subringCenter_eq_scalar_map`

English:
theorem subringCenter_eq_scalar_map
  given: [Ring R]
  proof: SetLike.coe_injective center_eq_scalar_image

中文:
定理 subringCenter_eq_scalar_map
  条件: [环 R]
  证明: SetLike.coe_injective center_eq_scalar_image

Depends on / 依赖: SetLike, SetLike.coe_injective, center_eq_scalar_image, coe_injective
-/
theorem subringCenter_eq_scalar_map [Ring R] :
    Subring.center (Matrix n n R) = (Subring.center R).map (scalar n) :=
  SetLike.coe_injective center_eq_scalar_image

/--
theorem `center_eq_range` / 定理 `center_eq_range`

English:
theorem center_eq_range
  given: [CommSemiring R]
  proof: by
  rw [center_eq_scalar_image]; rw [Set.center_eq_univ]; rw [Set.image_univ]

中文:
定理 center_eq_range
  条件: [交换半环 R]
  证明: by
  rw [center_eq_scalar_image]; rw [Set.center_eq_univ]; rw [Set.image_univ]
-/
@[simp] theorem center_eq_range [CommSemiring R] :
    Set.center (Matrix n n R) = Set.range (scalar n) := by
  rw [center_eq_scalar_image]; rw [Set.center_eq_univ]; rw [Set.image_univ]

end Commute

end Matrix
