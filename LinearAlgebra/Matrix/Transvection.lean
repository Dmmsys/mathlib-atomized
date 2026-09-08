/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.Field
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Transvections

Transvections are matrices of the form `1 + single i j c`, where `single i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L * D * L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `transvection i j c` is the matrix equal to `1 + single i j c`.
* `TransvectionStruct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 * ... * t_k * D * t'_1 * ... * t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `Fin r ⊕ Unit`, where `Fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/

@[expose] public section


universe u₁ u₂

namespace Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]
variable [DecidableEq n] [DecidableEq p]
variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/-- The transvection matrix `transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `transvection i j c * M`) corresponds to adding
`c` times the `j`-th row of `M` to its `i`-th row. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
/-
**Matrix.transvection** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transvection (c : R) : Matrix n n R
参数：c : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transvection matrix `transvection i j c` is equal to the identity plus `c` a
t position
`(i, j)`. Multiplying by it on the left (as in `transvection i j c * M`) corresp
onds to adding
`c` times the `j`-th row of `M` to its `i`-th row. Multiplying by it on the righ
t corresponds
to adding `c` times the `i`-th column to the `j`-th column.
-/
def transvection (c : R) : Matrix n n R :=
  1 + Matrix.single i j c

@[simp]
/-
**Matrix.transvection_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transvection_zero : transvection i j (0 : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_zero`：single_zero (i : m) (j : n) : single i j (0 : α) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transvection_zero : transvection i j (0 : R) = 1 := by simp [transvection]

section

/-- A transvection matrix is obtained from the identity by adding `c` times the `j`-th row to
the `i`-th row. -/
/-
**Matrix.updateRow_eq_transvection** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：updateRow_eq_transvection [Finite n] (c : R) : updateRow (1 : Matrix n n R
) i ((1 : Matrix n n R) i + c • (1 : Matrix n n R) j) = transvection i j c
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False

--- 原说明 ---
A transvection matrix is obtained from the identity by adding `c` times the `j`-
th row to
the `i`-th row.
-/
theorem updateRow_eq_transvection [Finite n] (c : R) :
    updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) i + c • (1 : Matrix n n R) j) =
      transvection i j c := by
  cases nonempty_fintype n
  ext a b
  by_cases ha : i = a
  · by_cases hb : j = b
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_one, transvection, add_apply, single_apply_same]
    · simp only [ha, updateRow_self, Pi.add_apply, one_apply, Pi.smul_apply, hb, ↓reduceIte,
        smul_eq_mul, mul_zero, add_zero, transvection, add_apply, and_false, not_false_eq_true,
        single_apply_of_ne]
  · simp only [updateRow_ne, transvection, ha, Ne.symm ha, single_apply_of_ne, add_zero,
      Ne, not_false_iff,
      false_and, add_apply]

variable [Fintype n]
/-
**Matrix.transvection_mul_transvection_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transvection_mul_transvection_same (h : i != j) (c d : R) : transvection i
 j c * transvection i j d = transvection i j (c + d)
参数：h : i != j；c d : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.single_mul_single_of_ne`：single_mul_single_of_ne (i : l) (j k : m
) {l : n} (h : j != k) (d : α) : single i j c * single k l d = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Matrix.single_add`：single_add [AddZeroClass α] (i : m) (j : n) (a b : α)
 : single i j (a + b) = single i j a + single i j b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transvection_mul_transvection_same (h : i ≠ j) (c d : R) :
    transvection i j c * transvection i j d = transvection i j (c + d) := by
  simp [transvection, Matrix.add_mul, Matrix.mul_add, h.symm, add_assoc,
    single_add]

@[simp]
/-
**Matrix.transvection_mul_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transvection_mul_apply_same {m : Type*} (b : m) (c : R) (M : Matrix n m R)
 : (transvection i j c * M) i b = M i b + c * M j b
参数：b : m；c : R；M : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.single_mul_apply_same`：single_mul_apply_same (i : l) (j : m) (b :
 n) (M : Matrix m n α) : (single i j c * M) i b = c * M j b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transvection_mul_apply_same {m : Type*} (b : m) (c : R) (M : Matrix n m R) :
    (transvection i j c * M) i b = M i b + c * M j b := by simp [transvection, Matrix.add_mul]

@[simp]
/-
**Matrix.mul_transvection_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_transvection_apply_same {m : Type*} (a : m) (c : R) (M : Matrix m n R)
 : (M * transvection i j c) a j = M a j + c * M a i
参数：a : m；c : R；M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_single_apply_same`：mul_single_apply_same (i : m) (j : n) (a :
 l) (M : Matrix l m α) : (M * single i j c) a j = M a i * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_transvection_apply_same {m : Type*} (a : m) (c : R) (M : Matrix m n R) :
    (M * transvection i j c) a j = M a j + c * M a i := by
  simp [transvection, Matrix.mul_add, mul_comm]

@[simp]
/-
**Matrix.transvection_mul_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transvection_mul_apply_of_ne {m : Type*} (a : n) (b : m) (ha : a != i) (c 
: R) (M : Matrix n m R) : (transvection i j c * M) a b = M a b
参数：a : n；b : m；ha : a != i；c : R；M : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.single_mul_apply_of_ne`：single_mul_apply_of_ne (i : l) (j : m) (a
 : l) (b : n) (h : a != i) (M : Matrix m n α) : (single i j c * M) a b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transvection_mul_apply_of_ne {m : Type*} (a : n) (b : m) (ha : a ≠ i) (c : R)
    (M : Matrix n m R) :
    (transvection i j c * M) a b = M a b := by simp [transvection, Matrix.add_mul, ha]

@[simp]
/-
**Matrix.mul_transvection_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_transvection_apply_of_ne {m : Type*} (a : m) (b : n) (hb : b != j) (c 
: R) (M : Matrix m n R) : (M * transvection i j c) a b = M a b
参数：a : m；b : n；hb : b != j；c : R；M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_single_apply_of_ne`：mul_single_apply_of_ne (i : m) (j : n) (a
 : l) (b : n) (hbj : b != j) (M : Matrix l m α) : (M * single i j c) a b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_transvection_apply_of_ne {m : Type*} (a : m) (b : n) (hb : b ≠ j) (c : R)
    (M : Matrix m n R) :
    (M * transvection i j c) a b = M a b := by simp [transvection, Matrix.mul_add, hb]

@[simp]
/-
**Matrix.det_transvection_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_transvection_of_ne (h : i != j) (c : R) : det (transvection i j c) = 1
参数：h : i != j；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.updateRow_eq_transvection`：updateRow_eq_transvection [Finite n] (
c : R) : updateRow (1 : Matrix n n R) i ((1 : Matrix n n R) i + c • (1 : Matrix 
n n R) j) = transvecti…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.det_updateRow_add_smul_self`：det_updateRow_add_smul_self (A : Mat
rix n n R) {i j : n} (hij : i != j) (c : R) : det (updateRow A i (A i + c • A j)
) = det A
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
-/
theorem det_transvection_of_ne (h : i ≠ j) (c : R) : det (transvection i j c) = 1 := by
  rw [← updateRow_eq_transvection i j, det_updateRow_add_smul_self _ h, det_one]

end

variable (R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
/-
**Matrix.TransvectionStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：Type u_1 → Type u₂ → Type (max u_1 u₂)
参数：max u_1 u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure containing all the information from which one can build a nontrivial
 transvection.
This structure is easier to manipulate than transvections as one has a direct ac
cess to all the
relevant fields.
-/
structure TransvectionStruct where
  (i j : n)
  hij : i ≠ j
  c : R
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial n] : Nonempty (TransvectionStruct n R) := by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

namespace TransvectionStruct

variable {R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
/-
**Matrix.TransvectionStruct.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Transvect
ionStruct`。
形式化陈述：toMatrix (t : TransvectionStruct n R) : Matrix n n R
参数：t : TransvectionStruct n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associating to a `transvection_struct` the corresponding transvection matrix.
-/
def toMatrix (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c

@[simp]
/-
**Matrix.TransvectionStruct.toMatrix_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Transv
ectionStruct`。
形式化陈述：toMatrix_mk (i j : n) (hij : i != j) (c : R) : TransvectionStruct.toMatrix
 ⟨i, j, hij, c⟩ = transvection i j c
参数：i j : n；hij : i != j；c : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMatrix_mk (i j : n) (hij : i ≠ j) (c : R) :
    TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ = transvection i j c :=
  rfl

@[simp]
/-
**Matrix.TransvectionStruct.det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.TransvectionSt
ruct`。
形式化陈述：∀ {n : Type u_1} {R : Type u₂} [inst : DecidableEq n] [inst_1 : CommRing R
] [inst_2 : Fintype n]   (t : Matrix.TransvectionStruct n R), t.toMatrix.det = 1
参数：t : Matrix.TransvectionStruct n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_transvection_of_ne`：det_transvection_of_ne (h : i != j) (c : 
R) : det (transvection i j c) = 1
· 使用定理 `Matrix.TransvectionStruct.hij`：∀ {n : Type u_1} {R : Type u₂} (self : Ma
trix.TransvectionStruct n R), self.i ≠ self.j
-/
protected theorem det [Fintype n] (t : TransvectionStruct n R) : det t.toMatrix = 1 :=
  det_transvection_of_ne _ _ t.hij _

@[simp]
/-
**Matrix.TransvectionStruct.det_toMatrix_prod** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
TransvectionStruct`。
形式化陈述：det_toMatrix_prod [Fintype n] (L : List (TransvectionStruct n R)) : det (L
.map toMatrix).prod = 1
参数：L : List (TransvectionStruct n R)。
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
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.TransvectionStruct.det`：∀ {n : Type u_1} {R : Type u₂} [inst : De
cidableEq n] [inst_1 : CommRing R] [inst_2 : Fintype n]   (t : Matrix.Transvecti
onStruct n R), t.to…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem det_toMatrix_prod [Fintype n] (L : List (TransvectionStruct n R)) :
    det (L.map toMatrix).prod = 1 := by
  induction L with
  | nil => simp
  | cons _ _ IH => simp [IH]

/-- The inverse of a `TransvectionStruct`, designed so that `t.inv.toMatrix` is the inverse of
`t.toMatrix`. -/
@[simps]
/-
**Matrix.TransvectionStruct.inv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.TransvectionSt
ruct`。
形式化陈述：{n : Type u_1} → {R : Type u₂} → [CommRing R] → Matrix.TransvectionStruct 
n R → Matrix.TransvectionStruct n R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.TransvectionStruct.hij`：∀ {n : Type u_1} {R : Type u₂} (self : Ma
trix.TransvectionStruct n R), self.i ≠ self.j

--- 原说明 ---
The inverse of a `TransvectionStruct`, designed so that `t.inv.toMatrix` is the 
inverse of
`t.toMatrix`.
-/
protected def inv (t : TransvectionStruct n R) : TransvectionStruct n R where
  i := t.i
  j := t.j
  hij := t.hij
  c := -t.c

section

variable [Fintype n]

/-
**Matrix.TransvectionStruct.inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Transvecti
onStruct`。
形式化陈述：inv_mul (t : TransvectionStruct n R) : t.inv.toMatrix * t.toMatrix = 1
参数：t : TransvectionStruct n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.TransvectionStruct.inv_i`：∀ {n : Type u_1} {R : Type u₂} [inst : 
CommRing R] (t : Matrix.TransvectionStruct n R), t.inv.i = t.i
· 使用定理 `Matrix.TransvectionStruct.inv_j`：∀ {n : Type u_1} {R : Type u₂} [inst : 
CommRing R] (t : Matrix.TransvectionStruct n R), t.inv.j = t.j
· 使用定理 `Matrix.TransvectionStruct.inv_c`：∀ {n : Type u_1} {R : Type u₂} [inst : 
CommRing R] (t : Matrix.TransvectionStruct n R), t.inv.c = -t.c
· 使用定理 `Matrix.transvection_mul_transvection_same`：transvection_mul_transvection
_same (h : i != j) (c d : R) : transvection i j c * transvection i j d = transve
ction i j (c + d)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Matrix.transvection_zero`：transvection_zero : transvection i j (0 : R) =
 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_mul (t : TransvectionStruct n R) : t.inv.toMatrix * t.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]
/-
**Matrix.TransvectionStruct.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Transvecti
onStruct`。
形式化陈述：mul_inv (t : TransvectionStruct n R) : t.toMatrix * t.inv.toMatrix = 1
参数：t : TransvectionStruct n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.TransvectionStruct.inv_i`：∀ {n : Type u_1} {R : Type u₂} [inst : 
CommRing R] (t : Matrix.TransvectionStruct n R), t.inv.i = t.i
· 使用定理 `Matrix.TransvectionStruct.inv_j`：∀ {n : Type u_1} {R : Type u₂} [inst : 
CommRing R] (t : Matrix.TransvectionStruct n R), t.inv.j = t.j
· 使用定理 `Matrix.TransvectionStruct.inv_c`：∀ {n : Type u_1} {R : Type u₂} [inst : 
CommRing R] (t : Matrix.TransvectionStruct n R), t.inv.c = -t.c
· 使用定理 `Matrix.transvection_mul_transvection_same`：transvection_mul_transvection
_same (h : i != j) (c d : R) : transvection i j c * transvection i j d = transve
ction i j (c + d)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Matrix.transvection_zero`：transvection_zero : transvection i j (0 : R) =
 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_inv (t : TransvectionStruct n R) : t.toMatrix * t.inv.toMatrix = 1 := by
  rcases t with ⟨_, _, t_hij⟩
  simp [toMatrix, transvection_mul_transvection_same, t_hij]
/-
**Matrix.TransvectionStruct.reverse_inv_prod_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 
`Matrix.TransvectionStruct`。
形式化陈述：reverse_inv_prod_mul_prod (L : List (TransvectionStruct n R)) : (L.reverse
.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod = 1
参数：L : List (TransvectionStruct n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `Matrix.TransvectionStruct.inv_mul`：inv_mul (t : TransvectionStruct n R) 
: t.inv.toMatrix * t.toMatrix = 1
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
-/
theorem reverse_inv_prod_mul_prod (L : List (TransvectionStruct n R)) :
    (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (t.inv.toMatrix * t.toMatrix) *
          (L.map toMatrix).prod = 1
      by simpa [Matrix.mul_assoc]
    simpa [inv_mul] using IH
/-
**Matrix.TransvectionStruct.prod_mul_reverse_inv_prod** 是 Mathlib 中的一个定理，位于命名空间 
`Matrix.TransvectionStruct`。
形式化陈述：prod_mul_reverse_inv_prod (L : List (TransvectionStruct n R)) : (L.map toM
atrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod = 1
参数：L : List (TransvectionStruct n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.TransvectionStruct.mul_inv`：mul_inv (t : TransvectionStruct n R) 
: t.toMatrix * t.inv.toMatrix = 1
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
-/
theorem prod_mul_reverse_inv_prod (L : List (TransvectionStruct n R)) :
    (L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L IH =>
    suffices
      t.toMatrix *
            ((L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) *
          t.inv.toMatrix = 1
      by simpa [Matrix.mul_assoc]
    simp_rw [IH, Matrix.mul_one, t.mul_inv]
/-
**Matrix.TransvectionStruct.isUnit_prod_comp_inverse** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix.TransvectionStruct`。
形式化陈述：isUnit_prod_comp_inverse (L : List (TransvectionStruct n R)) : IsUnit (L.m
ap (toMatrix ∘ .inv)).prod
参数：L : List (TransvectionStruct n R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.TransvectionStruct.reverse_inv_prod_mul_prod`：reverse_inv_prod_mu
l_prod (L : List (TransvectionStruct n R)) : (L.reverse.map (toMatrix ∘ Transvec
tionStruct.inv)).prod * (L.map toMatrix).…
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem isUnit_prod_comp_inverse (L : List (TransvectionStruct n R)) :
    IsUnit (L.map (toMatrix ∘ .inv)).prod := by
  refine IsUnit.of_mul_eq_one (L.reverse.map toMatrix).prod ?_
  rw [← reverse_inv_prod_mul_prod L.reverse, L.reverse_reverse]

/-- `M` is a scalar matrix if it commutes with every nontrivial transvection (elementary matrix). -/
/-
**Matrix.TransvectionStruct._root_.Matrix.mem_range_scalar_of_commute_transvecti
onStruct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.TransvectionStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` is a scalar matrix if it commutes with every nontrivial transvection (elemen
tary matrix).
-/
theorem _root_.Matrix.mem_range_scalar_of_commute_transvectionStruct {M : Matrix n n R}
    (hM : ∀ t : TransvectionStruct n R, Commute t.toMatrix M) :
    M ∈ Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_single ?_
  intro i j hij
  simpa [transvection, mul_add, add_mul] using! (hM ⟨i, j, hij, 1⟩).eq
/-
**Matrix.TransvectionStruct._root_.Matrix.mem_range_scalar_iff_commute_transvect
ionStruct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.TransvectionStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.mem_range_scalar_iff_commute_transvectionStruct {M : Matrix n n R} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ t : TransvectionStruct n R, Commute t.toMatrix M := by
  refine ⟨fun h t => ?_, mem_range_scalar_of_commute_transvectionStruct⟩
  rw [mem_range_scalar_iff_commute_single] at h
  refine (Commute.one_left M).add_left ?_
  convert! (h _ _ t.hij).smul_left t.c using 1
  rw [smul_single, smul_eq_mul, mul_one]

end

open Sum

/-- Given a `TransvectionStruct` on `n`, define the corresponding `TransvectionStruct` on `n ⊕ p`
using the identity on `p`. -/
/-
**Matrix.TransvectionStruct.sumInl** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Transvectio
nStruct`。
形式化陈述：sumInl (t : TransvectionStruct n R) : TransvectionStruct (n oplus p) R whe
re i
参数：t : TransvectionStruct n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `TransvectionStruct` on `n`, define the corresponding `TransvectionStruc
t` on `n ⊕ p`
using the identity on `p`.
-/
def sumInl (t : TransvectionStruct n R) : TransvectionStruct (n ⊕ p) R where
  i := inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c
/-
**Matrix.TransvectionStruct.toMatrix_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Tr
ansvectionStruct`。
形式化陈述：toMatrix_sumInl (t : TransvectionStruct n R) : (t.sumInl p).toMatrix = fro
mBlocks t.toMatrix 0 0 1
参数：t : TransvectionStruct n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.TransvectionStruct.toMatrix.congr_simp`：∀ {n : Type u_1} {R : Typ
e u₂} {inst : DecidableEq n} [inst_1 : DecidableEq n] [inst_2 : CommRing R]   (t
 t_1 : Matrix.TransvectionStruct n …
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toMatrix_sumInl (t : TransvectionStruct n R) :
    (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1 := by
  cases t
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h, single]
  · simp [TransvectionStruct.sumInl, transvection]
  · simp [TransvectionStruct.sumInl, transvection]
  · by_cases h : a = b <;> simp [TransvectionStruct.sumInl, transvection, h]

@[simp]
/-
**Matrix.TransvectionStruct.sumInl_toMatrix_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix.TransvectionStruct`。
形式化陈述：sumInl_toMatrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R) (L : L
ist (TransvectionStruct n R)) (N : Matrix p p R) : (L.map (toMatrix ∘ sumInl p))
.prod * fromBlocks M 0 0 N = fromBlocks ((L.map toMatrix).prod * M) 0 0 N
参数：M : Matrix n n R；L : List (TransvectionStruct n R)；N : Matrix p p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Matrix.TransvectionStruct.toMatrix_sumInl`：toMatrix_sumInl (t : Transvec
tionStruct n R) : (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem sumInl_toMatrix_prod_mul [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    (L.map (toMatrix ∘ sumInl p)).prod * fromBlocks M 0 0 N =
      fromBlocks ((L.map toMatrix).prod * M) 0 0 N := by
  induction L with
  | nil => simp
  | cons t L IH => simp [Matrix.mul_assoc, IH, toMatrix_sumInl, fromBlocks_multiply]

@[simp]
/-
**Matrix.TransvectionStruct.mul_sumInl_toMatrix_prod** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix.TransvectionStruct`。
形式化陈述：mul_sumInl_toMatrix_prod [Fintype n] [Fintype p] (M : Matrix n n R) (L : L
ist (TransvectionStruct n R)) (N : Matrix p p R) : fromBlocks M 0 0 N * (L.map (
toMatrix ∘ sumInl p)).prod = fromBlocks (M * (L.map toMatrix).prod) 0 0 N
参数：M : Matrix n n R；L : List (TransvectionStruct n R)；N : Matrix p p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Matrix.TransvectionStruct.toMatrix_sumInl`：toMatrix_sumInl (t : Transvec
tionStruct n R) : (t.sumInl p).toMatrix = fromBlocks t.toMatrix 0 0 1
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mul_sumInl_toMatrix_prod [Fintype n] [Fintype p] (M : Matrix n n R)
    (L : List (TransvectionStruct n R)) (N : Matrix p p R) :
    fromBlocks M 0 0 N * (L.map (toMatrix ∘ sumInl p)).prod =
      fromBlocks (M * (L.map toMatrix).prod) 0 0 N := by
  induction L generalizing M N with
  | nil => simp
  | cons t L IH => simp [IH, toMatrix_sumInl, fromBlocks_multiply]

variable {p}

/-- Given a `TransvectionStruct` on `n` and an equivalence between `n` and `p`, define the
corresponding `TransvectionStruct` on `p`. -/
/-
**Matrix.TransvectionStruct.reindexEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Trans
vectionStruct`。
形式化陈述：reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct
 p R where i
参数：e : n ≃ p；t : TransvectionStruct n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `TransvectionStruct` on `n` and an equivalence between `n` and `p`, defi
ne the
corresponding `TransvectionStruct` on `p`.
-/
def reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : TransvectionStruct p R where
  i := e t.i
  j := e t.j
  hij := by simp [t.hij]
  c := t.c

variable [Fintype n] [Fintype p]
/-
**Matrix.TransvectionStruct.toMatrix_reindexEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix.TransvectionStruct`。
形式化陈述：toMatrix_reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) : (t.reinde
xEquiv e).toMatrix = reindexAlgEquiv R _ e t.toMatrix
参数：e : n ≃ p；t : TransvectionStruct n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
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
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem toMatrix_reindexEquiv (e : n ≃ p) (t : TransvectionStruct n R) :
    (t.reindexEquiv e).toMatrix = reindexAlgEquiv R _ e t.toMatrix := by
  rcases t with ⟨t_i, t_j, _⟩
  ext a b
  simp only [reindexEquiv, transvection, toMatrix_mk]
  by_cases ha : e t_i = a <;> by_cases hb : e t_j = b <;> by_cases hab : a = b <;>
    simp [ha, hb, hab, e.eq_symm_apply, single]
/-
**Matrix.TransvectionStruct.toMatrix_reindexEquiv_prod** 是 Mathlib 中的一个定理，位于命名空间
 `Matrix.TransvectionStruct`。
形式化陈述：toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R))
 : (L.map (toMatrix ∘ reindexEquiv e)).prod = reindexAlgEquiv R _ e (L.map toMat
rix).prod
参数：e : n ≃ p；L : List (TransvectionStruct n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Matrix.submatrix_one_equiv`：submatrix_one_equiv [Zero α] [One α] [Decida
bleEq m] [DecidableEq l] (e : l ≃ m) : (1 : Matrix m m α).submatrix e e = 1
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.TransvectionStruct.toMatrix_reindexEquiv`：toMatrix_reindexEquiv (
e : n ≃ p) (t : TransvectionStruct n R) : (t.reindexEquiv e).toMatrix = reindexA
lgEquiv R _ e t.toMatrix
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
-/
theorem toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R)) :
    (L.map (toMatrix ∘ reindexEquiv e)).prod = reindexAlgEquiv R _ e (L.map toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L IH => simp [toMatrix_reindexEquiv, IH]

end TransvectionStruct

end Transvection

/-!
### Reducing matrices by left and right multiplication by transvections

In this section, we show that any matrix can be reduced to diagonal form by left and right
multiplication by transvections (or, equivalently, by elementary operations on lines and columns).
The main step is to kill the last row and column of a matrix in `Fin r ⊕ Unit` with nonzero last
coefficient, by subtracting this coefficient from the other ones. The list of these operations is
recorded in `list_transvec_col M` and `list_transvec_row M`. We have to analyze inductively how
these operations affect the coefficients in the last row and the last column to conclude that they
have the desired effect.

Once this is done, one concludes the reduction by induction on the size
of the matrices, through a suitable reindexing to identify any fintype with `Fin r ⊕ Unit`.
-/


namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

open Unit Sum TransvectionStruct

/-- A list of transvections such that multiplying on the left with these transvections will replace
the last column with zeroes. -/
/-
**Matrix.Pivot.listTransvecCol** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Pivot`。
形式化陈述：listTransvecCol : List (Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list of transvections such that multiplying on the left with these transvectio
ns will replace
the last column with zeroes.
-/
def listTransvecCol : List (Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inl i) (inr unit) <| -M (inl i) (inr unit) / M (inr unit) (inr unit)

/-- A list of transvections such that multiplying on the right with these transvections will replace
the last row with zeroes. -/
/-
**Matrix.Pivot.listTransvecRow** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Pivot`。
形式化陈述：listTransvecRow : List (Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list of transvections such that multiplying on the right with these transvecti
ons will replace
the last row with zeroes.
-/
def listTransvecRow : List (Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inr unit) (inl i) <| -M (inr unit) (inl i) / M (inr unit) (inr unit)

@[simp]
/-
**Matrix.Pivot.length_listTransvecCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：length_listTransvecCol : (listTransvecCol M).length = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_listTransvecCol : (listTransvecCol M).length = r := by simp [listTransvecCol]
/-
**Matrix.Pivot.listTransvecCol_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：listTransvecCol_getElem {i : Nat} (h : i < (listTransvecCol M).length) : (
listTransvecCol M)[i] = letI i' : Fin r
参数：h : i < (listTransvecCol M).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.Pivot.length_listTransvecCol`：length_listTransvecCol : (listTrans
vecCol M).length = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem listTransvecCol_getElem {i : ℕ} (h : i < (listTransvecCol M).length) :
    (listTransvecCol M)[i] =
      letI i' : Fin r := ⟨i, length_listTransvecCol M ▸ h⟩
      transvection (inl i') (inr unit) <| -M (inl i') (inr unit) / M (inr unit) (inr unit) := by
  simp [listTransvecCol]

@[simp]
/-
**Matrix.Pivot.length_listTransvecRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：length_listTransvecRow : (listTransvecRow M).length = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_listTransvecRow : (listTransvecRow M).length = r := by simp [listTransvecRow]
/-
**Matrix.Pivot.listTransvecRow_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：listTransvecRow_getElem {i : Nat} (h : i < (listTransvecRow M).length) : (
listTransvecRow M)[i] = letI i' : Fin r
参数：h : i < (listTransvecRow M).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.Pivot.length_listTransvecRow`：length_listTransvecRow : (listTrans
vecRow M).length = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem listTransvecRow_getElem {i : ℕ} (h : i < (listTransvecRow M).length) :
    (listTransvecRow M)[i] =
      letI i' : Fin r := ⟨i, length_listTransvecRow M ▸ h⟩
      transvection (inr unit) (inl i') <| -M (inr unit) (inl i') / M (inr unit) (inr unit) := by
  simp [listTransvecRow]

/-- Multiplying by some of the matrices in `listTransvecCol M` does not change the last row. -/
/-
**Matrix.Pivot.listTransvecCol_mul_last_row_drop** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix.Pivot`。
形式化陈述：listTransvecCol_mul_last_row_drop (i : Fin r oplus Unit) {k : Nat} (hk : k
 <= r) : (((listTransvecCol M).drop k).prod * M) (inr unit) i = M (inr unit) i
参数：i : Fin r oplus Unit；hk : k <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `List.drop_eq_getElem_cons`：∀ {α : Type u_1} {i : ℕ} {l : List α} (h : i 
< l.length), List.drop i l = l[i] :: List.drop (i + 1) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.transvection_mul_apply_of_ne`：transvection_mul_apply_of_ne {m : T
ype*} (a : n) (b : m) (ha : a != i) (c : R) (M : Matrix n m R) : (transvection i
 j c * M) a b = M a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.drop_eq_nil_of_le`：∀ {α : Type u} {as : List α} {i : ℕ}, as.length 
≤ i → List.drop i as = []
· 使用定理 `Matrix.Pivot.length_listTransvecCol`：length_listTransvecCol : (listTrans
vecCol M).length = r
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Multiplying by some of the matrices in `listTransvecCol M` does not change the l
ast row.
-/
theorem listTransvecCol_mul_last_row_drop (i : Fin r ⊕ Unit) {k : ℕ} (hk : k ≤ r) :
    (((listTransvecCol M).drop k).prod * M) (inr unit) i = M (inr unit) i := by
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    rw [List.drop_eq_getElem_cons hn']
    simpa [listTransvecCol, Matrix.mul_assoc]
  | self =>
    simp only [length_listTransvecCol, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]

/-- Multiplying by all the matrices in `listTransvecCol M` does not change the last row. -/
/-
**Matrix.Pivot.listTransvecCol_mul_last_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pi
vot`。
形式化陈述：listTransvecCol_mul_last_row (i : Fin r oplus Unit) : ((listTransvecCol M)
.prod * M) (inr unit) i = M (inr unit) i
参数：i : Fin r oplus Unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `Matrix.Pivot.listTransvecCol_mul_last_row_drop`：listTransvecCol_mul_last
_row_drop (i : Fin r oplus Unit) {k : Nat} (hk : k <= r) : (((listTransvecCol M)
.drop k).prod * M) (inr unit) i = M …
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Multiplying by all the matrices in `listTransvecCol M` does not change the last 
row.
-/
theorem listTransvecCol_mul_last_row (i : Fin r ⊕ Unit) :
    ((listTransvecCol M).prod * M) (inr unit) i = M (inr unit) i := by
  simpa using listTransvecCol_mul_last_row_drop M i zero_le

/-- Multiplying by all the matrices in `listTransvecCol M` kills all the coefficients in the
last column but the last one. -/
/-
**Matrix.Pivot.listTransvecCol_mul_last_col** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pi
vot`。
形式化陈述：listTransvecCol_mul_last_col (hM : M (inr unit) (inr unit) != 0) (i : Fin 
r) : ((listTransvecCol M).prod * M) (inl i) (inr unit) = 0
参数：hM : M (inr unit) (inr unit) != 0；i : Fin r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `List.drop_eq_getElem_cons`：∀ {α : Type u_1} {i : ℕ} {l : List α} (h : i 
< l.length), List.drop i l = l[i] :: List.drop (i + 1) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.transvection_mul_apply_same`：transvection_mul_apply_same {m : Typ
e*} (b : m) (c : R) (M : Matrix n m R) : (transvection i j c * M) i b = M i b + 
c * M j b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Matrix.Pivot.listTransvecCol_mul_last_row_drop`：listTransvecCol_mul_last
_row_drop (i : Fin r oplus Unit) {k : Nat} (hk : k <= r) : (((listTransvecCol M)
.drop k).prod * M) (inr unit) i = M …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
Multiplying by all the matrices in `listTransvecCol M` kills all the coefficient
s in the
last column but the last one.
-/
theorem listTransvecCol_mul_last_col (hM : M (inr unit) (inr unit) ≠ 0) (i : Fin r) :
    ((listTransvecCol M).prod * M) (inl i) (inr unit) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r →
        (((listTransvecCol M).drop k).prod * M) (inl i) (inr unit) =
          if k ≤ i then 0 else M (inl i) (inr unit) by
    simpa [List.drop] using H 0
  intro k hk
  induction hk using Nat.decreasingInduction with
  | of_succ n hn IH =>
    have hn' : n < (listTransvecCol M).length := by simpa [listTransvecCol] using hn
    let n' : Fin r := ⟨n, hn⟩
    rw [List.drop_eq_getElem_cons hn']
    have A :
      (listTransvecCol M)[n] =
        transvection (inl n') (inr unit) (-M (inl n') (inr unit) / M (inr unit) (inr unit)) := by
      simp [n', listTransvecCol]
    simp only [Matrix.mul_assoc, A, List.prod_cons]
    by_cases h : n' = i
    · have hni : n = i := by
        cases i
        simp only [n', Fin.mk_eq_mk] at h
        simp [h]
      simp only [h, transvection_mul_apply_same, IH, ← hni, add_le_iff_nonpos_right,
          listTransvecCol_mul_last_row_drop _ _ hn]
      simp [field]
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        simp [n'] at h
      simp only [ne_eq, inl.injEq, Ne.symm h, not_false_eq_true, transvection_mul_apply_of_ne]
      rw [IH]
      rcases le_or_gt (n + 1) i with (hi | hi)
      · simp only [hi, n.le_succ.trans hi, if_true]
      · rw [if_neg, if_neg]
        · simpa only [hni.symm, not_le, or_false] using Nat.lt_succ_iff_lt_or_eq.1 hi
        · simpa only [not_le] using hi
  | self =>
    simp only [length_listTransvecCol, le_refl, List.drop_eq_nil_of_le, List.prod_nil,
      Matrix.one_mul]
    rw [if_neg]
    simpa only [not_le] using i.2

/-- Multiplying by some of the matrices in `listTransvecRow M` does not change the last column. -/
/-
**Matrix.Pivot.mul_listTransvecRow_last_col_take** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix.Pivot`。
形式化陈述：mul_listTransvecRow_last_col_take (i : Fin r oplus Unit) {k : Nat} (hk : k
 <= r) : (M * ((listTransvecRow M).take k).prod) i (inr unit) = M i (inr unit)
参数：i : Fin r oplus Unit；hk : k <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.getElem?_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α}, (L
ist.ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `List.take_add_one`：∀ {α : Type u_1} {l : List α} {i : ℕ}, List.take (i +
 1) l = List.take i l ++ l[i]?.toList
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Matrix.mul_transvection_apply_of_ne`：mul_transvection_apply_of_ne {m : T
ype*} (a : m) (b : n) (hb : b != j) (c : R) (M : Matrix m n R) : (M * transvecti
on i j c) a b = M a b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Multiplying by some of the matrices in `listTransvecRow M` does not change the l
ast column.
-/
theorem mul_listTransvecRow_last_col_take (i : Fin r ⊕ Unit) {k : ℕ} (hk : k ≤ r) :
    (M * ((listTransvecRow M).take k).prod) i (inr unit) = M i (inr unit) := by
  induction k with
  | zero => simp only [Matrix.mul_one, List.prod_nil, List.take, Matrix.mul_one]
  | succ k IH =>
    have hkr : k < r := hk
    let k' : Fin r := ⟨k, hkr⟩
    have :
      (listTransvecRow M)[k]? =
        ↑(transvection (inr Unit.unit) (inl k')
            (-M (inr Unit.unit) (inl k') / M (inr Unit.unit) (inr Unit.unit))) := by
      simp only [k', listTransvecRow, hkr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_add_one, ← Matrix.mul_assoc, this, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    rw [mul_transvection_apply_of_ne, IH hkr.le]
    simp only [Ne, not_false_iff, reduceCtorEq]

/-- Multiplying by all the matrices in `listTransvecRow M` does not change the last column. -/
/-
**Matrix.Pivot.mul_listTransvecRow_last_col** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pi
vot`。
形式化陈述：mul_listTransvecRow_last_col (i : Fin r oplus Unit) : (M * (listTransvecRo
w M).prod) i (inr unit) = M i (inr unit)
参数：i : Fin r oplus Unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_length`：∀ {α : Type u_1} {l : List α}, List.take l.length l = 
l
· 使用定理 `Matrix.Pivot.mul_listTransvecRow_last_col_take`：mul_listTransvecRow_last
_col_take (i : Fin r oplus Unit) {k : Nat} (hk : k <= r) : (M * ((listTransvecRo
w M).take k).prod) i (inr unit) = M …
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Multiplying by all the matrices in `listTransvecRow M` does not change the last 
column.
-/
theorem mul_listTransvecRow_last_col (i : Fin r ⊕ Unit) :
    (M * (listTransvecRow M).prod) i (inr unit) = M i (inr unit) := by
  have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
  rw [← List.take_length (l := listTransvecRow M), A]
  simpa using mul_listTransvecRow_last_col_take M i le_rfl

/-- Multiplying by all the matrices in `listTransvecRow M` kills all the coefficients in the
last row but the last one. -/
/-
**Matrix.Pivot.mul_listTransvecRow_last_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pi
vot`。
形式化陈述：mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) != 0) (i : Fin 
r) : (M * (listTransvecRow M).prod) (inr unit) (inl i) = 0
参数：hM : M (inr unit) (inr unit) != 0；i : Fin r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem?_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α}, (L
ist.ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `List.take_add_one`：∀ {α : Type u_1} {l : List α} {i : ℕ}, List.take (i +
 1) l = List.take i l ++ l[i]?.toList
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Matrix.mul_transvection_apply_same`：mul_transvection_apply_same {m : Typ
e*} (a : m) (c : R) (M : Matrix m n R) : (M * transvection i j c) a j = M a j + 
c * M a i
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Matrix.Pivot.mul_listTransvecRow_last_col_take`：mul_listTransvecRow_last
_col_take (i : Fin r oplus Unit) {k : Nat} (hk : k <= r) : (M * ((listTransvecRo
w M).take k).prod) i (inr unit) = M …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
Multiplying by all the matrices in `listTransvecRow M` kills all the coefficient
s in the
last row but the last one.
-/
theorem mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0) (i : Fin r) :
    (M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  suffices H :
    ∀ k : ℕ,
      k ≤ r →
        (M * ((listTransvecRow M).take k).prod) (inr unit) (inl i) =
          if k ≤ i then M (inr unit) (inl i) else 0 by
    have A : (listTransvecRow M).length = r := by simp [listTransvecRow]
    rw [← List.take_length (l := listTransvecRow M), A]
    have : ¬r ≤ i := by simp
    simpa only [this, ite_eq_right_iff] using! H r le_rfl
  intro k hk
  induction k with
  | zero => simp
  | succ n IH =>
    have hnr : n < r := hk
    let n' : Fin r := ⟨n, hnr⟩
    have A :
      (listTransvecRow M)[n]? =
        ↑(transvection (inr unit) (inl n')
        (-M (inr unit) (inl n') / M (inr unit) (inr unit))) := by
      simp only [n', listTransvecRow, hnr, dif_pos, List.getElem?_ofFn]
    simp only [List.take_add_one, A, ← Matrix.mul_assoc, List.prod_append, Matrix.mul_one,
      List.prod_cons, List.prod_nil, Option.toList_some]
    by_cases h : n' = i
    · have hni : n = i := by
        cases i
        simp only [n', Fin.mk_eq_mk] at h
        simp only [h]
      have : ¬n.succ ≤ i := by simp only [← hni, n.lt_succ_self, not_le]
      simp only [h, mul_transvection_apply_same, if_false,
        mul_listTransvecRow_last_col_take _ _ hnr.le, hni.le, this, if_true, IH hnr.le]
      field
    · have hni : n ≠ i := by
        rintro rfl
        cases i
        tauto
      simp only [IH hnr.le, Ne, mul_transvection_apply_of_ne, Ne.symm h, inl.injEq,
        not_false_eq_true]
      rcases le_or_gt (n + 1) i with (hi | hi)
      · simp [hi, n.le_succ.trans hi]
      · rw [if_neg, if_neg]
        · simpa only [not_le] using! hi
        · simpa only [hni.symm, not_le, or_false] using! Nat.lt_succ_iff_lt_or_eq.1 hi

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` kills
all the coefficients in the last row but the last one. -/
/-
**Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_col** 是 Mathlib 中的一个
定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：listTransvecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr u
nit) != 0) (i : Fin r) : ((listTransvecCol M).prod * M * (listTransvecRow M).pro
d) (inr unit) (inl i) = 0
参数：hM : M (inr unit) (inr unit) != 0；i : Fin r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.Pivot.listTransvecCol_mul_last_row`：listTransvecCol_mul_last_row 
(i : Fin r oplus Unit) : ((listTransvecCol M).prod * M) (inr unit) i = M (inr un
it) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.Pivot.mul_listTransvecRow_last_row`：mul_listTransvecRow_last_row 
(hM : M (inr unit) (inr unit) != 0) (i : Fin r) : (M * (listTransvecRow M).prod)
 (inr unit) (inl i) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecR
ow M` kills
all the coefficients in the last row but the last one.
-/
theorem listTransvecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inr unit) (inl i) = 0 := by
  have : listTransvecRow M = listTransvecRow ((listTransvecCol M).prod * M) := by
    simp [listTransvecRow, listTransvecCol_mul_last_row]
  rw [this]
  apply mul_listTransvecRow_last_row
  simpa [listTransvecCol_mul_last_row] using hM

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` kills
all the coefficients in the last column but the last one. -/
/-
**Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_row** 是 Mathlib 中的一个
定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：listTransvecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr u
nit) != 0) (i : Fin r) : ((listTransvecCol M).prod * M * (listTransvecRow M).pro
d) (inl i) (inr unit) = 0
参数：hM : M (inr unit) (inr unit) != 0；i : Fin r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.Pivot.mul_listTransvecRow_last_col`：mul_listTransvecRow_last_col 
(i : Fin r oplus Unit) : (M * (listTransvecRow M).prod) i (inr unit) = M i (inr 
unit)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.Pivot.listTransvecCol_mul_last_col`：listTransvecCol_mul_last_col 
(hM : M (inr unit) (inr unit) != 0) (i : Fin r) : ((listTransvecCol M).prod * M)
 (inl i) (inr unit) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecR
ow M` kills
all the coefficients in the last column but the last one.
-/
theorem listTransvecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) ≠ 0)
    (i : Fin r) :
    ((listTransvecCol M).prod * M * (listTransvecRow M).prod) (inl i) (inr unit) = 0 := by
  have : listTransvecCol M = listTransvecCol (M * (listTransvecRow M).prod) := by
    simp [listTransvecCol, mul_listTransvecRow_last_col]
  rw [this, Matrix.mul_assoc]
  apply listTransvecCol_mul_last_col
  simpa [mul_listTransvecRow_last_col] using hM

/-- Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecRow M` turns
the matrix in block-diagonal form. -/
/-
**Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow** 是 Ma
thlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow (hM : M (inr un
it) (inr unit) != 0) : IsTwoBlockDiagonal ((listTransvecCol M).prod * M * (listT
ransvecRow M).prod)
参数：hM : M (inr unit) (inr unit) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_row`：listTrans
vecCol_mul_mul_listTransvecRow_last_row (hM : M (inr unit) (inr unit) != 0) (i :
 Fin r) : ((listTransvecCol M).prod * M * (listTran…
· 使用定理 `Matrix.Pivot.listTransvecCol_mul_mul_listTransvecRow_last_col`：listTrans
vecCol_mul_mul_listTransvecRow_last_col (hM : M (inr unit) (inr unit) != 0) (i :
 Fin r) : ((listTransvecCol M).prod * M * (listTran…

--- 原说明 ---
Multiplying by all the matrices either in `listTransvecCol M` and `listTransvecR
ow M` turns
the matrix in block-diagonal form.
-/
theorem isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
    (hM : M (inr unit) (inr unit) ≠ 0) :
    IsTwoBlockDiagonal ((listTransvecCol M).prod * M * (listTransvecRow M).prod) := by
  constructor
  · ext i j
    have : j = unit := by simp only
    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
  · ext i j
    have : i = unit := by simp only
    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]

/-- There exist two lists of `TransvectionStruct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal, when the last coefficient is nonzero. -/
/-
**Matrix.Pivot.exists_isTwoBlockDiagonal_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix.Pivot`。
形式化陈述：exists_isTwoBlockDiagonal_of_ne_zero (hM : M (inr unit) (inr unit) != 0) :
 exists L L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜), IsTwoBlockDiagona
l ((L.map toMatrix).prod * M * (L'.map toMatrix).prod)
参数：hM : M (inr unit) (inr unit) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow`
：isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow (hM : M (inr unit) (
inr unit) != 0) : IsTwoBlockDiagonal ((listTransvecCol M).pro…

--- 原说明 ---
There exist two lists of `TransvectionStruct` such that multiplying by them on t
he left and
on the right makes a matrix block-diagonal, when the last coefficient is nonzero
.
-/
theorem exists_isTwoBlockDiagonal_of_ne_zero (hM : M (inr unit) (inr unit) ≠ 0) :
    ∃ L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  let L : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp, -M (inr unit) (inl i) / M (inr unit) (inr unit)⟩
  refine ⟨L, L', ?_⟩
  have A : L.map toMatrix = listTransvecCol M := by simp [L, listTransvecCol, Function.comp_def]
  have B : L'.map toMatrix = listTransvecRow M := by simp [L', listTransvecRow, Function.comp_def]
  rw [A, B]
  exact isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM

/-- There exist two lists of `TransvectionStruct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal. -/
/-
**Matrix.Pivot.exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec** 是
 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec (M : Matrix 
(Fin r oplus Unit) (Fin r oplus Unit) 𝕜) : exists L L' : List (TransvectionStruc
t (Fin r oplus Unit) 𝕜), IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map
 toMatrix).prod)
参数：M : Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.transvection_mul_apply_same`：transvection_mul_apply_same {m : Typ
e*} (b : m) (c : R) (M : Matrix n m R) : (transvection i j c * M) i b = M i b + 
c * M j b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.Pivot.exists_isTwoBlockDiagonal_of_ne_zero`：exists_isTwoBlockDiag
onal_of_ne_zero (hM : M (inr unit) (inr unit) != 0) : exists L L' : List (Transv
ectionStruct (Fin r oplus Unit) 𝕜), IsT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_transvection_apply_same`：mul_transvection_apply_same {m : Typ
e*} (a : m) (c : R) (M : Matrix m n R) : (M * transvection i j c) a j = M a j + 
c * M a i

--- 原说明 ---
There exist two lists of `TransvectionStruct` such that multiplying by them on t
he left and
on the right makes a matrix block-diagonal.
-/
theorem exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :
    ∃ L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  by_cases H : IsTwoBlockDiagonal M
  · refine ⟨List.nil, List.nil, by simpa using H⟩
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) = 0; swap
  · exact exists_isTwoBlockDiagonal_of_ne_zero M hM
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
  have : ∃ i : Fin r, M (inl i) (inr unit) ≠ 0 ∨ M (inr unit) (inl i) ≠ 0 := by
    rcases H with H | H
    · contrapose! H
      rintro i ⟨⟩
      exact (H i).1
    · contrapose! H
      rintro ⟨⟩ j
      exact (H j).2
  rcases this with ⟨i, h | h⟩
  · let M' := transvection (inr Unit.unit) (inl i) 1 * M
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [M', hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    rw [Matrix.mul_assoc] at hLL'
    refine ⟨L ++ [⟨inr unit, inl i, by simp, 1⟩], L', ?_⟩
    simp only [List.map_append, List.prod_append, Matrix.mul_one, toMatrix_mk, List.prod_cons,
      List.prod_nil, List.map, Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
  · let M' := M * transvection (inl i) (inr unit) 1
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [M', hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩
    refine ⟨L, ⟨inl i, inr unit, by simp, 1⟩::L', ?_⟩
    simp only [← Matrix.mul_assoc, toMatrix_mk, List.prod_cons, List.map]
    rw [Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'

/-- Inductive step for the reduction: if one knows that any size `r` matrix can be reduced to
diagonal form by elementary operations, then one deduces it for matrices over `Fin r ⊕ Unit`. -/
/-
**Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction*
* 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction (IH : for
all M : Matrix (Fin r) (Fin r) 𝕜, exists (L₀ L₀' : List (TransvectionStruct (Fin
 r) 𝕜)) (D₀ : Fin r -> 𝕜), (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod 
= diagonal D₀) (M : Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜) : exists (L 
L' : List (TransvectionStruct (Fin r oplus Unit) 𝕜)) (D : Fin r oplus Unit -> 𝕜)
, (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
参数：IH : forall M : Matrix (Fin r) (Fin r) 𝕜, exists (L₀ L₀' : List (Transvection
Struct (Fin r) 𝕜)) (D₀ : Fin r -> 𝕜), (L₀.map toMatrix).prod * M * (L₀'.map toMa
trix).prod = diagonal D₀；M : Matrix (Fin r oplus Unit) (Fin r oplus Unit) 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Pivot.exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transv
ec`：exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec (M : Matrix (F
in r oplus Unit) (Fin r oplus Unit) 𝕜) : exists L L' : List (Tra…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.fromBlocks_toBlocks`：fromBlocks_toBlocks (M : Matrix (n oplus o) 
(l oplus m) α) : fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ 
= M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.TransvectionStruct.sumInl_toMatrix_prod_mul`：sumInl_toMatrix_prod
_mul [Fintype n] [Fintype p] (M : Matrix n n R) (L : List (TransvectionStruct n 
R)) (N : Matrix p p R) : (L.map (toMatri…
· 使用定理 `Matrix.TransvectionStruct.mul_sumInl_toMatrix_prod`：mul_sumInl_toMatrix_
prod [Fintype n] [Fintype p] (M : Matrix n n R) (L : List (TransvectionStruct n 
R)) (N : Matrix p p R) : fromBlocks M 0 …
· 使用定理 `Matrix.fromBlocks_diagonal`：fromBlocks_diagonal (d₁ : l -> α) (d₂ : m ->
 α) : fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Inductive step for the reduction: if one knows that any size `r` matrix can be r
educed to
diagonal form by elementary operations, then one deduces it for matrices over `F
in r ⊕ Unit`.
-/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
    (IH :
      ∀ M : Matrix (Fin r) (Fin r) 𝕜,
        ∃ (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜)) (D₀ : Fin r → 𝕜),
          (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod = diagonal D₀)
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜) :
    ∃ (L L' : List (TransvectionStruct (Fin r ⊕ Unit) 𝕜)) (D : Fin r ⊕ Unit → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine
    ⟨L₀.map (sumInl Unit) ++ L₁, L₁' ++ L₀'.map (sumInl Unit),
      Sum.elim D₀ fun _ => M' (inr unit) (inr unit), ?_⟩
  suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * M' * (L₀'.map (toMatrix ∘ sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [M', c, Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    rw [← fromBlocks_toBlocks M', hM.1, hM.2]
    rfl
  rw [this]
  simp [h₀]

variable {n p} [Fintype n] [Fintype p]

/-- Reduction to diagonal form by elementary operations is invariant under reindexing. -/
/-
**Matrix.Pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal** 
是 Mathlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix
 p p 𝕜) (e : p ≃ n) (H : exists (L L' : List (TransvectionStruct n 𝕜)) (D : n ->
 𝕜), (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 _ e M * (L'.map toMatrix).
prod = diagonal D) : exists (L L' : List (TransvectionStruct p 𝕜)) (D : p -> 𝕜),
 (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D
参数：M : Matrix p p 𝕜；e : p ≃ n；H : exists (L L' : List (TransvectionStruct n 𝕜)) 
(D : n -> 𝕜), (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 _ e M * (L'.map t
oMatrix).prod = diagonal D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Matrix.TransvectionStruct.toMatrix_reindexEquiv_prod`：toMatrix_reindexEq
uiv_prod (e : n ≃ p) (L : List (TransvectionStruct n R)) : (L.map (toMatrix ∘ re
indexEquiv e)).prod = reindexAlgEquiv R _ …
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
· 使用定理 `Matrix.submatrix_diagonal_equiv`：submatrix_diagonal_equiv [Zero α] [Deci
dableEq m] [DecidableEq l] (d : m -> α) (e : l ≃ m) : (diagonal d).submatrix e e
 = diagonal (d ∘ e)

--- 原说明 ---
Reduction to diagonal form by elementary operations is invariant under reindexin
g.
-/
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix p p 𝕜)
    (e : p ≃ n)
    (H :
      ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
        (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 _ e M * (L'.map toMatrix).prod =
          diagonal D) :
    ∃ (L L' : List (TransvectionStruct p 𝕜)) (D : p → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, ?_⟩
  have : M = reindexAlgEquiv 𝕜 _ e.symm (reindexAlgEquiv 𝕜 _ e M) := by simp
  rw [this]
  simp_rw [List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, h₀]
  simp

/-- Any matrix can be reduced to diagonal form by elementary operations. Formulated here on `Type 0`
because we will make an induction using `Fin r`.
See `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` for the general version (which follows
from this one and reindexing). -/
/-
**Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux** 是 Ma
thlib 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fin
type n] [DecidableEq n] (M : Matrix n n 𝕜) : exists (L L' : List (TransvectionSt
ruct n 𝕜)) (D : n -> 𝕜), (L.map toMatrix).prod * M * (L'.map toMatrix).prod = di
agonal D
参数：n : Type；M : Matrix n n 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.Pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diago
nal`：reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix 
p p 𝕜) (e : p ≃ n) (H : exists (L L' : List (TransvectionStruct n…
· 使用定理 `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_indu
ction`：exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction (IH : fo
rall M : Matrix (Fin r) (Fin r) 𝕜, exists (L₀ L₀' : List (Transvect…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Any matrix can be reduced to diagonal form by elementary operations. Formulated 
here on `Type 0`
because we will make an induction using `Fin r`.
See `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` for the general ver
sion (which follows
from this one and reindexing).
-/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fintype n]
    [DecidableEq n] (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  suffices ∀ cn, Fintype.card n = cn →
      ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D by exact this _ rfl
  intro cn hn
  induction cn generalizing n M with
  | zero =>
    refine ⟨List.nil, List.nil, fun _ => 1, ?_⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
  | succ r IH =>
    have e : n ≃ Fin r ⊕ Unit := by
      refine Fintype.equivOfCardEq ?_
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
    apply
      exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction fun N =>
        IH (Fin r) N (by simp)

/-- Any matrix can be reduced to diagonal form by elementary operations. -/
/-
**Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal** 是 Mathli
b 中的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) 
: exists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜), (L.map toMatrix).p
rod * M * (L'.map toMatrix).prod = diagonal D
参数：M : Matrix n n 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.Pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diago
nal`：reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix 
p p 𝕜) (e : p ≃ n) (H : exists (L L' : List (TransvectionStruct n…
· 使用定理 `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux`
：exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux (n : Type) [Fintype 
n] [DecidableEq n] (M : Matrix n n 𝕜) : exists (L L' : List (…

--- 原说明 ---
Any matrix can be reduced to diagonal form by elementary operations.
-/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections. -/
/-
**Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec** 是 Mathlib 中
的一个定理，位于命名空间 `Matrix.Pivot`。
形式化陈述：exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) : e
xists (L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜), M = (L.map toMatrix).
prod * diagonal D * (L'.map toMatrix).prod
参数：M : Matrix n n 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`：exi
sts_list_transvec_mul_mul_list_transvec_eq_diagonal (M : Matrix n n 𝕜) : exists 
(L L' : List (TransvectionStruct n 𝕜)) (D : n -> 𝕜), (L.m…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.TransvectionStruct.reverse_inv_prod_mul_prod`：reverse_inv_prod_mu
l_prod (L : List (TransvectionStruct n R)) : (L.reverse.map (toMatrix ∘ Transvec
tionStruct.inv)).prod * (L.map toMatrix).…
· 使用定理 `Matrix.TransvectionStruct.prod_mul_reverse_inv_prod`：prod_mul_reverse_in
v_prod (L : List (TransvectionStruct n R)) : (L.map toMatrix).prod * (L.reverse.
map (toMatrix ∘ TransvectionStruct.inv)).…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Any matrix can be written as the product of transvections, a diagonal matrix, an
d
transvections.
-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, ?_⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end Pivot

open Pivot TransvectionStruct

variable {n} [Fintype n]

/-- Induction principle for matrices based on transvections: if a property is true for all diagonal
matrices, all transvections, and is stable under product, then it is true for all matrices. This is
the useful way to say that matrices are generated by diagonal matrices and transvections.

We state a slightly more general version: to prove a property for a matrix `M`, it suffices to
assume that the diagonal matrices we consider have the same determinant as `M`. This is useful to
obtain similar principles for `SLₙ` or `GLₙ`. -/
/-
**Matrix.diagonal_transvection_induction** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_transvection_induction (P : Matrix n n 𝕜 -> Prop) (M : Matrix n n
 𝕜) (hdiag : forall D : n -> 𝕜, det (diagonal D) = det M -> P (diagonal D)) (htr
ansvec : forall t : TransvectionStruct n 𝕜, P t.toMatrix) (hmul : forall A B, P 
A -> P B -> P (A * B)) : P M
参数：P : Matrix n n 𝕜 -> Prop；M : Matrix n n 𝕜；hdiag : forall D : n -> 𝕜, det (dia
gonal D) = det M -> P (diagonal D)；htransvec : forall t : TransvectionStruct n 𝕜
, P t.toMatrix；hmul : forall A B, P A -> P B -> P (A * B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`：exists
_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) : exists (L L' 
: List (TransvectionStruct n 𝕜)) (D : n -> 𝕜), M = (L.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.TransvectionStruct.det_toMatrix_prod`：det_toMatrix_prod [Fintype 
n] (L : List (TransvectionStruct n R)) : det (L.map toMatrix).prod = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…

--- 原说明 ---
Induction principle for matrices based on transvections: if a property is true f
or all diagonal
matrices, all transvections, and is stable under product, then it is true for al
l matrices. This is
the useful way to say that matrices are generated by diagonal matrices and trans
vections.

We state a slightly more general version: to prove a property for a matrix `M`, 
it suffices to
assume that the diagonal matrices we consider have the same determinant as `M`. 
This is useful to
obtain similar principles for `SLₙ` or `GLₙ`.
-/
theorem diagonal_transvection_induction (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜)
    (hdiag : ∀ D : n → 𝕜, det (diagonal D) = det M → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix) (hmul : ∀ A B, P A → P B → P (A * B)) :
    P M := by
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩
  have PD : P (diagonal D) := hdiag D (by simp [h])
  suffices H :
    ∀ (L₁ L₂ : List (TransvectionStruct n 𝕜)) (E : Matrix n n 𝕜),
      P E → P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod) by
    rw [h]
    apply H L L'
    exact PD
  intro L₁ L₂ E PE
  induction L₁ with
  | nil =>
    simp only [Matrix.one_mul, List.prod_nil, List.map]
    induction L₂ generalizing E with
    | nil => simpa
    | cons t L₂ IH =>
      simp only [← Matrix.mul_assoc, List.prod_cons, List.map]
      apply IH
      exact hmul _ _ PE (htransvec _)
  | cons t L₁ IH =>
    simp only [Matrix.mul_assoc, List.prod_cons, List.map] at IH ⊢
    exact hmul _ _ (htransvec _) IH

/-- Induction principle for invertible matrices based on transvections: if a property is true for
all invertible diagonal matrices, all transvections, and is stable under product of invertible
matrices, then it is true for all invertible matrices. This is the useful way to say that
invertible matrices are generated by invertible diagonal matrices and transvections. -/
/-
**Matrix.diagonal_transvection_induction_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Matrix`。
形式化陈述：diagonal_transvection_induction_of_det_ne_zero (P : Matrix n n 𝕜 -> Prop) 
(M : Matrix n n 𝕜) (hMdet : det M != 0) (hdiag : forall D : n -> 𝕜, det (diagona
l D) != 0 -> P (diagonal D)) (htransvec : forall t : TransvectionStruct n 𝕜, P t
.toMatrix) (hmul : forall A B, det A != 0 -> det B != 0 -> P A -> P B -> P (A * 
B)) : P M
参数：P : Matrix n n 𝕜 -> Prop；M : Matrix n n 𝕜；hMdet : det M != 0；hdiag : forall D
 : n -> 𝕜, det (diagonal D) != 0 -> P (diagonal D)；htransvec : forall t : Transv
ectionStruct n 𝕜, P t.toMatrix；hmul : forall A B, det A != 0 -> det B != 0 -> P 
A -> P B -> P (A * B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_transvection_induction`：diagonal_transvection_induction 
(P : Matrix n n 𝕜 -> Prop) (M : Matrix n n 𝕜) (hdiag : forall D : n -> 𝕜, det (d
iagonal D) = det M -> P (dia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.TransvectionStruct.det`：∀ {n : Type u_1} {R : Type u₂} [inst : De
cidableEq n] [inst_1 : CommRing R] [inst_2 : Fintype n]   (t : Matrix.Transvecti
onStruct n R), t.to…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Induction principle for invertible matrices based on transvections: if a propert
y is true for
all invertible diagonal matrices, all transvections, and is stable under product
 of invertible
matrices, then it is true for all invertible matrices. This is the useful way to
 say that
invertible matrices are generated by invertible diagonal matrices and transvecti
ons.
-/
theorem diagonal_transvection_induction_of_det_ne_zero (P : Matrix n n 𝕜 → Prop) (M : Matrix n n 𝕜)
    (hMdet : det M ≠ 0) (hdiag : ∀ D : n → 𝕜, det (diagonal D) ≠ 0 → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n 𝕜, P t.toMatrix)
    (hmul : ∀ A B, det A ≠ 0 → det B ≠ 0 → P A → P B → P (A * B)) : P M := by
  let Q : Matrix n n 𝕜 → Prop := fun N => det N ≠ 0 ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction Q M
    · grind
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2

end Matrix

