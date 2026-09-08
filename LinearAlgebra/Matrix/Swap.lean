/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Data.Matrix.PEquiv

/-!
# Swap matrices

A swap matrix indexed by `i` and `j` is the matrix that, when multiplying another matrix
on the left (resp. on the right), swaps the `i`-th row with the `j`-th row
(resp. the `i`-th column with the `j`-th column).

Swap matrices are a special case of *elementary matrices*. For transvections see
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`.

## Implementation detail

This is a thin wrapper around `(Equiv.swap i j).permMatrix`.
-/

@[expose] public section

namespace Matrix

section Def
variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

variable (R) in
/-- The swap matrix `swap R i j` is the identity matrix with the
`i`-th and `j`-th rows modified such that multiplying by it on the
left (resp. right) corresponds to swapping the `i`-th and `j`-th row (resp. column). -/
/-
**Matrix.swap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：swap (i j : n) : Matrix n n R
参数：i j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The swap matrix `swap R i j` is the identity matrix with the
`i`-th and `j`-th rows modified such that multiplying by it on the
left (resp. right) corresponds to swapping the `i`-th and `j`-th row (resp. colu
mn).
-/
def swap (i j : n) : Matrix n n R :=
  (Equiv.swap i j).permMatrix R
/-
**Matrix.swap_comm** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_comm (i j : n) : swap R i j = swap R j i
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swap_comm (i j : n) :
    swap R i j = swap R j i := by
  simp only [swap, Equiv.swap_comm]

@[simp]
/-
**Matrix.transpose_swap** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transpose_swap (i j : n) : (swap R i j).transpose = swap R i j
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.transpose_permMatrix`：transpose_permMatrix [Zero R] [One R] : (σ.
permMatrix R).transpose = (σ⁻¹).permMatrix R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transpose_swap (i j : n) : (swap R i j).transpose = swap R i j := by
  simp [swap]
/-
**Matrix.isSymm_swap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_swap (i j : n) : (swap R i j).IsSymm
参数：i j : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.transpose_swap`：transpose_swap (i j : n) : (swap R i j).transpose
 = swap R i j
-/
theorem isSymm_swap (i j : n) : (swap R i j).IsSymm :=
  transpose_swap i j

@[simp]
/-
**Matrix.conjTranspose_swap** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_swap {R : Type*} [NonAssocSemiring R] [StarRing R] (i j : n)
 : (swap R i j).conjTranspose = swap R i j
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.conjTranspose_permMatrix`：conjTranspose_permMatrix [NonAssocSemir
ing R] [StarRing R] : (σ.permMatrix R).conjTranspose = (σ⁻¹).permMatrix R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjTranspose_swap {R : Type*} [NonAssocSemiring R] [StarRing R] (i j : n) :
    (swap R i j).conjTranspose = swap R i j := by
  simp [swap]

end Def

section
variable {R n m : Type*} [Semiring R] [DecidableEq n]

@[simp]
/-
**Matrix.map_swap** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：map_swap {S : Type*} [NonAssocSemiring S] (f : R ->+* S) (i j : n) : (swap
 R i j).map f = swap S i j
参数：f : R ->+* S；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PEquiv.map_toMatrix`：map_toMatrix [DecidableEq n] [NonAssocSemiring α] [
NonAssocSemiring β] (f : α ->+* β) (σ : m ≃. n) : σ.toMatrix.map f = σ.toMatrix
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_swap {S : Type*} [NonAssocSemiring S] (f : R →+* S) (i j : n) :
    (swap R i j).map f = swap S i j := by
  simp [swap]

variable [Fintype n]
/-
**Matrix.swap_mulVec** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_mulVec (i j : n) (a : n -> R) : swap R i j *ᵥ a = a ∘ Equiv.swap i j
参数：i j : n；a : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PEquiv.toMatrix_toPEquiv_mulVec`：toMatrix_toPEquiv_mulVec [DecidableEq n
] [Fintype n] [NonAssocSemiring α] (σ : m ≃ n) (a : n -> α) : σ.toPEquiv.toMatri
x *ᵥ a = a ∘ σ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swap_mulVec (i j : n) (a : n → R) :
    swap R i j *ᵥ a = a ∘ Equiv.swap i j := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]
/-
**Matrix.vecMul_swap** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vecMul_swap (i j : n) (a : n -> R) : a ᵥ* swap R i j = a ∘ Equiv.swap i j
参数：i j : n；a : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PEquiv.vecMul_toMatrix_toPEquiv`：vecMul_toMatrix_toPEquiv [DecidableEq n
] [Fintype m] [NonAssocSemiring α] (σ : m ≃ n) (a : m -> α) : a ᵥ* σ.toPEquiv.to
Matrix = a ∘ σ.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vecMul_swap (i j : n) (a : n → R) :
    a ᵥ* swap R i j = a ∘ Equiv.swap i j := by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

@[simp]
/-
**Matrix.swap_mulVec_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_mulVec_apply (i j : n) (a : n -> R) : (swap R i j *ᵥ a) i = a j
参数：i j : n；a : n -> R。
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
· 使用引理 `PEquiv.toMatrix_toPEquiv_mulVec`：toMatrix_toPEquiv_mulVec [DecidableEq n
] [Fintype n] [NonAssocSemiring α] (σ : m ≃ n) (a : n -> α) : σ.toPEquiv.toMatri
x *ᵥ a = a ∘ σ
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swap_mulVec_apply (i j : n) (a : n → R) :
    (swap R i j *ᵥ a) i = a j := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

@[simp]
/-
**Matrix.vecMul_swap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vecMul_swap_apply (i j : n) (a : n -> R) : (a ᵥ* swap R i j) i = a j
参数：i j : n；a : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `PEquiv.vecMul_toMatrix_toPEquiv`：vecMul_toMatrix_toPEquiv [DecidableEq n
] [Fintype m] [NonAssocSemiring α] (σ : m ≃ n) (a : m -> α) : a ᵥ* σ.toPEquiv.to
Matrix = a ∘ σ.symm
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vecMul_swap_apply (i j : n) (a : n → R) :
    (a ᵥ* swap R i j) i = a j := by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

/-- Multiplying with `swap R i j` on the left swaps the `i`-th row with the `j`-th row. -/
@[simp]
/-
**Matrix.swap_mul_apply_left** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_mul_apply_left (i j : n) (a : m) (g : Matrix n m R) : (swap R i j * g
) i a = g j a
参数：i j : n；a : m；g : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.toMatrix_toPEquiv_mul`：toMatrix_toPEquiv_mul [Fintype m] [Decidab
leEq m] [NonAssocSemiring α] (f : l ≃ m) (M : Matrix m n α) : f.toPEquiv.toMatri
x * M = M.submatri…
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Multiplying with `swap R i j` on the left swaps the `i`-th row with the `j`-th r
ow.
-/
lemma swap_mul_apply_left (i j : n) (a : m) (g : Matrix n m R) :
    (swap R i j * g) i a = g j a := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul]

/-- Multiplying with `swap R i j` on the left swaps the `j`-th row with the `i`-th row. -/
@[simp]
/-
**Matrix.swap_mul_apply_right** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_mul_apply_right (i j : n) (a : m) (g : Matrix n m R) : (swap R i j * 
g) j a = g i a
参数：i j : n；a : m；g : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.swap_comm`：swap_comm (i j : n) : swap R i j = swap R j i
· 使用引理 `Matrix.swap_mul_apply_left`：swap_mul_apply_left (i j : n) (a : m) (g : M
atrix n m R) : (swap R i j * g) i a = g j a

--- 原说明 ---
Multiplying with `swap R i j` on the left swaps the `j`-th row with the `i`-th r
ow.
-/
lemma swap_mul_apply_right (i j : n) (a : m) (g : Matrix n m R) :
    (swap R i j * g) j a = g i a := by
  rw [swap_comm, swap_mul_apply_left]
/-
**Matrix.swap_mul_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_mul_of_ne {i j a : n} {b : m} (hai : a != i) (haj : a != j) (g : Matr
ix n m R) : (swap R i j * g) a b = g a b
参数：hai : a != i；haj : a != j；g : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.toMatrix_toPEquiv_mul`：toMatrix_toPEquiv_mul [Fintype m] [Decidab
leEq m] [NonAssocSemiring α] (f : l ≃ m) (M : Matrix m n α) : f.toPEquiv.toMatri
x * M = M.submatri…
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma swap_mul_of_ne {i j a : n} {b : m} (hai : a ≠ i) (haj : a ≠ j) (g : Matrix n m R) :
    (swap R i j * g) a b = g a b := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul, Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Multiplying with `swap R i j` on the right swaps the `i`-th column with the `j`-th column. -/
@[simp]
/-
**Matrix.mul_swap_apply_left** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_swap_apply_left (i j : n) (a : m) (g : Matrix m n R) : (g * swap R i j
) a i = g a j
参数：i j : n；a : m；g : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PEquiv.mul_toMatrix_toPEquiv`：mul_toMatrix_toPEquiv [Fintype m] [Decidab
leEq n] [NonAssocSemiring α] (M : Matrix l m α) (f : m ≃ n) : (M * f.toPEquiv.to
Matrix) = M.submat…
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Multiplying with `swap R i j` on the right swaps the `i`-th column with the `j`-
th column.
-/
lemma mul_swap_apply_left (i j : n) (a : m) (g : Matrix m n R) :
    (g * swap R i j) a i = g a j := by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv]

/-- Multiplying with `swap R i j` on the right swaps the `j`-th column with the `i`-th column. -/
@[simp]
/-
**Matrix.mul_swap_apply_right** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_swap_apply_right (i j : n) (a : m) (g : Matrix m n R) : (g * swap R i 
j) a j = g a i
参数：i j : n；a : m；g : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.swap_comm`：swap_comm (i j : n) : swap R i j = swap R j i
· 使用引理 `Matrix.mul_swap_apply_left`：mul_swap_apply_left (i j : n) (a : m) (g : M
atrix m n R) : (g * swap R i j) a i = g a j

--- 原说明 ---
Multiplying with `swap R i j` on the right swaps the `j`-th column with the `i`-
th column.
-/
lemma mul_swap_apply_right (i j : n) (a : m) (g : Matrix m n R) :
    (g * swap R i j) a j = g a i := by
  rw [swap_comm, mul_swap_apply_left]
/-
**Matrix.mul_swap_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mul_swap_of_ne {i j b : n} {a : m} (hbi : b != i) (hbj : b != j) (g : Matr
ix m n R) : (g * swap R i j) a b = g a b
参数：hbi : b != i；hbj : b != j；g : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `PEquiv.mul_toMatrix_toPEquiv`：mul_toMatrix_toPEquiv [Fintype m] [Decidab
leEq n] [NonAssocSemiring α] (M : Matrix l m α) (f : m ≃ n) : (M * f.toPEquiv.to
Matrix) = M.submat…
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_swap_of_ne {i j b : n} {a : m} (hbi : b ≠ i) (hbj : b ≠ j) (g : Matrix m n R) :
    (g * swap R i j) a b = g a b := by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv, Equiv.swap_apply_of_ne_of_ne hbi hbj]

/-- Swap matrices are self inverse. -/
/-
**Matrix.swap_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：swap_mul_self (i j : n) : swap R i j * swap R i j = 1
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.swap_inv`：∀ {α : Type u_4} [inst : DecidableEq α] (x y : α), (Equi
v.swap x y)⁻¹ = Equiv.swap x y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.inv_def`：inv_def (f : Perm α) : f⁻¹ = f.symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swap_swap`：swap_swap (a b : α) : (swap a b).trans (swap a b) = Equ
iv.refl _
· 使用定理 `PEquiv.toMatrix_refl`：toMatrix_refl [DecidableEq n] [Zero α] [One α] : (
(PEquiv.refl n).toMatrix : Matrix n n α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Swap matrices are self inverse.
-/
lemma swap_mul_self (i j : n) : swap R i j * swap R i j = 1 := by
  simp only [swap]
  rw [← Equiv.swap_inv, Equiv.Perm.inv_def]
  simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

end

namespace GeneralLinearGroup
variable (R : Type*) {n : Type*} [CommRing R] [DecidableEq n] [Fintype n]

/-- `Matrix.swap` as an element of `GL n R`. -/
@[simps val]
/-
**Matrix.GeneralLinearGroup.swap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.GeneralLinear
Group`。
形式化陈述：swap (i j : n) : GL n R where val
参数：i j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.swap` as an element of `GL n R`.
-/
def swap (i j : n) : GL n R where
  val := Matrix.swap R i j
  inv := Matrix.swap R i j
  val_inv := swap_mul_self i j
  inv_val := swap_mul_self i j

variable {R} {S : Type*} [CommRing S] (f : R →+* S)

@[simp]
/-
**Matrix.GeneralLinearGroup.map_swap** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.GeneralLi
nearGroup`。
形式化陈述：map_swap (i j : n) : (swap R i j).map f = swap S i j
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_map_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用引理 `Matrix.map_swap`：map_swap {S : Type*} [NonAssocSemiring S] (f : R ->+* S
) (i j : n) : (swap R i j).map f = swap S i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_swap (i j : n) : (swap R i j).map f = swap S i j := by
  ext : 1
  simp [swap]

end GeneralLinearGroup

end Matrix

