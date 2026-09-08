/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Jonathan Reich
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.NormDet

/-!
# Cartan matrices

This file defines Cartan matrices for simple Lie algebras, both the exceptional types
(E₆, E₇, E₈, F₄, G₂) and the classical infinite families (A, B, C, D).

## Main definitions

### Exceptional types
* `CartanMatrix.E₆` : The Cartan matrix of type E₆
* `CartanMatrix.E₇` : The Cartan matrix of type E₇
* `CartanMatrix.E₈` : The Cartan matrix of type E₈
* `CartanMatrix.F₄` : The Cartan matrix of type F₄
* `CartanMatrix.G₂` : The Cartan matrix of type G₂

### Classical types
* `CartanMatrix.A` : The Cartan matrix of type Aₙ₋₁ (corresponding to sl(n))
* `CartanMatrix.B` : The Cartan matrix of type Bₙ (corresponding to so(2n+1))
* `CartanMatrix.C` : The Cartan matrix of type Cₙ (corresponding to sp(2n))
* `CartanMatrix.D` : The Cartan matrix of type Dₙ (corresponding to so(2n))

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates I -- IX
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 11

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

@[expose] public section

namespace CartanMatrix

open Matrix

/-! ### Exceptional Cartan matrices -/

/-- The Cartan matrix of type E₆. See [bourbaki1968] plate V, page 277. -/
/-
**CartanMatrix.E** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type E₆. See [bourbaki1968] plate V, page 277.
-/
def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2,  0, -1,  0,  0;
     -1,  0,  2, -1,  0,  0;
      0, -1, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type E₇. See [bourbaki1968] plate VI, page 281. -/
/-
**CartanMatrix.E** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type E₇. See [bourbaki1968] plate VI, page 281.
-/
def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type E₈. See [bourbaki1968] plate VII, page 285. -/
/-
**CartanMatrix.E** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type E₈. See [bourbaki1968] plate VII, page 285.
-/
def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type F₄. See [bourbaki1968] plate VIII, page 288. -/
/-
**CartanMatrix.F** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type F₄. See [bourbaki1968] plate VIII, page 288.
-/
def F₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2, -1,  0,  0;
     -1,  2, -2,  0;
      0, -1,  2, -1;
      0,  0, -1,  2]

/-- The Cartan matrix of type G₂. See [bourbaki1968] plate IX, page 290.
We use the transpose of Bourbaki's matrix for consistency with F₄. -/
/-
**CartanMatrix.G** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type G₂. See [bourbaki1968] plate IX, page 290.
We use the transpose of Bourbaki's matrix for consistency with F₄.
-/
def G₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ 2, -3;
     -1,  2]

/-! ### Classical Cartan matrices -/

/-- The Cartan matrix of type Aₙ₋₁ (rank n-1, corresponding to sl(n)). -/
/-
**CartanMatrix.A** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
形式化陈述：A (n : Nat) : Matrix (Fin n) (Fin n) Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type Aₙ₋₁ (rank n-1, corresponding to sl(n)).
-/
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

/-- The Cartan matrix of type Bₙ (rank n, corresponding to so(2n+1)). -/
/-
**CartanMatrix.B** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
形式化陈述：B (n : Nat) : Matrix (Fin n) (Fin n) Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type Bₙ (rank n, corresponding to so(2n+1)).
-/
def B (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1
    else if j.val + 1 = i.val then -1
    else 0

/-- The Cartan matrix of type Cₙ (rank n, corresponding to sp(2n)). -/
/-
**CartanMatrix.C** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
形式化陈述：C (n : Nat) : Matrix (Fin n) (Fin n) Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type Cₙ (rank n, corresponding to sp(2n)).
-/
def C (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1
    else 0

/-- The Cartan matrix of type Dₙ (rank n, corresponding to so(2n)). -/
/-
**CartanMatrix.D** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatrix`。
形式化陈述：D (n : Nat) : Matrix (Fin n) (Fin n) Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrix of type Dₙ (rank n, corresponding to so(2n)).
-/
def D (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if n ≤ 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
    else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
    else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
    else 0

/-! ### Properties -/

section Properties

variable (n : ℕ)

/-
**CartanMatrix.A_diag** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ), (CartanMatrix.A n).diag = 2
参数：n : ℕ；CartanMatrix.A n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem A_diag : (A n).diag = 2 := by ext; simp [A]
/-
**CartanMatrix.B_diag** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ) (i : Fin n), CartanMatrix.B n i i = 2
参数：n : ℕ；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem B_diag (i : Fin n) : B n i i = 2 := by simp [B, Matrix.of_apply]
/-
**CartanMatrix.C_diag** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ) (i : Fin n), CartanMatrix.C n i i = 2
参数：n : ℕ；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem C_diag (i : Fin n) : C n i i = 2 := by simp [C, Matrix.of_apply]
/-
**CartanMatrix.D_diag** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ) (i : Fin n), CartanMatrix.D n i i = 2
参数：n : ℕ；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem D_diag (i : Fin n) : D n i i = 2 := by simp [D, Matrix.of_apply]
/-
**CartanMatrix.A_apply_le_zero_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：A_apply_le_zero_of_ne (i j : Fin n) (h : i != j) : A n i j <= 0
参数：i j : Fin n；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem A_apply_le_zero_of_ne (i j : Fin n) (h : i ≠ j) : A n i j ≤ 0 := by
  simp only [A, Matrix.of_apply]; split_ifs <;> omega
/-
**CartanMatrix.B_off_diag_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：B_off_diag_nonpos (i j : Fin n) (h : i != j) : B n i j <= 0
参数：i j : Fin n；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem B_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : B n i j ≤ 0 := by
  simp only [B, Matrix.of_apply]; split_ifs <;> omega
/-
**CartanMatrix.C_off_diag_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：C_off_diag_nonpos (i j : Fin n) (h : i != j) : C n i j <= 0
参数：i j : Fin n；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem C_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : C n i j ≤ 0 := by
  simp only [C, Matrix.of_apply]; split_ifs <;> omega
/-
**CartanMatrix.D_off_diag_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_off_diag_nonpos (i j : Fin n) (h : i != j) : D n i j <= 0
参数：i j : Fin n；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem D_off_diag_nonpos (i j : Fin n) (h : i ≠ j) : D n i j ≤ 0 := by
  simp only [D, Matrix.of_apply]; split_ifs <;> omega

/-! ### Transpose properties -/

/-
**CartanMatrix.A_transpose** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ), (CartanMatrix.A n).transpose = CartanMatrix.A n
参数：n : ℕ；CartanMatrix.A n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
### Transpose properties
-/
@[simp] theorem A_transpose : (A n).transpose = A n := by
  ext; simp only [A, transpose_apply, of_apply]; grind
/-
**CartanMatrix.A_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：A_isSymm : (A n).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CartanMatrix.A_transpose`：∀ (n : ℕ), (CartanMatrix.A n).transpose = Cart
anMatrix.A n
-/
theorem A_isSymm : (A n).IsSymm := A_transpose n
/-
**CartanMatrix.B_transpose** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ), (CartanMatrix.B n).transpose = CartanMatrix.C n
参数：n : ℕ；CartanMatrix.B n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
@[simp] theorem B_transpose : (B n).transpose = C n := by
  ext; simp only [B, C, transpose_apply, of_apply]; grind
/-
**CartanMatrix.C_transpose** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ), (CartanMatrix.C n).transpose = CartanMatrix.B n
参数：n : ℕ；CartanMatrix.C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `CartanMatrix.B_transpose`：∀ (n : ℕ), (CartanMatrix.B n).transpose = Cart
anMatrix.C n
-/
@[simp] theorem C_transpose : (C n).transpose = B n := by
  rw [← (B n).transpose_transpose, B_transpose]
/-
**CartanMatrix.D_transpose** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：∀ (n : ℕ), (CartanMatrix.D n).transpose = CartanMatrix.D n
参数：n : ℕ；CartanMatrix.D n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
@[simp] theorem D_transpose : (D n).transpose = D n := by
  ext; simp only [D, transpose_apply, of_apply]; grind
/-
**CartanMatrix.D_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_isSymm : (D n).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CartanMatrix.D_transpose`：∀ (n : ℕ), (CartanMatrix.D n).transpose = Cart
anMatrix.D n
-/
theorem D_isSymm : (D n).IsSymm := D_transpose n

/-! ### Small cases -/

/-
**CartanMatrix.A_one** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：A_one : A 1 = !![2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
### Small cases
-/
theorem A_one : A 1 = !![2] := by decide
/-
**CartanMatrix.A_two** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：A_two : A 2 = !![ 2, -1; -1, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem A_two : A 2 = !![ 2, -1;
                         -1,  2] := by decide
/-
**CartanMatrix.A_three** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：A_three : A 3 = !![ 2, -1, 0; -1, 2, -1; 0, -1, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem A_three : A 3 = !![ 2, -1,  0;
                           -1,  2, -1;
                            0, -1,  2] := by decide
/-
**CartanMatrix.B_one** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：B_one : B 1 = A 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem B_one : B 1 = A 1 := by decide
/-
**CartanMatrix.C_one** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：C_one : C 1 = A 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem C_one : C 1 = A 1 := by decide
/-
**CartanMatrix.D_one** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_one : D 1 = A 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem D_one : D 1 = A 1 := by decide
/-
**CartanMatrix.D_two** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_two : D 2 = !![2, 0; 0, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem D_two : D 2 = !![2, 0;
                         0, 2] := by decide
/-
**CartanMatrix.B_two** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：B_two : B 2 = !![ 2, -2; -1, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem B_two : B 2 = !![ 2, -2;
                         -1,  2] := by decide
/-
**CartanMatrix.C_two** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：C_two : C 2 = !![ 2, -1; -2, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem C_two : C 2 = !![ 2, -1;
                         -2,  2] := by decide
/-
**CartanMatrix.D_three** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_three : D 3 = !![ 2, -1, -1; -1, 2, 0; -1, 0, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem D_three : D 3 = !![ 2, -1, -1;
                           -1,  2,  0;
                           -1,  0,  2] := by decide
/-
**CartanMatrix.D_three'** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_three' : (D 3).reindex c[0, 1] c[0, 1] = A 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cycle.nodup_coe_iff`：nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ 
l.Nodup
-/
theorem D_three' : (D 3).reindex c[0, 1] c[0, 1] = A 3 := by decide
/-
**CartanMatrix.D_four** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：D_four : D 4 = !![ 2, -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem D_four : D 4 = !![ 2, -1,  0,  0;
                          -1,  2, -1, -1;
                           0, -1,  2,  0;
                           0, -1,  0,  2] := by decide



/-! ### Exceptional matrix diagonal entries -/

/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix diagonal entries
-/
@[simp] theorem E₆_diag (i : Fin 6) : E₆ i i = 2 := by fin_cases i <;> decide
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix diagonal entries
-/
@[simp] theorem E₇_diag (i : Fin 7) : E₇ i i = 2 := by fin_cases i <;> decide
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix diagonal entries
-/
@[simp] theorem E₈_diag (i : Fin 8) : E₈ i i = 2 := by fin_cases i <;> decide
/-
**CartanMatrix.F** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix diagonal entries
-/
@[simp] theorem F₄_diag (i : Fin 4) : F₄ i i = 2 := by fin_cases i <;> decide
/-
**CartanMatrix.G** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix diagonal entries
-/
@[simp] theorem G₂_diag (i : Fin 2) : G₂ i i = 2 := by fin_cases i <;> decide


/-! ### Exceptional matrix off-diagonal entries -/

/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix off-diagonal entries
-/
theorem E₆_off_diag_nonpos (i j : Fin 6) (h : i ≠ j) : E₆ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₆]
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem E₇_off_diag_nonpos (i j : Fin 7) (h : i ≠ j) : E₇ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₇]
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem E₈_off_diag_nonpos (i j : Fin 8) (h : i ≠ j) : E₈ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [E₈]
/-
**CartanMatrix.F** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem F₄_off_diag_nonpos (i j : Fin 4) (h : i ≠ j) : F₄ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [F₄]
/-
**CartanMatrix.G** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem G₂_off_diag_nonpos (i j : Fin 2) (h : i ≠ j) : G₂ i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [G₂]

/-! ### Exceptional matrix transpose properties -/

/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix transpose properties
-/
@[simp] theorem E₆_transpose : E₆.transpose = E₆ := by decide
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix transpose properties
-/
@[simp] theorem E₇_transpose : E₇.transpose = E₇ := by decide
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix transpose properties
-/
@[simp] theorem E₈_transpose : E₈.transpose = E₈ := by decide
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix transpose properties
-/
theorem E₆_isSymm : E₆.IsSymm := E₆_transpose
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem E₇_isSymm : E₇.IsSymm := E₇_transpose
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem E₈_isSymm : E₈.IsSymm := E₈_transpose

/-! ### Exceptional matrix determinants -/

/-
**CartanMatrix.G** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Exceptional matrix determinants
-/
theorem G₂_det : G₂.det = 1 := by decide
/-
**CartanMatrix.F** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem F₄_det : F₄.det = 1 := by decide

/-! The determinants of E₆, E₇, E₈ are 3, 2, 1 respectively. -/

/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinants of E₆, E₇, E₈ are 3, 2, 1 respectively.
-/
theorem E₆_det : E₆.det = 3 := by
  simp only [E₆, norm_det]
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem E₇_det : E₇.det = 2 := by
  simp only [E₇, norm_det]
/-
**CartanMatrix.E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem E₈_det : E₈.det = 1 := by
  simp only [E₈, norm_det]

/-- A Cartan matrix is simply laced if its off-diagonal entries are all `0` or `-1`. -/
/-
**CartanMatrix._root_.Matrix.IsSimplyLaced** 是 Mathlib 中的一个定义，位于命名空间 `CartanMatr
ix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Cartan matrix is simply laced if its off-diagonal entries are all `0` or `-1`.
-/
def _root_.Matrix.IsSimplyLaced {ι : Type*} (A : Matrix ι ι ℤ) : Prop :=
  Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1

set_option backward.isDefEq.respectTransparency.types false in
/-
**CartanMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Fintype ι] [DecidableEq ι] : DecidablePred (Matrix.IsSimplyLaced (ι := ι)) :=
  inferInstanceAs <|
    DecidablePred fun A : Matrix ι ι ℤ ↦ ∀ ⦃i j : ι⦄, i ≠ j → (fun i j ↦ A i j = 0 ∨ A i j = -1) i j
/-
**CartanMatrix._root_.Matrix.isSimplyLaced_iff_of_linearOrder** 是 Mathlib 中的一个引理
，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Matrix.isSimplyLaced_iff_of_linearOrder
    {ι : Type*} [LinearOrder ι] (A : Matrix ι ι ℤ) (hA : A.IsSymm) :
    A.IsSimplyLaced ↔ ∀ ⦃i j : ι⦄, j < i → (A i j = 0 ∨ A i j = -1) := by
  constructor
  · intro h i j hij
    exact h hij.ne'
  · intro h i j hij
    obtain hij | hij := hij.lt_or_gt
    · simpa only [hA.apply i j] using h hij
    · exact h hij
/-
**CartanMatrix._root_.Matrix.isSimplyLaced_transpose** 是 Mathlib 中的一个定理，位于命名空间 `
CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Matrix.isSimplyLaced_transpose {ι : Type*} (A : Matrix ι ι ℤ) :
    A.transpose.IsSimplyLaced ↔ A.IsSimplyLaced := by
  rw [IsSimplyLaced, IsSimplyLaced, Pairwise, Pairwise, forall_comm]
  aesop
/-
**CartanMatrix.isSimplyLaced_A** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：isSimplyLaced_A (n : Nat) : IsSimplyLaced (A n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSimplyLaced_A (n : ℕ) : IsSimplyLaced (A n) := by
  intro i j h
  simp only [A, of_apply]
  grind
/-
**CartanMatrix.isSimplyLaced_D** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
形式化陈述：isSimplyLaced_D (n : Nat) : IsSimplyLaced (D n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSimplyLaced_D (n : ℕ) : IsSimplyLaced (D n) := by
  intro i j h
  simp only [D, of_apply]
  grind

set_option backward.isDefEq.respectTransparency.types false in
/-
**CartanMatrix.isSimplyLaced_E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSimplyLaced_E₆ : IsSimplyLaced E₆ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₆ E₆_isSymm]; decide

set_option backward.isDefEq.respectTransparency.types false in
/-
**CartanMatrix.isSimplyLaced_E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSimplyLaced_E₇ : IsSimplyLaced E₇ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₇ E₇_isSymm]; decide

set_option backward.isDefEq.respectTransparency.types false in
/-
**CartanMatrix.isSimplyLaced_E** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSimplyLaced_E₈ : IsSimplyLaced E₈ := by
  rw [Matrix.isSimplyLaced_iff_of_linearOrder E₈ E₈_isSymm]; decide

/-! The Cartan matrices F₄ and G₂ are not simply laced because they contain
off-diagonal entries that are neither 0 nor -1. -/

/-
**CartanMatrix.not_isSimplyLaced_F** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartan matrices F₄ and G₂ are not simply laced because they contain
off-diagonal entries that are neither 0 nor -1.
-/
theorem not_isSimplyLaced_F₄ : ¬ IsSimplyLaced F₄ := by decide
/-
**CartanMatrix.not_isSimplyLaced_G** 是 Mathlib 中的一个定理，位于命名空间 `CartanMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_isSimplyLaced_G₂ : ¬ IsSimplyLaced G₂ := by decide

end Properties

end CartanMatrix

end

