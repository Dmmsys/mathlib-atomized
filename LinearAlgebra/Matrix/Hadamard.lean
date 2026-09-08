/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic

/-!
# Hadamard product of matrices

This file defines the Hadamard product `Matrix.hadamard`
and contains basic properties about them.

## Main definition

- `Matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `Matrix.hadamard`;

## References

* <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/

@[expose] public section


variable {α m n R : Type*}

namespace Matrix

/-- `Matrix.hadamard` (denoted as `⊙` within the Matrix namespace) defines the Hadamard product,
which is the pointwise product of two matrices of the same size. -/
/-
**Matrix.hadamard** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α
参数：A : Matrix m n α；B : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.hadamard` (denoted as `⊙` within the Matrix namespace) defines the Hadam
ard product,
which is the pointwise product of two matrices of the same size.
-/
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j

-- TODO: set as an equation lemma for `hadamard`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Matrix.hadamard_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) : hadam
ard A B i j = A i j * B i j
参数：A : Matrix m n α；B : Matrix m n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    hadamard A B i j = A i j * B i j :=
  rfl

@[inherit_doc] scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

-- commutativity
/-
**Matrix.hadamard_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_comm [CommMagma α] : A ⊙ B = B ⊙ A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem hadamard_comm [CommMagma α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _

-- associativity
/-
**Matrix.hadamard_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _

-- distributivity
/-
**Matrix.hadamard_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _
/-
**Matrix.add_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _

-- scalar multiplication
section Scalar

@[simp]
/-
**Matrix.smul_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙
 B = k • A ⊙ B
参数：k : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
theorem smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
/-
**Matrix.hadamard_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • 
B) = k • A ⊙ B
参数：k : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
theorem hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _

end Scalar

section Zero

variable [MulZeroClass α]

@[simp]
/-
**Matrix.hadamard_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_zero : A ⊙ (0 : Matrix m n α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => mul_zero _

@[simp]
/-
**Matrix.zero_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_hadamard : (0 : Matrix m n α) ⊙ A = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => zero_mul _

end Zero

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

/-
**Matrix.hadamard_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_diagonal (M) (w : n -> α) : M ⊙ diagonal w = diagonal (M.diag * w
)
参数：M；w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hadamard_diagonal (M) (w : n → α) :
    M ⊙ diagonal w = diagonal (M.diag * w) := by aesop (add simp diagonal)
/-
**Matrix.diagonal_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_hadamard (M) (w : n -> α) : diagonal w ⊙ M = diagonal (w * M.diag
)
参数：M；w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_hadamard (M) (w : n → α) :
    diagonal w ⊙ M = diagonal (w * M.diag) := by aesop (add simp diagonal)
/-
**Matrix.diagonal_hadamard_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_hadamard_diagonal (v : n -> α) (w : n -> α) : diagonal v ⊙ diagon
al w = diagonal (v * w)
参数：v : n -> α；w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_hadamard`：diagonal_hadamard (M) (w : n -> α) : diagonal 
w ⊙ M = diagonal (w * M.diag)
· 使用定理 `Matrix.diag_diagonal`：diag_diagonal [DecidableEq n] [Zero α] (a : n -> α
) : diag (diagonal a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) := by simp [diagonal_hadamard]
/-
**Matrix.diagonal_hadamard_eq_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_hadamard_eq_diagonal_iff {A : Matrix n n α} {d e} : diagonal d ⊙ 
A = diagonal e ↔ d * A.diag = e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_hadamard`：diagonal_hadamard (M) (w : n -> α) : diagonal 
w ⊙ M = diagonal (w * M.diag)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem diagonal_hadamard_eq_diagonal_iff {A : Matrix n n α} {d e} :
    diagonal d ⊙ A = diagonal e ↔ d * A.diag = e := by
  simp [diagonal_hadamard, diagonal_eq_diagonal_iff, funext_iff]
/-
**Matrix.hadamard_diagonal_eq_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_diagonal_eq_diagonal_iff {A : Matrix n n α} {d e} : A ⊙ diagonal 
d = diagonal e ↔ A.diag * d = e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.hadamard_diagonal`：hadamard_diagonal (M) (w : n -> α) : M ⊙ diago
nal w = diagonal (M.diag * w)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hadamard_diagonal_eq_diagonal_iff {A : Matrix n n α} {d e} :
    A ⊙ diagonal d = diagonal e ↔ A.diag * d = e := by
  simp [hadamard_diagonal, diagonal_eq_diagonal_iff, funext_iff]

end Diagonal

section One

variable [DecidableEq n] [MulZeroOneClass α]
variable (M : Matrix n n α)

/-
**Matrix.hadamard_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_one : M ⊙ 1 = diagonal M.diag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.hadamard_diagonal`：hadamard_diagonal (M) (w : n -> α) : M ⊙ diago
nal w = diagonal (M.diag * w)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem hadamard_one : M ⊙ 1 = diagonal M.diag := mul_one M.diag ▸ hadamard_diagonal M 1
/-
**Matrix.one_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_hadamard : 1 ⊙ M = diagonal M.diag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_hadamard`：diagonal_hadamard (M) (w : n -> α) : diagonal 
w ⊙ M = diagonal (w * M.diag)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_hadamard : 1 ⊙ M = diagonal M.diag := one_mul M.diag ▸ diagonal_hadamard M 1
/-
**Matrix.one_hadamard_eq_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_hadamard_eq_diagonal_iff {A : Matrix n n α} {d} : 1 ⊙ A = diagonal d ↔
 A.diag = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.diagonal_hadamard_eq_diagonal_iff`：diagonal_hadamard_eq_diagonal_
iff {A : Matrix n n α} {d e} : diagonal d ⊙ A = diagonal e ↔ d * A.diag = e
-/
theorem one_hadamard_eq_diagonal_iff {A : Matrix n n α} {d} : 1 ⊙ A = diagonal d ↔ A.diag = d := by
  simpa using diagonal_hadamard_eq_diagonal_iff (A := A) (d := 1)
/-
**Matrix.hadamard_one_eq_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_one_eq_diagonal_iff {A : Matrix n n α} {d} : A ⊙ 1 = diagonal d ↔
 A.diag = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.hadamard_diagonal_eq_diagonal_iff`：hadamard_diagonal_eq_diagonal_
iff {A : Matrix n n α} {d e} : A ⊙ diagonal d = diagonal e ↔ A.diag * d = e
-/
theorem hadamard_one_eq_diagonal_iff {A : Matrix n n α} {d} : A ⊙ 1 = diagonal d ↔ A.diag = d := by
  simpa using hadamard_diagonal_eq_diagonal_iff (A := A) (d := 1)
/-
**Matrix.one_hadamard_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_hadamard_eq_zero_iff {A : Matrix n n α} : 1 ⊙ A = 0 ↔ A.diag = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_zero'`：diagonal_zero' [Zero α] : (diagonal 0 : Matrix n 
n α) = 0
· 使用定理 `Matrix.one_hadamard_eq_diagonal_iff`：one_hadamard_eq_diagonal_iff {A : M
atrix n n α} {d} : 1 ⊙ A = diagonal d ↔ A.diag = d
-/
theorem one_hadamard_eq_zero_iff {A : Matrix n n α} : 1 ⊙ A = 0 ↔ A.diag = 0 := by
  simpa using one_hadamard_eq_diagonal_iff (A := A) (d := 0)
/-
**Matrix.hadamard_one_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_one_eq_zero_iff {A : Matrix n n α} : A ⊙ 1 = 0 ↔ A.diag = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_zero'`：diagonal_zero' [Zero α] : (diagonal 0 : Matrix n 
n α) = 0
· 使用定理 `Matrix.hadamard_one_eq_diagonal_iff`：hadamard_one_eq_diagonal_iff {A : M
atrix n n α} {d} : A ⊙ 1 = diagonal d ↔ A.diag = d
-/
theorem hadamard_one_eq_zero_iff {A : Matrix n n α} : A ⊙ 1 = 0 ↔ A.diag = 0 := by
  simpa using hadamard_one_eq_diagonal_iff (A := A) (d := 0)
/-
**Matrix.one_hadamard_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_hadamard_eq_one_iff {A : Matrix n n α} : 1 ⊙ A = 1 ↔ A.diag = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.one_hadamard_eq_diagonal_iff`：one_hadamard_eq_diagonal_iff {A : M
atrix n n α} {d} : 1 ⊙ A = diagonal d ↔ A.diag = d
-/
theorem one_hadamard_eq_one_iff {A : Matrix n n α} : 1 ⊙ A = 1 ↔ A.diag = 1 :=
  one_hadamard_eq_diagonal_iff
/-
**Matrix.hadamard_one_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_one_eq_one_iff {A : Matrix n n α} : A ⊙ 1 = 1 ↔ A.diag = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.hadamard_one_eq_diagonal_iff`：hadamard_one_eq_diagonal_iff {A : M
atrix n n α} {d} : A ⊙ 1 = diagonal d ↔ A.diag = d
-/
theorem hadamard_one_eq_one_iff {A : Matrix n n α} : A ⊙ 1 = 1 ↔ A.diag = 1 :=
  hadamard_one_eq_diagonal_iff

end One

/-
**Matrix.hadamard_of_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : MulOneClass α] (A :
 Matrix m n α), A.hadamard (Matrix.of 1) = A
参数：A : Matrix m n α；Matrix.of 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem hadamard_of_one [MulOneClass α] (A : Matrix m n α) :
    A ⊙ of 1 = A := by ext; simp
/-
**Matrix.of_one_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {m : Type u_2} {n : Type u_3} [inst : MulOneClass α] (A :
 Matrix m n α), (Matrix.of 1).hadamard A = A
参数：A : Matrix m n α；Matrix.of 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem of_one_hadamard [MulOneClass α] (A : Matrix m n α) :
    of 1 ⊙ A = A := by ext; simp
/-
**Matrix.hadamard_self_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_self_eq_self_iff [Mul α] {A : Matrix m n α} : A ⊙ A = A ↔ forall 
i j, IsIdempotentElem (A i j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem hadamard_self_eq_self_iff [Mul α] {A : Matrix m n α} :
    A ⊙ A = A ↔ ∀ i j, IsIdempotentElem (A i j) := ext_iff.symm
/-
**Matrix.submatrix_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_hadamard {l o : Type*} [Mul α] (A B : Matrix m n α) (e : l -> m)
 (f : o -> n) : (A ⊙ B).submatrix e f = A.submatrix e f ⊙ B.submatrix e f
参数：A B : Matrix m n α；e : l -> m；f : o -> n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_hadamard {l o : Type*} [Mul α]
    (A B : Matrix m n α) (e : l → m) (f : o → n) :
    (A ⊙ B).submatrix e f = A.submatrix e f ⊙ B.submatrix e f := rfl
/-
**Matrix.transpose_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_hadamard [Mul α] (A B : Matrix m n α) : (A ⊙ B)ᵀ = Aᵀ ⊙ Bᵀ
参数：A B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem transpose_hadamard [Mul α] (A B : Matrix m n α) : (A ⊙ B)ᵀ = Aᵀ ⊙ Bᵀ :=
  ext fun _ _ => rfl
/-
**Matrix.conjTranspose_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_hadamard [Mul α] [StarMul α] (A B : Matrix m n α) : (A ⊙ B)ᴴ
 = Bᴴ ⊙ Aᴴ
参数：A B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
-/
theorem conjTranspose_hadamard [Mul α] [StarMul α] (A B : Matrix m n α) : (A ⊙ B)ᴴ = Bᴴ ⊙ Aᴴ :=
  ext fun _ _ => StarMul.star_mul _ _

section single

variable [DecidableEq m] [DecidableEq n] [MulZeroClass α]

/-
**Matrix.single_hadamard_single_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_hadamard_single_eq (i : m) (j : n) (a b : α) : single i j a ⊙ singl
e i j b = single i j (a * b)
参数：i : m；j : n；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `apply_ite₂`：apply_ite₂ {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Dec
idable P] (a b : α) (c d : β) : f (ite P a b) (ite P c d) = ite P (f a c) (f b d
…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem single_hadamard_single_eq (i : m) (j : n) (a b : α) :
    single i j a ⊙ single i j b = single i j (a * b) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)
/-
**Matrix.single_hadamard_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_hadamard_single_of_ne {ia : m} {ja : n} {ib : m} {jb : n} (h : ¬(ia
 = ib ∧ ja = jb)) (a b : α) : single ia ja a ⊙ single ib jb b = 0
参数：h : ¬(ia = ib ∧ ja = jb)；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem single_hadamard_single_of_ne
    {ia : m} {ja : n} {ib : m} {jb : n} (h : ¬(ia = ib ∧ ja = jb)) (a b : α) :
    single ia ja a ⊙ single ib jb b = 0 := by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

end single

section trace

variable [Fintype m] [Fintype n]
variable (R) [NonUnitalSemiring α]

/-
**Matrix.sum_hadamard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.dotProduct_vecMul_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m -> α) (w
 : n -> α) : v ᵥ* (A ⊙ B) ⬝ᵥ w = trace (diagonal v * A * (B * diagonal w)ᵀ)
参数：v : m -> α；w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.sum_hadamard_eq`：sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j
) = trace (A * Bᵀ)
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Matrix.diagonal_mul`：diagonal_mul [Fintype m] [DecidableEq m] (d : m -> 
α) (M : Matrix m n α) (i j) : (diagonal d * M) i j = d i * M i j
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m → α) (w : n → α) :
    v ᵥ* (A ⊙ B) ⬝ᵥ w = trace (diagonal v * A * (B * diagonal w)ᵀ) := by
  rw [← sum_hadamard_eq, Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul, mul_assoc]

end trace

end BasicProperties

end Matrix

