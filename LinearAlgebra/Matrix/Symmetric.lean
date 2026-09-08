/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric matrices

This file contains the definition and basic results about symmetric matrices.

## Main definition

* `Matrix.isSymm`: a matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/

@[expose] public section


variable {α β n m R : Type*}

namespace Matrix

/-- A matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`. -/
@[wikidata Q339011]
/-
**Matrix.IsSymm** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsSymm (A : Matrix n n α) : Prop
参数：A : Matrix n n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`.
-/
def IsSymm (A : Matrix n n α) : Prop :=
  Aᵀ = A
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Matrix n n α) [Decidable (Aᵀ = A)] : Decidable (IsSymm A) :=
  inferInstanceAs <| Decidable (_ = _)
/-
**Matrix.IsSymm.eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, A.IsSymm → A.transpose
 = A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSymm.eq {A : Matrix n n α} (h : A.IsSymm) : Aᵀ = A :=
  h

/-- A version of `Matrix.ext_iff` that unfolds the `Matrix.transpose`. -/
/-
**Matrix.IsSymm.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, A.IsSymm ↔ ∀ (i j : n)
, A j i = A i j
参数：i j : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N

--- 原说明 ---
A version of `Matrix.ext_iff` that unfolds the `Matrix.transpose`.
-/
theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ ∀ i j, A j i = A i j :=
  Matrix.ext_iff.symm

/-- A version of `Matrix.ext` that unfolds the `Matrix.transpose`. -/
/-
**Matrix.IsSymm.ext** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, (∀ (i j : n), A j i = 
A i j) → A.IsSymm
参数：∀ (i j : n), A j i = A i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
A version of `Matrix.ext` that unfolds the `Matrix.transpose`.
-/
theorem IsSymm.ext {A : Matrix n n α} : (∀ i j, A j i = A i j) → A.IsSymm :=
  Matrix.ext
/-
**Matrix.IsSymm.apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, A.IsSymm → ∀ (i j : n)
, A j i = A i j
参数：i j : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.IsSymm.ext_iff`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α
}, A.IsSymm ↔ ∀ (i j : n), A j i = A i j
-/
theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j :=
  IsSymm.ext_iff.1 h i j
/-
**Matrix.isSymm_mul_transpose_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matri
x n n α) : (A * Aᵀ).IsSymm
参数：A : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
-/
theorem isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (A * Aᵀ).IsSymm :=
  transpose_mul _ _
/-
**Matrix.isSymm_transpose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matri
x n n α) : (Aᵀ * A).IsSymm
参数：A : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
-/
theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (Aᵀ * A).IsSymm :=
  transpose_mul _ _
/-
**Matrix.isSymm_add_transpose_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + A
ᵀ).IsSymm
参数：A : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm :=
  add_comm _ _
/-
**Matrix.isSymm_transpose_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + 
A).IsSymm
参数：A : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
  add_comm _ _

@[simp]
/-
**Matrix.isSymm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_zero`：transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0
-/
theorem isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm :=
  transpose_zero

@[simp]
/-
**Matrix.isSymm_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
-/
theorem isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm :=
  transpose_one
/-
**Matrix.IsSymm.pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} [inst : CommSemiring α] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n]   {A : Matrix n n α}, A.IsSymm → ∀ (k : ℕ), (A ^ k).
IsSymm
参数：k : ℕ；A ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Matrix.transpose_pow`：transpose_pow [CommSemiring α] [Fintype m] [Decida
bleEq m] (M : Matrix m m α) (k : Nat) : (M ^ k)ᵀ = Mᵀ ^ k
-/
theorem IsSymm.pow [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
    (k : ℕ) :
    (A ^ k).IsSymm := by
  rw [IsSymm, transpose_pow, h]

@[simp]
/-
**Matrix.IsSymm.map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {n : Type u_3} {A : Matrix n n α}, A.IsSym
m → ∀ (f : α → β), (A.map f).IsSymm
参数：f : α → β；A.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Matrix.IsSymm.eq`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, A.
IsSymm → A.transpose = A
-/
theorem IsSymm.map {A : Matrix n n α} (h : A.IsSymm) (f : α → β) : (A.map f).IsSymm := by
  rw [IsSymm, ← transpose_map, h.eq]

@[simp]
/-
**Matrix.isSymm_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_map_iff {A : Matrix n n α} {f : α -> β} (hf : f.Injective) : (A.map
 f).IsSymm ↔ A.IsSymm
参数：hf : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.map_injective`：map_injective {f : α -> β} (hf : Function.Injectiv
e f) : Function.Injective fun M : Matrix m n α => M.map f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSymm_map_iff {A : Matrix n n α} {f : α → β} (hf : f.Injective) :
    (A.map f).IsSymm ↔ A.IsSymm := by
  rw [IsSymm, IsSymm, ← transpose_map, map_injective hf |>.eq_iff]
/-
**Matrix.IsSymm.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, A.IsSymm → A.transpose
.IsSymm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsSymm.transpose {A : Matrix n n α} (h : A.IsSymm) : Aᵀ.IsSymm :=
  congr_arg _ h

@[simp]
/-
**Matrix.isSymm_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_transpose_iff {A : Matrix n n α} : Aᵀ.IsSymm ↔ A.IsSymm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.IsSymm.transpose`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n
 α}, A.IsSymm → A.transpose.IsSymm
-/
theorem isSymm_transpose_iff {A : Matrix n n α} : Aᵀ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.transpose)⟩
  rw [← A.transpose_transpose]
  exact h.transpose

@[simp]
/-
**Matrix.IsSymm.conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} [inst : Star α] {A : Matrix n n α}, A.IsSy
mm → A.conjTranspose.IsSymm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsSymm.map`：∀ {α : Type u_1} {β : Type u_2} {n : Type u_3} {A : M
atrix n n α}, A.IsSymm → ∀ (f : α → β), (A.map f).IsSymm
· 使用定理 `Matrix.IsSymm.transpose`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n
 α}, A.IsSymm → A.transpose.IsSymm
-/
theorem IsSymm.conjTranspose [Star α] {A : Matrix n n α} (h : A.IsSymm) : Aᴴ.IsSymm :=
  h.transpose.map _

@[simp]
/-
**Matrix.isSymm_conjTranspose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_conjTranspose_iff [InvolutiveStar α] {A : Matrix n n α} : Aᴴ.IsSymm
 ↔ A.IsSymm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.IsSymm.conjTranspose`：∀ {α : Type u_1} {n : Type u_3} [inst : Sta
r α] {A : Matrix n n α}, A.IsSymm → A.conjTranspose.IsSymm
-/
theorem isSymm_conjTranspose_iff [InvolutiveStar α] {A : Matrix n n α} : Aᴴ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.conjTranspose)⟩
  rw [← A.conjTranspose_conjTranspose]
  exact h.conjTranspose

@[simp]
/-
**Matrix.IsSymm.neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} [inst : Neg α] {A : Matrix n n α}, A.IsSym
m → (-A).IsSymm
参数：-A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_neg`：transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ =
 -Mᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsSymm.neg [Neg α] {A : Matrix n n α} (h : A.IsSymm) : (-A).IsSymm :=
  (transpose_neg _).trans (congr_arg _ h)

@[simp]
/-
**Matrix.isSymm_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_neg_iff [InvolutiveNeg α] {A : Matrix n n α} : (-A).IsSymm ↔ A.IsSy
mm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Matrix.IsSymm.neg`：∀ {α : Type u_1} {n : Type u_3} [inst : Neg α] {A : M
atrix n n α}, A.IsSymm → (-A).IsSymm
-/
theorem isSymm_neg_iff [InvolutiveNeg α] {A : Matrix n n α} : (-A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]
/-
**Matrix.IsSymm.add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A B : Matrix n n α} [inst : Add α], A.IsS
ymm → B.IsSymm → (A + B).IsSymm
参数：A + B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_add`：transpose_add [Add α] (M : Matrix m n α) (N : Matr
ix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm :=
  (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
/-
**Matrix.IsSymm.sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {A B : Matrix n n α} [inst : Sub α], A.IsS
ymm → B.IsSymm → (A - B).IsSymm
参数：A - B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_sub`：transpose_sub [Sub α] (M : Matrix m n α) (N : Matr
ix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm :=
  (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
/-
**Matrix.IsSymm.smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {R : Type u_5} [inst : SMul R α] {A : Matr
ix n n α},   A.IsSymm → ∀ (k : R), (k • A).IsSymm
参数：k : R；k • A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_smul`：transpose_smul {R : Type*} [SMul R α] (c : R) (M 
: Matrix m n α) : (c • M)ᵀ = c • Mᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm :=
  (transpose_smul _ _).trans (congr_arg _ h)

@[simp]
/-
**Matrix.isSymm_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_smul_iff [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Inv
ertible k] : (k • A).IsSymm ↔ A.IsSymm
参数：k : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `invOf_smul_smul`：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst
_1 : MulAction α β] (c : α) (x : β) [inst_2 : Invertible c],   ⅟c • c • x = x
· 使用定理 `Matrix.IsSymm.smul`：∀ {α : Type u_1} {n : Type u_3} {R : Type u_5} [inst
 : SMul R α] {A : Matrix n n α},   A.IsSymm → ∀ (k : R), (k • A).IsSymm
-/
theorem isSymm_smul_iff [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Invertible k] :
    (k • A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.smul k)⟩
  rw [← invOf_smul_smul k A]
  exact h.smul ⅟k

@[simp]
/-
**Matrix.IsSymm.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4} {A : Matrix n n α}, A.IsSym
m → ∀ (f : m → n), (A.submatrix f f).IsSymm
参数：f : m → n；A.submatrix f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSymm.submatrix {A : Matrix n n α} (h : A.IsSymm) (f : m → n) : (A.submatrix f f).IsSymm :=
  (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)
/-
**Matrix.IsSymm.reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4} {A : Matrix n n α},   A.IsS
ymm → ∀ (f : n ≃ m), ((Matrix.reindex f f) A).IsSymm
参数：f : n ≃ m；(Matrix.reindex f f) A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.reindex_apply`：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matri
x m n α) : reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm
· 使用定理 `Matrix.IsSymm.submatrix`：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4} 
{A : Matrix n n α}, A.IsSymm → ∀ (f : m → n), (A.submatrix f f).IsSymm
-/
theorem IsSymm.reindex {A : Matrix n n α} (h : A.IsSymm) (f : n ≃ m) : (A.reindex f f).IsSymm := by
  rw [reindex_apply]
  apply submatrix h
/-
**Matrix.isSymm_reindex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_reindex_iff {A : Matrix n n α} (f : n ≃ m) : (A.reindex f f).IsSymm
 ↔ A.IsSymm
参数：f : n ≃ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Matrix.IsSymm.reindex`：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4} {A
 : Matrix n n α},   A.IsSymm → ∀ (f : n ≃ m), ((Matrix.reindex f f) A).IsSymm
-/
theorem isSymm_reindex_iff {A : Matrix n n α} (f : n ≃ m) : (A.reindex f f).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp]
/-
**Matrix.isSymm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_diagonal [DecidableEq n] [Zero α] (v : n -> α) : (diagonal v).IsSym
m
参数：v : n -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v

--- 原说明 ---
The diagonal matrix `diagonal v` is symmetric.
-/
theorem isSymm_diagonal [DecidableEq n] [Zero α] (v : n → α) : (diagonal v).IsSymm :=
  diagonal_transpose _

/-- A block matrix `A.fromBlocks B C D` is symmetric,
if `A` and `D` are symmetric and `Bᵀ = C`. -/
/-
**Matrix.IsSymm.fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4} {A : Matrix m m α} {B : Mat
rix m n α} {C : Matrix n m α}   {D : Matrix n n α}, A.IsSymm → B.transpose = C →
 D.IsSymm → (Matrix.fromBlocks A B C D).IsSymm
参数：Matrix.fromBlocks A B C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …

--- 原说明 ---
A block matrix `A.fromBlocks B C D` is symmetric,
if `A` and `D` are symmetric and `Bᵀ = C`.
-/
theorem IsSymm.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsSymm) (hBC : Bᵀ = C) (hD : D.IsSymm) :
    (A.fromBlocks B C D).IsSymm := by
  have hCB : Cᵀ = B := by
    rw [← hBC]
    simp
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose, hA, hCB, hBC, hD]

/-- This is the `iff` version of `Matrix.isSymm.fromBlocks`. -/
/-
**Matrix.isSymm_fromBlocks_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n 
m α} {D : Matrix n n α} : (A.fromBlocks B C D).IsSymm ↔ A.IsSymm ∧ Bᵀ = C ∧ Cᵀ =
 B ∧ D.IsSymm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.fromBlocks`：∀ {α : Type u_1} {n : Type u_3} {m : Type u_4}
 {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}   {D : Matrix n n α}, 
A.IsSymm → B.t…

--- 原说明 ---
This is the `iff` version of `Matrix.isSymm.fromBlocks`.
-/
theorem isSymm_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsSymm ↔ A.IsSymm ∧ Bᵀ = C ∧ Cᵀ = B ∧ D.IsSymm :=
  ⟨fun h =>
    ⟨(congr_arg toBlocks₁₁ h :), (congr_arg toBlocks₂₁ h :), (congr_arg toBlocks₁₂ h :),
      (congr_arg toBlocks₂₂ h :)⟩,
    fun ⟨hA, hBC, _, hD⟩ => IsSymm.fromBlocks hA hBC hD⟩
/-
**Matrix.isSymm_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_comp_iff {A : Matrix m m (Matrix n n α)} : (A.comp m m n n α).IsSym
m ↔ Aᵀ = A.map (·ᵀ)
参数：Matrix n n α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Matrix.transpose_comp`：transpose_comp (M : Matrix I J (Matrix K L R)) : 
(comp I J K L R M)ᵀ = comp J I L K R (Mᵀ.map (·ᵀ))
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.transpose_involutive`：transpose_involutive : (transpose : Matrix 
n n α -> Matrix n n α).Involutive
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSymm_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ Aᵀ = A.map (·ᵀ) := by
  rw [IsSymm, transpose_comp, transpose_map, comp .. |>.injective.eq_iff, eq_comm,
    transpose_involutive _ _ |>.eq_iff]
/-
**Matrix.isSymm_comp_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isSymm_comp_iff_forall {A : Matrix m m (Matrix n n α)} : (A.comp m m n n α
).IsSymm ↔ forall i j i' j', A j i j' i' = A i j i' j'
参数：Matrix n n α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.comp_apply`：∀ (I : Type u_1) (J : Type u_2) (K : Type u_3) (L : T
ype u_4) (R : Type u_5) (m : Matrix I J (Matrix K L R))   (ik : I × K) (jl : J ×
 L), (M…
-/
theorem isSymm_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ ∀ i j i' j', A j i j' i' = A i j i' j' := by
  simp [IsSymm.ext_iff]
  grind

end Matrix

